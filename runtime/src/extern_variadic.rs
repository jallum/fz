//! Runtime support for C variadic externs.
//!
//! Dispatcher names are mechanical:
//!
//! `fz_call_var_<ret>_<fixed...>_<var...>_to_<ret>`
//!
//! Every argument token names the fz marshal class at the call boundary, not
//! necessarily the exact C parameter type after ABI-specific casts. Dispatchers
//! keep the unsafe C-variadic call surface in one place so codegen can call a
//! normal fixed-arity runtime helper.

use std::collections::HashMap;
use std::ffi::{CStr, c_char};
use std::sync::{Mutex, OnceLock};

type SymbolCache = HashMap<Vec<u8>, usize>;

fn symbol_cache() -> &'static Mutex<SymbolCache> {
    static CACHE: OnceLock<Mutex<SymbolCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Resolve a C symbol through `dlsym(RTLD_DEFAULT, name)`.
///
/// Returns `0` for a null name or an unresolved symbol. Both successes and
/// misses are cached by raw symbol bytes.
///
/// # Safety
/// `name` must be either null or a valid NUL-terminated C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_extern_symbol_addr(name: *const c_char) -> usize {
    if name.is_null() {
        return 0;
    }
    let key = unsafe { CStr::from_ptr(name) }.to_bytes().to_vec();
    let mut cache = symbol_cache().lock().expect("extern symbol cache poisoned");
    if let Some(&addr) = cache.get(&key) {
        return addr;
    }
    let addr = resolve_symbol_addr(name);
    cache.insert(key, addr);
    addr
}

#[cfg(unix)]
fn resolve_symbol_addr(name: *const c_char) -> usize {
    let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, name) };
    ptr as usize
}

#[cfg(not(unix))]
fn resolve_symbol_addr(_name: *const c_char) -> usize {
    0
}

fn abort_null_fn_ptr(dispatcher: &str) -> ! {
    eprintln!("fz panic: {} received null C function pointer", dispatcher);
    std::process::abort();
}

/// Call a C function shaped like `int f(const char*, int, ...)` with one
/// integer variadic argument. This covers libc `open(path, flags, mode)`.
///
/// # Safety
/// `fn_ptr` must point to a C function with this ABI shape, and `path` must
/// satisfy that function's pointer contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_call_var_i64_cstring_i64_i64_to_i64(
    fn_ptr: usize,
    path: *const c_char,
    fixed0: i64,
    var0: i64,
) -> i64 {
    if fn_ptr == 0 {
        abort_null_fn_ptr("fz_call_var_i64_cstring_i64_i64_to_i64");
    }
    type FnPtr = unsafe extern "C" fn(*const c_char, libc::c_int, ...) -> libc::c_int;
    let f: FnPtr = unsafe { std::mem::transmute(fn_ptr) };
    unsafe { f(path, fixed0 as libc::c_int, var0 as libc::c_uint) as i64 }
}

/// Call a C function shaped like `int f(const char*, ...)` with one integer
/// variadic argument. This covers simple `printf("%lld", n)`-style calls.
///
/// # Safety
/// `fn_ptr` must point to a C function with this ABI shape, and `fmt` must
/// satisfy that function's pointer contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_call_var_i64_cstring_i64_to_i64(
    fn_ptr: usize,
    fmt: *const c_char,
    var0: i64,
) -> i64 {
    if fn_ptr == 0 {
        abort_null_fn_ptr("fz_call_var_i64_cstring_i64_to_i64");
    }
    type FnPtr = unsafe extern "C" fn(*const c_char, ...) -> libc::c_int;
    let f: FnPtr = unsafe { std::mem::transmute(fn_ptr) };
    unsafe { f(fmt, var0 as libc::c_longlong) as i64 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[cfg(unix)]
    #[test]
    fn symbol_lookup_caches_successes_and_misses() {
        let open = CString::new("open").expect("cstring");
        let first = unsafe { fz_extern_symbol_addr(open.as_ptr()) };
        let second = unsafe { fz_extern_symbol_addr(open.as_ptr()) };
        assert_ne!(first, 0, "libc open should resolve");
        assert_eq!(first, second, "cached lookup should be stable");

        let missing = CString::new("__fz_missing_symbol_for_variadic_test").expect("cstring");
        let miss1 = unsafe { fz_extern_symbol_addr(missing.as_ptr()) };
        let miss2 = unsafe { fz_extern_symbol_addr(missing.as_ptr()) };
        assert_eq!(miss1, 0);
        assert_eq!(miss2, 0);
    }

    #[cfg(unix)]
    #[test]
    #[serial_test::serial]
    fn open_dispatcher_creates_file_with_requested_mode_after_umask() {
        use std::os::unix::fs::PermissionsExt;
        use std::time::{SystemTime, UNIX_EPOCH};

        let open_name = CString::new("open").expect("cstring");
        let open_addr = unsafe { fz_extern_symbol_addr(open_name.as_ptr()) };
        assert_ne!(open_addr, 0, "libc open should resolve");

        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "fz-variadic-open-{}-{}",
            std::process::id(),
            unique
        ));
        let c_path = CString::new(path.as_os_str().as_encoded_bytes()).expect("path cstring");

        let requested: libc::mode_t = 0o764;
        let umask: libc::mode_t = 0o027;
        let old_umask = unsafe { libc::umask(umask) };
        let fd = unsafe {
            fz_call_var_i64_cstring_i64_i64_to_i64(
                open_addr,
                c_path.as_ptr(),
                (libc::O_CREAT | libc::O_EXCL | libc::O_RDWR) as i64,
                requested as i64,
            )
        };
        unsafe {
            libc::umask(old_umask);
        }

        assert!(fd >= 0, "open failed: {}", std::io::Error::last_os_error());
        let close_rc = unsafe { libc::close(fd as libc::c_int) };
        assert_eq!(close_rc, 0, "close failed");

        let mode = std::fs::metadata(&path)
            .expect("created file metadata")
            .permissions()
            .mode()
            & 0o777;
        let _ = std::fs::remove_file(&path);
        assert_eq!(mode, (requested as u32) & !(umask as u32) & 0o777);
    }
}
