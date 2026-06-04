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
use std::mem::transmute;
use std::process::abort;
use std::sync::{Mutex, OnceLock};

use libc::{RTLD_DEFAULT, c_int, c_longlong, c_uint, dlsym};

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
    let ptr = unsafe { dlsym(RTLD_DEFAULT, name) };
    ptr as usize
}

#[cfg(not(unix))]
fn resolve_symbol_addr(_name: *const c_char) -> usize {
    0
}

fn abort_null_fn_ptr(dispatcher: &str) -> ! {
    eprintln!("fz panic: {} received null C function pointer", dispatcher);
    abort();
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
    type FnPtr = unsafe extern "C" fn(*const c_char, c_int, ...) -> c_int;
    let f: FnPtr = unsafe { transmute(fn_ptr) };
    unsafe { f(path, fixed0 as c_int, var0 as c_uint) as i64 }
}

/// Call a C function shaped like `int f(const char*, ...)` with one integer
/// variadic argument. This covers simple `printf("%lld", n)`-style calls.
///
/// # Safety
/// `fn_ptr` must point to a C function with this ABI shape, and `fmt` must
/// satisfy that function's pointer contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_call_var_i64_cstring_i64_to_i64(fn_ptr: usize, fmt: *const c_char, var0: i64) -> i64 {
    if fn_ptr == 0 {
        abort_null_fn_ptr("fz_call_var_i64_cstring_i64_to_i64");
    }
    type FnPtr = unsafe extern "C" fn(*const c_char, ...) -> c_int;
    let f: FnPtr = unsafe { transmute(fn_ptr) };
    unsafe { f(fmt, var0 as c_longlong) as i64 }
}

#[cfg(test)]
#[path = "extern_variadic_test.rs"]
mod extern_variadic_test;
