use super::*;
use std::env::temp_dir;
use std::ffi::CString;
use std::fs::{metadata, remove_file};
use std::io::Error;
use std::process::id;

use libc::{O_CREAT, O_EXCL, O_RDWR, c_int, close, mode_t};

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
    let path = temp_dir().join(format!("fz-variadic-open-{}-{}", id(), unique));
    let c_path = CString::new(path.as_os_str().as_encoded_bytes()).expect("path cstring");

    let requested: mode_t = 0o764;
    let umask: mode_t = 0o027;
    let old_umask = unsafe { libc::umask(umask) };
    let fd = unsafe {
        fz_call_var_i64_cstring_i64_i64_to_i64(
            open_addr,
            c_path.as_ptr(),
            (O_CREAT | O_EXCL | O_RDWR) as i64,
            requested as i64,
        )
    };
    unsafe {
        libc::umask(old_umask);
    }

    assert!(fd >= 0, "open failed: {}", Error::last_os_error());
    let close_rc = unsafe { close(fd as c_int) };
    assert_eq!(close_rc, 0, "close failed");

    let mode = metadata(&path).expect("created file metadata").permissions().mode() & 0o777;
    let _ = remove_file(&path);
    assert_eq!(mode, (requested as u32) & !(umask as u32) & 0o777);
}
