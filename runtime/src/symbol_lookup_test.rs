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

    let missing = CString::new("__fz_missing_symbol_for_lookup_test").expect("cstring");
    let miss1 = unsafe { fz_extern_symbol_addr(missing.as_ptr()) };
    let miss2 = unsafe { fz_extern_symbol_addr(missing.as_ptr()) };
    assert_eq!(miss1, 0);
    assert_eq!(miss2, 0);
}
