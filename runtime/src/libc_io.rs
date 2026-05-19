//! fz-vw1 — minimal libc shims used by the extern-binary integration
//! fixture. These wrap libc's `open`/`write`/`close` and convert between
//! libc's raw return values and fz's tagged `FzValue` representation, so
//! that calls from fz code see boxed integers like every other extern
//! today returns.
//!
//! These are not a general-purpose libc binding — just enough surface to
//! demonstrate the `cstring` and `binary` extern marshal classes
//! end-to-end across the interpreter, JIT, and AOT paths.

use crate::fz_value::FzValue;

/// Open `path` write-only. Returns the file descriptor as a tagged
/// `FzValue::Int` (or a negative tagged int on error).
///
/// # Safety
/// `path` must be a valid NUL-terminated UTF-8 byte sequence — the
/// cstring marshal class from [[fz-9ss]] guarantees this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_test_open_writeonly(path: *const u8) -> u64 {
    let fd = unsafe { libc::open(path as *const libc::c_char, libc::O_WRONLY) };
    FzValue::from_int(fd as i64).0
}

/// Write `len` bytes from `buf` to `fd`, then close `fd`. Returns a
/// tagged `FzValue::Int(1)` if the write produced exactly `len` bytes
/// and the close succeeded, else `FzValue::Int(0)`.
///
/// # Safety
/// `buf` must point to at least `len` readable bytes — the binary
/// marshal class from [[fz-9ss]] guarantees this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_test_write_close(fd: i64, buf: *const u8, len: i64) -> u64 {
    let n = unsafe { libc::write(fd as libc::c_int, buf as *const libc::c_void, len as usize) };
    let close_rc = unsafe { libc::close(fd as libc::c_int) };
    let ok = (n == len as isize && close_rc == 0) as i64;
    FzValue::from_int(ok).0
}
