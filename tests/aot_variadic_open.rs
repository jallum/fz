//! AOT variadic-extern call with C ABI mode bits.
//!
//! Builds and runs a program that calls the variadic `libc::open(path, flags,
//! mode)` and checks that the created file's permission bits are exactly
//! `requested & ~umask`. This pins the variadic-extern calling convention
//! (the `mode` argument must be passed through the C varargs ABI) and the
//! umask interaction end-to-end through the AOT path. It inspects filesystem
//! permissions after the binary exits, which the fixture matrix cannot express,
//! so it stays a Rust integration test.

use std::env::temp_dir;
use std::ffi::OsStr;
use std::fs::{metadata, remove_file, write};
use std::path::PathBuf;
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn run_with_args(args: &[&OsStr]) -> Output {
    Command::new(FZ_BIN).args(args).output().expect("invoke fz binary")
}

#[cfg(unix)]
#[test]
#[serial_test::serial]
fn aot_variadic_open_creates_file_with_mode_bits() {
    use std::ffi::CString;
    use std::os::unix::fs::PermissionsExt;

    struct UmaskGuard(libc::mode_t);
    impl Drop for UmaskGuard {
        fn drop(&mut self) {
            unsafe {
                libc::umask(self.0);
            }
        }
    }

    let source_path = unique_temp_path("fz_variadic_open_aot", ".fz");
    let out_bin = unique_temp_path("fz_variadic_open_aot", ".bin");
    let created_path = unique_temp_path("fz_variadic_open_created", ".tmp");
    let path_text = created_path.to_string_lossy();
    assert!(CString::new(path_text.as_bytes()).is_ok());

    let requested: libc::mode_t = 0o764;
    let umask: libc::mode_t = 0o027;
    let flags = libc::O_CREAT | libc::O_EXCL | libc::O_RDWR;
    let src = format!(
        r#"
extern "C" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
extern "C" fn libc::close(fd :: integer) :: integer
fn main() do
  fd = libc::open("{}", {}, {} :: integer)
  libc::close(fd)
  nil
end
"#,
        path_text, flags, requested
    );
    write(&source_path, src).expect("write variadic open fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let _guard = UmaskGuard(unsafe { libc::umask(umask) });
    let run = Command::new(&out_bin).output().expect("run aot binary");
    assert!(
        run.status.success(),
        "aot binary failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );

    let mode = metadata(&created_path)
        .expect("created file metadata")
        .permissions()
        .mode()
        & 0o777;
    let _ = remove_file(&created_path);
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert_eq!(mode, (requested as u32) & !(umask as u32) & 0o777);
}
