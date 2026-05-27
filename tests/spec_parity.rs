//! fz-ul4.31.6 — three-path parity for `@spec` violation rejection.
//!
//! Builds a deliberately-wrong `@spec` (declared `float -> float` on a
//! body called only with ints) and verifies the `fz` binary rejects it
//! with a `spec/violation` diagnostic on each of the three execution
//! paths: `fz interp`, `fz run` (JIT), `fz build` (AOT). The same
//! validation pass runs in every driver, so the verdict is invariant
//! by construction; this test pins the wiring against regression.

use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

const VIOLATION_SRC: &str = "\
defmodule M do
  @spec add1(float) :: float
  fn add1(n), do: n + 1
end

fn main(), do: print(M.add1(41))
";

fn write_temp_fz(name: &str) -> std::path::PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("fz_spec_parity_{}.fz", name));
    std::fs::write(&path, VIOLATION_SRC).expect("write temp fixture");
    path
}

fn unique_temp_path(prefix: &str, suffix: &str) -> std::path::PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "{}_{}_{}{}",
        prefix,
        std::process::id(),
        nonce,
        suffix
    ))
}

fn run_with_args(args: &[&std::ffi::OsStr]) -> std::process::Output {
    Command::new(FZ_BIN)
        .args(args)
        .output()
        .expect("invoke fz binary")
}

#[test]
fn interp_rejects_spec_violation() {
    let p = write_temp_fz("interp");
    let out = run_with_args(&[std::ffi::OsStr::new("interp"), p.as_os_str()]);
    assert!(
        !out.status.success(),
        "interp must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from interp; stderr={}",
        stderr
    );
}

#[test]
fn jit_rejects_spec_violation() {
    let p = write_temp_fz("jit");
    let out = run_with_args(&[std::ffi::OsStr::new("run"), p.as_os_str()]);
    assert!(
        !out.status.success(),
        "jit must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from jit; stderr={}",
        stderr
    );
}

#[test]
fn aot_rejects_spec_violation() {
    let p = write_temp_fz("aot");
    let mut out_bin = std::env::temp_dir();
    out_bin.push("fz_spec_parity_aot.bin");
    let out = run_with_args(&[
        std::ffi::OsStr::new("build"),
        p.as_os_str(),
        std::ffi::OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        !out.status.success(),
        "aot must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from aot; stderr={}",
        stderr
    );
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
    std::fs::write(&source_path, src).expect("write variadic open fixture");

    let build = run_with_args(&[
        std::ffi::OsStr::new("build"),
        source_path.as_os_str(),
        std::ffi::OsStr::new("-o"),
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

    let mode = std::fs::metadata(&created_path)
        .expect("created file metadata")
        .permissions()
        .mode()
        & 0o777;
    let _ = std::fs::remove_file(&created_path);
    let _ = std::fs::remove_file(&source_path);
    let _ = std::fs::remove_file(&out_bin);
    let _ = std::fs::remove_file(out_bin.with_extension("o"));
    assert_eq!(mode, (requested as u32) & !(umask as u32) & 0o777);
}
