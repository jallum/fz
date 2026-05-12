//! fz-ul4.31.6 — three-path parity for `@spec` violation rejection.
//!
//! Builds a deliberately-wrong `@spec` (declared `float -> float` on a
//! body called only with ints) and verifies the `fz` binary rejects it
//! with a `spec/violation` diagnostic on each of the three execution
//! paths: `fz interp`, `fz run` (JIT), `fz build` (AOT). The same
//! validation pass runs in every driver, so the verdict is invariant
//! by construction; this test pins the wiring against regression.

use std::process::Command;

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");

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

fn run_with_args(args: &[&std::ffi::OsStr]) -> std::process::Output {
    Command::new(FZ_BIN)
        .args(args)
        .output()
        .expect("invoke fz binary")
}

#[test]
fn interp_rejects_spec_violation() {
    let p = write_temp_fz("interp");
    let out = run_with_args(&[
        std::ffi::OsStr::new("interp"),
        p.as_os_str(),
    ]);
    assert!(!out.status.success(),
        "interp must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from interp; stderr={}", stderr);
}

#[test]
fn jit_rejects_spec_violation() {
    let p = write_temp_fz("jit");
    let out = run_with_args(&[
        std::ffi::OsStr::new("run"),
        p.as_os_str(),
    ]);
    assert!(!out.status.success(),
        "jit must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from jit; stderr={}", stderr);
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
    assert!(!out.status.success(),
        "aot must reject @spec violation; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("spec/violation") || stderr.contains("@spec violation"),
        "expected spec/violation diag from aot; stderr={}", stderr);
}
