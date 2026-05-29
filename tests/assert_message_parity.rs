//! fz-6df.1 — four-path parity for `Kernel.assert/2` / `refute/2` messages.
//!
//! `assert(x, msg)` / `refute(x, msg)` route the caller's message through the
//! existing `panic/1` -> `fz_panic` path on the failing branch. This test pins
//! that the caller-supplied message reaches the abort (rendered as
//! `fz panic: <message>`) identically on each execution path: `fz interp`,
//! `fz run` (JIT), `fz build` (AOT), and `fz repl --script`.
//!
//! The fixture matrix cannot cover this: a runtime abort is a nonzero exit,
//! which the matrix scores as a failure before any output comparison. So the
//! failing branch is pinned here; the passing branch is exercised by the broad
//! assertion-fixture set (every converted fixture calls `assert`/`refute`).

use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

const FZ_BIN: &str = env!("CARGO_BIN_EXE_fz");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

const MESSAGE: &str = "custom assertion message";

const ASSERT_SRC: &str = "\
fn main() do
  assert(1 == 2, \"custom assertion message\")
end
";

const REFUTE_SRC: &str = "\
fn main() do
  refute(1 == 1, \"custom assertion message\")
end
";

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

fn write_src(name: &str, src: &str) -> std::path::PathBuf {
    let path = unique_temp_path(&format!("fz_assert_msg_{}", name), ".fz");
    std::fs::write(&path, src).expect("write temp fixture");
    path
}

fn assert_aborts_with_message(ctx: &str, out: &std::process::Output) {
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "{ctx} must abort; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&out.stdout),
        stderr
    );
    assert!(
        stderr.contains(MESSAGE),
        "{ctx} must surface the caller message {MESSAGE:?}; stderr={stderr}"
    );
}

fn run(args: &[&std::ffi::OsStr]) -> std::process::Output {
    Command::new(FZ_BIN)
        .args(args)
        .output()
        .expect("invoke fz binary")
}

fn check_interp(name: &str, src: &str) {
    let p = write_src(name, src);
    let out = run(&[std::ffi::OsStr::new("interp"), p.as_os_str()]);
    assert_aborts_with_message(&format!("interp/{name}"), &out);
    let _ = std::fs::remove_file(&p);
}

fn check_jit(name: &str, src: &str) {
    let p = write_src(name, src);
    let out = run(&[std::ffi::OsStr::new("run"), p.as_os_str()]);
    assert_aborts_with_message(&format!("jit/{name}"), &out);
    let _ = std::fs::remove_file(&p);
}

fn check_repl(name: &str, src: &str) {
    let p = write_src(name, src);
    let out = run(&[
        std::ffi::OsStr::new("repl"),
        std::ffi::OsStr::new("--script"),
        p.as_os_str(),
    ]);
    assert_aborts_with_message(&format!("repl/{name}"), &out);
    let _ = std::fs::remove_file(&p);
}

fn check_aot(name: &str, src: &str) {
    let p = write_src(name, src);
    let out_bin = unique_temp_path(&format!("fz_assert_msg_{}_aot", name), ".bin");
    let build = run(&[
        std::ffi::OsStr::new("build"),
        p.as_os_str(),
        std::ffi::OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot/{name} build failed; stderr={}",
        String::from_utf8_lossy(&build.stderr)
    );
    let out = Command::new(&out_bin).output().expect("run aot binary");
    assert_aborts_with_message(&format!("aot/{name}"), &out);
    let _ = std::fs::remove_file(&p);
    let _ = std::fs::remove_file(&out_bin);
    let _ = std::fs::remove_file(out_bin.with_extension("o"));
}

#[test]
fn interp_assert_message_reaches_abort() {
    check_interp("assert", ASSERT_SRC);
    check_interp("refute", REFUTE_SRC);
}

#[test]
fn jit_assert_message_reaches_abort() {
    check_jit("assert", ASSERT_SRC);
    check_jit("refute", REFUTE_SRC);
}

#[test]
fn repl_assert_message_reaches_abort() {
    check_repl("assert", ASSERT_SRC);
    check_repl("refute", REFUTE_SRC);
}

#[test]
fn aot_assert_message_reaches_abort() {
    check_aot("assert", ASSERT_SRC);
    check_aot("refute", REFUTE_SRC);
}
