//! AOT extern execution through ordinary private declarations.
//!
//! These tests build and execute linked programs so declared externs are proven
//! through the AOT linker, not merely present in an object file.

use std::env::temp_dir;
use std::ffi::OsStr;
use std::fs::{metadata, remove_file, write};
use std::path::PathBuf;
use std::process::{Command, Output, id};
use std::sync::atomic::{AtomicU64, Ordering};

const FZ2_BIN: &str = env!("CARGO_BIN_EXE_fz2");
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_temp_path(prefix: &str, suffix: &str) -> PathBuf {
    let nonce = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    temp_dir().join(format!("{}_{}_{}{}", prefix, id(), nonce, suffix))
}

fn run_with_args(args: &[&OsStr]) -> Output {
    Command::new(FZ2_BIN).args(args).output().expect("invoke fz2 binary")
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
extern "C" defp libc::open(path :: c_string, flags :: c_int, ...) :: c_int
extern "C" defp libc::close(fd :: c_int) :: c_int
def main() do
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

#[test]
fn aot_kernel_float_remainder_calls_the_private_runtime_export() {
    let source_path = unique_temp_path("fz_kernel_rem_ff_aot", ".fz");
    let out_bin = unique_temp_path("fz_kernel_rem_ff_aot", ".bin");
    write(&source_path, "def main() do\n  dbg(-7.5 % 2.0)\n  nil\nend\n").expect("write remainder fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot remainder build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&out_bin).output().expect("run remainder aot binary");
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert!(
        run.status.success(),
        "aot remainder binary failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "-1.5\n");
}

#[test]
fn aot_kernel_self_and_make_ref_call_their_typed_private_exports() {
    let source_path = unique_temp_path("fz_kernel_self_ref_aot", ".fz");
    let out_bin = unique_temp_path("fz_kernel_self_ref_aot", ".bin");
    write(
        &source_path,
        "def main(), do: if self() == self() and make_ref() != make_ref(), do: dbg(42), else: dbg(0)\n",
    )
    .expect("write self/ref fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot self/ref build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&out_bin).output().expect("run self/ref aot binary");
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert!(
        run.status.success(),
        "aot self/ref binary failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "42\n");
}

#[test]
fn aot_kernel_make_resource_calls_the_private_runtime_export_and_drains_its_dtor() {
    let source_path = unique_temp_path("fz_kernel_make_resource_aot", ".fz");
    let out_bin = unique_temp_path("fz_kernel_make_resource_aot", ".bin");
    write(
        &source_path,
        "extern \"C\" defp fz_resource_test_print_dtor(integer) :: nil\n\
         def dtor(value), do: fz_resource_test_print_dtor(value)\n\
         def main() do\n\
           _resource = make_resource(42, &dtor/1)\n\
           dbg(:before)\n\
         end\n",
    )
    .expect("write make_resource fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot make_resource build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&out_bin).output().expect("run make_resource aot binary");
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert!(
        run.status.success(),
        "aot make_resource binary failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), ":before\ndtor:42\n");
}

#[cfg(unix)]
#[test]
fn aot_c_extern_nonzero_boolean_is_true() {
    let source_path = unique_temp_path("fz_nonzero_boolean_aot", ".fz");
    let out_bin = unique_temp_path("fz_nonzero_boolean_aot", ".bin");
    write(
        &source_path,
        "extern \"C\" defp abs(c_int) :: boolean\ndef main(), do: if abs(7), do: dbg(42), else: dbg(0)\n",
    )
    .expect("write nonzero Boolean fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot nonzero Boolean build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&out_bin).output().expect("run nonzero Boolean aot binary");
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert!(
        run.status.success(),
        "AOT nonzero Boolean binary failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr),
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "42\n");
}

#[test]
fn aot_raw_arithmetic_pair_edges_match_the_real_total_c_exports() {
    let source_path = unique_temp_path("fz_arithmetic_raw_pair_edges_aot", ".fz");
    let out_bin = unique_temp_path("fz_arithmetic_raw_pair_edges_aot", ".bin");
    write(
        &source_path,
        include_str!("../fixtures2/00556_arithmetic_raw_pair_edges.fz"),
    )
    .expect("write arithmetic raw-pair fixture");

    let build = run_with_args(&[
        OsStr::new("build"),
        source_path.as_os_str(),
        OsStr::new("-o"),
        out_bin.as_os_str(),
    ]);
    assert!(
        build.status.success(),
        "aot arithmetic raw-pair build failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    let run = Command::new(&out_bin)
        .output()
        .expect("run arithmetic raw-pair aot binary");
    let _ = remove_file(&source_path);
    let _ = remove_file(&out_bin);
    let _ = remove_file(out_bin.with_extension("o"));
    assert!(
        run.status.success(),
        "AOT raw arithmetic pair fixture failed; stdout={:?} stderr={:?}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr),
    );
}
