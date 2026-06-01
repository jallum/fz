use crate::fz_ir::Module;
use crate::ir_interp::run_main;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    crate::ir_lower::lower_program(
        &mut crate::types::ConcreteTypes,
        &prog,
        &crate::telemetry::NullTelemetry,
    )
    .expect("lower")
}

#[cfg(unix)]
#[test]
#[serial_test::serial]
fn variadic_open_interp_creates_file_with_mode_bits() {
    use std::ffi::CString;
    use std::os::unix::fs::PermissionsExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct UmaskGuard(libc::mode_t);
    impl Drop for UmaskGuard {
        fn drop(&mut self) {
            unsafe {
                libc::umask(self.0);
            }
        }
    }

    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "fz-interp-variadic-open-{}-{}",
        std::process::id(),
        unique
    ));
    let path_text = path.to_string_lossy();
    assert!(
        CString::new(path_text.as_bytes()).is_ok(),
        "test path must be representable as a C string"
    );

    let requested: libc::mode_t = 0o764;
    let umask: libc::mode_t = 0o027;
    let _guard = UmaskGuard(unsafe { libc::umask(umask) });
    let flags = libc::O_CREAT | libc::O_EXCL | libc::O_RDWR;
    let src = format!(
        r#"
extern "C" fn libc::open(path :: cstring, flags :: integer, ...) :: integer
extern "C" fn libc::close(fd :: integer) :: integer
fn main() do
  fd = libc::open("{}", {}, {} :: integer)
  libc::close(fd)
  fd
end
"#,
        path_text, flags, requested
    );

    let module = lower_src(&src);
    let fd = run_main(&crate::telemetry::NullTelemetry, &module).expect("interp run");
    assert!(fd >= 0, "open failed with fd {}", fd);
    let mode = std::fs::metadata(&path)
        .expect("created file metadata")
        .permissions()
        .mode()
        & 0o777;
    let _ = std::fs::remove_file(&path);
    assert_eq!(mode, (requested as u32) & !(umask as u32) & 0o777);
}

#[test]
fn unsupported_variadic_extern_shape_is_interp_error() {
    let module = lower_src(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%f", 1.5) end
"#,
    );
    let err = run_main(&crate::telemetry::NullTelemetry, &module)
        .expect_err("unsupported variadic shape should fail interp");
    assert!(err.contains("unsupported variadic extern shape"));
    assert!(err.contains("F64"));
}
