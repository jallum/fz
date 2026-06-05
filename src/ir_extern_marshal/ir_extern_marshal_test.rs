use super::*;
use crate::frontend::{FrontendOk, compile_source_with_types};
use crate::fz_ir::{ExternMarshal, Prim};
use crate::telemetry::ConfiguredTelemetry;

fn compile(src: &str) -> FrontendOk {
    let mut t = crate::types::new();
    let tel = ConfiguredTelemetry::new();
    compile_source_with_types(&mut t, src.to_string(), "test.fz".to_string(), &tel)
        .unwrap_or_else(|err| panic!("frontend failed: {:?}", err.diagnostics.as_slice()))
}

fn main_extern_arg(ok: &FrontendOk, arg_idx: usize) -> ExternTy {
    let main = ok.module.fn_by_name("main").expect("main missing");
    let (block_id, stmt_idx, args) = main
        .blocks
        .iter()
        .flat_map(|block| {
            block.stmts.iter().enumerate().filter_map(move |(i, stmt)| {
                let Stmt::Let(_, Prim::Extern(_, _, args)) = stmt else {
                    return None;
                };
                Some((block.id, i, args))
            })
        })
        .next()
        .expect("extern call missing");
    assert!(matches!(
        args[arg_idx].marshal,
        ExternMarshal::Auto | ExternMarshal::Ascribed(_)
    ));
    let spec = ok.module_plan.any_spec_for(main.id).expect("main spec missing");
    spec.extern_marshals[&ExternMarshalSite {
        block: block_id,
        stmt_idx,
        arg_idx,
    }]
}

#[test]
fn auto_int_literal_resolves_to_i64() {
    let ok = compile(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%d", 7) end
"#,
    );
    assert!(ok.diagnostics.as_slice().is_empty());
    assert_eq!(main_extern_arg(&ok, 1), ExternTy::I64);
}

#[test]
fn auto_float_literal_resolves_to_f64() {
    let ok = compile(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%f", 1.5) end
"#,
    );
    assert!(ok.diagnostics.as_slice().is_empty());
    assert_eq!(main_extern_arg(&ok, 1), ExternTy::F64);
}

#[test]
fn binary_auto_requires_explicit_ascription() {
    let ok = compile(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%s", "hello") end
"#,
    );
    let d = ok
        .diagnostics
        .as_slice()
        .iter()
        .find(|d| d.code == codes::TYPE_EXTERN_MARSHAL)
        .expect("marshal diagnostic missing");
    assert!(d.message.contains("binary values need an explicit"));
    assert!(d.helps.iter().any(|h| h.contains(":: cstring")));
}

#[test]
fn binary_explicit_ascription_resolves() {
    let ok = compile(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%s", "hello" :: cstring) end
"#,
    );
    assert!(ok.diagnostics.as_slice().is_empty());
    assert_eq!(main_extern_arg(&ok, 1), ExternTy::CString);
}

#[test]
fn list_auto_errors_cleanly() {
    let ok = compile(
        r#"
extern "C" fn libc::printf(fmt :: cstring, ...) :: integer
fn main() do libc::printf("%p", [1, 2]) end
"#,
    );
    let d = ok
        .diagnostics
        .as_slice()
        .iter()
        .find(|d| d.code == codes::TYPE_EXTERN_MARSHAL)
        .expect("marshal diagnostic missing");
    assert!(d.message.contains("no default C variadic marshal class"));
}
