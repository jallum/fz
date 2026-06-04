use crate::diag::{Diagnostic, Span, codes};
use crate::fz_ir::{ExternMarshal, ExternMarshalSite, ExternTy, FnId, Module, Prim, Stmt};
use crate::ir_planner::{ModulePlan, SpecPlan};
use crate::types::{RenderTypes, Ty, Types};

pub fn resolve_module_types<T>(t: &mut T, module: &Module, module_types: &mut ModulePlan) -> Vec<Diagnostic>
where
    T: Types<Ty = Ty> + RenderTypes,
{
    let mut diagnostics = Vec::new();
    let mut specs: Vec<_> = module_types.specs.keys().cloned().collect();
    specs.sort_by_key(|key| {
        (
            key.fn_id.0,
            module_types
                .spec_precedence
                .get(&key.body_key())
                .copied()
                .unwrap_or(u32::MAX),
        )
    });

    for spec_key in specs {
        let Some(fn_types) = module_types.specs.get_mut(&spec_key) else {
            continue;
        };
        diagnostics.extend(resolve_fn_types(t, module, spec_key.fn_id, fn_types));
    }

    diagnostics
}

pub fn resolve_fn_types<T>(t: &mut T, module: &Module, fn_id: FnId, fn_types: &mut SpecPlan) -> Vec<Diagnostic>
where
    T: Types<Ty = Ty> + RenderTypes,
{
    let mut diagnostics = Vec::new();
    let Some(fn_idx) = module.fn_idx.get(&fn_id).copied() else {
        return diagnostics;
    };
    let f = &module.fns[fn_idx];
    fn_types.extern_marshals.clear();

    for block in &f.blocks {
        let stmt_spans = module.source.stmt_spans.get(&(f.id, block.id));
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let Stmt::Let(_, Prim::Extern(_, eid, args)) = stmt else {
                continue;
            };
            let decl = module.extern_by_id(*eid);
            let span = stmt_spans
                .and_then(|spans| spans.get(stmt_idx))
                .copied()
                .unwrap_or(Span::DUMMY);
            for (arg_idx, arg) in args.iter().enumerate() {
                let site = ExternMarshalSite {
                    block: block.id,
                    stmt_idx,
                    arg_idx,
                };
                match arg.marshal {
                    ExternMarshal::Fixed(ty) => {
                        fn_types.extern_marshals.insert(site, ty);
                    }
                    ExternMarshal::Ascribed(ty) => {
                        fn_types.extern_marshals.insert(site, ty);
                        if let Some(arg_ty) = fn_types.vars.get(&arg.var)
                            && let Some(diag) = check_explicit_ascription(t, decl.symbol.as_str(), ty, arg_ty, span)
                        {
                            diagnostics.push(diag);
                        }
                    }
                    ExternMarshal::Auto if decl.variadic => {
                        let resolved = fn_types
                            .vars
                            .get(&arg.var)
                            .map(|arg_ty| resolve_auto(t, decl.symbol.as_str(), arg_ty, span))
                            .unwrap_or_else(|| {
                                Err(Box::new(marshal_diag(
                                    decl.symbol.as_str(),
                                    span,
                                    "cannot infer a C variadic marshal class for this argument",
                                    "add an explicit call-argument ascription such as `:: integer`, `:: float`, `:: cstring`, or `:: binary`",
                                )))
                            });
                        match resolved {
                            Ok(ty) => {
                                fn_types.extern_marshals.insert(site, ty);
                            }
                            Err(diag) => diagnostics.push(*diag),
                        }
                    }
                    ExternMarshal::Auto => {
                        diagnostics.push(marshal_diag(
                            decl.symbol.as_str(),
                            span,
                            "non-variadic extern call has unresolved marshal metadata",
                            "this is an internal lowering invariant violation",
                        ));
                    }
                }
            }
        }
    }

    diagnostics
}

fn resolve_auto<T>(t: &mut T, symbol: &str, arg_ty: &Ty, span: Span) -> Result<ExternTy, Box<Diagnostic>>
where
    T: Types<Ty = Ty> + RenderTypes,
{
    if t.is_integer(arg_ty) {
        return Ok(ExternTy::I64);
    }
    if t.is_floating(arg_ty) {
        return Ok(ExternTy::F64);
    }
    let str_ty = t.str_t();
    if t.is_subtype(arg_ty, &str_ty) {
        return Err(Box::new(marshal_diag(
            symbol,
            span,
            "binary values need an explicit C variadic marshal class",
            "write the argument as `value :: cstring` for a NUL-terminated pointer or `value :: binary` for raw bytes",
        )));
    }
    Err(Box::new(
        marshal_diag(
            symbol,
            span,
            format!(
                "no default C variadic marshal class for fz type `{}`",
                t.display(arg_ty)
            ),
            "add an explicit ascription only if the callee really expects one of the supported C wire types",
        )
        .with_note(format!(
            "extern `{}` is variadic; automatic marshaling only defaults integer to i64 and float to f64",
            symbol
        )),
    ))
}

fn check_explicit_ascription<T>(
    t: &mut T,
    symbol: &str,
    ascribed: ExternTy,
    arg_ty: &Ty,
    span: Span,
) -> Option<Diagnostic>
where
    T: Types<Ty = Ty> + RenderTypes,
{
    let expected = match ascribed {
        ExternTy::I64 => t.int(),
        ExternTy::F64 => t.float(),
        ExternTy::Binary | ExternTy::CString => t.str_t(),
        ExternTy::Any => return None,
        ExternTy::Unit | ExternTy::Never => {
            return Some(marshal_diag(
                symbol,
                span,
                format!("{:?} is not a valid extern argument marshal class", ascribed),
                "use `integer`, `float`, `any`, `binary`, or `cstring` for extern arguments",
            ));
        }
    };
    if t.is_disjoint(arg_ty, &expected) {
        Some(
            marshal_diag(
                symbol,
                span,
                format!(
                    "extern argument ascribed as {:?}, but the value has fz type `{}`",
                    ascribed,
                    t.display(arg_ty)
                ),
                "make the ascription match the value class before calling the variadic extern",
            )
            .with_note(format!(
                "extern `{}` argument marshal checks run after type inference",
                symbol
            )),
        )
    } else {
        None
    }
}

fn marshal_diag(symbol: &str, span: Span, message: impl Into<String>, help: impl Into<String>) -> Diagnostic {
    Diagnostic::error(codes::TYPE_EXTERN_MARSHAL, message, span)
        .with_label(format!("variadic extern `{}` argument", symbol))
        .with_help(help)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{FrontendOk, compile_source};
    use crate::fz_ir::{ExternMarshal, Prim};

    fn compile(src: &str) -> FrontendOk {
        compile_source(src.to_string(), "test.fz".to_string())
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
}
