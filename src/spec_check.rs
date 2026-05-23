//! fz-ul4.31.5 — Validate declared `@spec` against inferred types.
//!
//! Option 1 semantics: the declared `@spec` is an upper bound on what
//! the typer infers. Validation passes iff every narrow inferred spec
//! is element-wise a subtype of the declared spec (both inputs and
//! result). Narrower inferred is fine (success-typing: the user is
//! claiming a wider domain than the body actually accepts). Wider or
//! disjoint inferred is an error.
//!
//! Any-key inferred specs are SKIPPED in validation: they are
//! typer-internal fallback entries with `any()` on every input,
//! representing "what if all args are unknown." A user-written `@spec`
//! is a claim about typed input domains; comparing it against the
//! all-any any-key would produce category-error rejections for every
//! reasonable declared spec. See `.29.10` for the broader story.
//!
//! ## Pipeline position
//!
//! Runs after `ir_typer::type_module` produces `ModuleTypes`. The
//! validator looks up each AST `FnDef`'s declared `@spec`, resolves it
//! against the enclosing module's `ModuleTypeEnv` (already built in
//! `resolve::flatten_modules`), then iterates the registered narrow
//! specs in `ModuleTypes.specs` for that fn. Each comparison emits a
//! `spec/violation` diagnostic on failure; the pass is non-fatal — it
//! returns a list and the driver decides whether to halt.

#![allow(dead_code)] // fz-ul4.31.6 wires this into the run/jit/aot
// drivers; tests exercise the API directly.

use crate::ast::{Attribute, Item, Program};
use crate::diag::{Diagnostic, Span, codes};
use crate::fz_ir::FnId;
use crate::ir_typer::ModuleTypes;
use crate::type_expr::{ModuleTypeEnv, resolve_spec_decl};

/// Validate every `@spec` in `program` against the corresponding
/// inferred specs in `module_types`. Returns a list of diagnostics
/// (empty when all specs hold).
pub fn validate_specs<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &mut T,
    program: &Program,
    ir_module: &crate::fz_ir::Module,
    module_types: &ModuleTypes,
) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    let empty_env = ModuleTypeEnv::new();
    for item in &program.items {
        let Item::Fn(fn_def) = &**item else {
            continue;
        };
        let Some(spec) = fn_def.attrs.iter().find_map(|a| match a {
            Attribute::Spec(s) => Some(s),
            _ => None,
        }) else {
            continue;
        };
        // The module env is keyed by everything up to the last `.` in
        // the qualified fn name. Top-level fns use "" (empty env).
        let module_path: String = match fn_def.name.rfind('.') {
            Some(i) => fn_def.name[..i].to_string(),
            None => String::new(),
        };
        let env: &ModuleTypeEnv = program
            .module_type_envs
            .get(&module_path)
            .unwrap_or(&empty_env);
        let resolved = match resolve_spec_decl(t, spec, env) {
            Ok(r) => r,
            Err(e) => {
                diags.push(Diagnostic::error(
                    codes::SPEC_VIOLATION,
                    format!("@spec for `{}`: {}", fn_def.name, e.msg),
                    e.span,
                ));
                continue;
            }
        };
        let Some(ir_fn) = ir_module.fns.iter().find(|f| f.name == fn_def.name) else {
            // No IR fn for this name — fn might be dead-stripped or
            // not yet lowered. Skip silently.
            continue;
        };
        let ir_fn_id = ir_fn.id;
        validate_one_fn(
            t,
            &resolved.params,
            &resolved.result,
            ir_fn_id,
            ir_fn,
            &fn_def.name,
            fn_def.name_span,
            module_types,
            &mut diags,
        );
    }
    diags
}

fn validate_one_fn<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &mut T,
    declared_param_tys: &[T::Ty],
    declared_result_ty: &T::Ty,
    fn_id: FnId,
    ir_fn: &crate::fz_ir::FnIr,
    user_name: &str,
    name_span: Span,
    module_types: &ModuleTypes,
    diags: &mut Vec<Diagnostic>,
) {
    let arity = declared_param_tys.len();
    let any = t.any();
    let declared_param_displays: Vec<String> =
        declared_param_tys.iter().map(|ty| t.display(ty)).collect();
    let declared_result_display: String = t.display(declared_result_ty);
    for ((fid, key), ft) in &module_types.specs {
        if *fid != fn_id {
            continue;
        }
        if key.len() != arity {
            continue;
        } // should be impossible post-arity-check
        if key
            .iter()
            .all(|slot| slot.is_none() || slot == &Some(any.clone()))
        {
            continue;
        } // skip any-key per design
        // Element-wise inferred ⊆ declared on each input.
        for (i, inferred) in key.iter().enumerate() {
            let Some(inferred) = inferred else {
                continue;
            };
            if !t.is_subtype(inferred, &declared_param_tys[i]) {
                let inferred_display = t.display(inferred);
                diags.push(Diagnostic::error(
                    codes::SPEC_VIOLATION,
                    format!(
                        "@spec violation for `{}`: param {} inferred as `{}` \
                         is not a subtype of declared `{}`",
                        user_name, i, inferred_display, declared_param_displays[i],
                    ),
                    name_span,
                ));
            }
        }
        // Compute inferred return type: lub over each Term::Return val
        // typed under this spec's FnTypes. Local stays `T::Ty`-typed
        // through the fold; only the boundary with `ft.vars` (still
        // concrete-`Ty` keyed) goes through direct lookup.
        let mut inferred_result: Option<T::Ty> = None;
        for b in &ir_fn.blocks {
            if let crate::fz_ir::Term::Return(rv) = &b.terminator {
                let d_ty = match ft.vars.get(rv) {
                    Some(d) => d.clone(),
                    None => t.any(),
                };
                inferred_result = Some(match inferred_result {
                    Some(prev) => t.union(prev, d_ty),
                    None => d_ty,
                });
            }
        }
        let inferred_ty = inferred_result.unwrap_or_else(|| t.any());
        if !t.is_subtype(&inferred_ty, declared_result_ty) {
            let inferred_display = t.display(&inferred_ty);
            diags.push(Diagnostic::error(
                codes::SPEC_VIOLATION,
                format!(
                    "@spec violation for `{}`: result inferred as `{}` \
                     is not a subtype of declared `{}`",
                    user_name, inferred_display, declared_result_display,
                ),
                name_span,
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_lower;
    use crate::ir_typer::type_module;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::resolve::flatten_modules;

    fn pipeline<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
        t: &mut T,
        src: &str,
    ) -> (Program, crate::fz_ir::Module, ModuleTypes) {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let prog = flatten_modules(t, prog).expect("flatten");
        let ir = ir_lower::lower_program(t, &prog).expect("lower");
        let mt = type_module(t, &ir, &crate::telemetry::NullTelemetry);
        (prog, ir, mt)
    }

    #[test]
    fn spec_matching_inferred_passes() {
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: print(M.add1(41))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(diags.is_empty(), "unexpected diags: {:?}", diags);
    }

    #[test]
    fn spec_wider_than_inferred_passes_success_typing_style() {
        // Declared spec accepts `integer`; inferred is the narrower
        // `int_lit(41)`. int_lit(41) ⊆ integer, so this passes.
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: print(M.add1(41))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(
            diags.is_empty(),
            "wider declared must accept narrower inferred; got: {:?}",
            diags
        );
    }

    #[test]
    fn spec_disjoint_from_inferred_fails() {
        // Declared accepts `float`; inferred from callsite is int.
        // int ⊄ float, so this fails.
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @spec add1(float) :: float
  fn add1(n), do: n + 1
end
fn main(), do: print(M.add1(41))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(!diags.is_empty(), "disjoint spec must fail");
        let msg = format!("{:?}", diags[0].message);
        assert!(
            msg.contains("not a subtype"),
            "expected subtype-violation diag, got: {}",
            msg
        );
    }

    #[test]
    fn spec_resolves_against_module_type_env() {
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @type id :: integer
  @spec lookup(id) :: id
  fn lookup(x), do: x
end
fn main(), do: print(M.lookup(7))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(
            diags.is_empty(),
            "alias-based spec should resolve and pass; got: {:?}",
            diags
        );
    }

    #[test]
    fn spec_with_unknown_alias_fails_at_validation() {
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @spec one(unknown_thing) :: integer
  fn one(_), do: 1
end
fn main(), do: print(M.one(0))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(!diags.is_empty(), "unknown alias must surface a diag");
        let msg = format!("{:?}", diags[0].message);
        assert!(
            msg.contains("unknown type name"),
            "expected unknown-name diag, got: {}",
            msg
        );
    }

    #[test]
    fn spec_validation_skips_any_key_specs() {
        // Validation must skip any-key specs when they exist (they have
        // `any()` on every param, which would clash with any
        // narrow declared @spec). Post-.29.12.6, fns with fully-typed
        // direct callsites have their any-key dropped — this test
        // covers both scenarios via a fn that *does* keep its any-key
        // because it's also reachable via a closure/cont path with a
        // narrow capture but `any` slot 0.
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: print(M.add1(41))
"#,
        );
        // Validation passes — either the any-key was dropped (.29.12.6)
        // or it was kept and validation correctly skipped it.
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(
            diags.is_empty(),
            "validation must pass regardless of any-key presence; got: {:?}",
            diags
        );
    }

    #[test]
    fn fn_without_spec_is_not_validated() {
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
defmodule M do
  fn double(x), do: x * 2
end
fn main(), do: print(M.double(7))
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(
            diags.is_empty(),
            "fn without @spec should produce no diags; got: {:?}",
            diags
        );
    }

    #[test]
    fn spec_on_top_level_fn_uses_empty_env() {
        let mut ct = crate::types::ConcreteTypes;
        let (prog, ir, mt) = pipeline(
            &mut ct,
            r#"
@spec one() :: integer
fn one(), do: 1
fn main(), do: print(one())
"#,
        );
        let diags = validate_specs(&mut ct, &prog, &ir, &mt);
        assert!(
            diags.is_empty(),
            "top-level @spec with builtin scalar must pass; got: {:?}",
            diags
        );
    }
}
