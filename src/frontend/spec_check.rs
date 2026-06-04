//! Validate declared `@spec` overload sets against inferred planner facts.
//!
//! A declared `@spec` is an upper bound on what the planner infers. Validation
//! passes when every narrow inferred spec is covered by at least one declared
//! arrow: inferred inputs must fit the declared inputs, and the inferred result
//! must fit that same arrow's declared result. Narrower inferred behavior is
//! accepted. Wider or disjoint inferred behavior is an error.
//!
//! Any-key inferred specs are SKIPPED in validation: they are
//! planner-internal fallback entries with `any()` on every input,
//! representing "what if all args are unknown." A user-written `@spec`
//! is a claim about typed input domains; comparing it against the
//! all-any any-key would produce category-error rejections for every
//! reasonable declared spec.
//!
//! ## Pipeline position
//!
//! Runs after `ir_planner::plan_module` produces `ModulePlan`. The
//! validator looks up each AST `FnDef`'s declared `@spec`, resolves it
//! against the enclosing module's `ModuleTypeEnv` (already built in
//! `resolve::flatten_modules`), then iterates the registered narrow
//! specs in `ModulePlan.specs` for that fn. Each comparison emits a
//! `spec/violation` diagnostic on failure; the pass is non-fatal — it
//! returns a list and the driver decides whether to halt.

use crate::ast::{Attribute, Item, Program};
use crate::diag::{Diagnostic, Span, codes};
use crate::fz_ir::{FnId, FnIr, Module, Term};
use crate::ir_planner::ModulePlan;
use crate::ir_planner::fn_types::SpecPlan;
use crate::specs::{ResolvedSpecSet, declared_specs_cover_inferred_spec};
use crate::type_expr::{ModuleTypeEnv, resolve_spec_decls};
use crate::types::{ClosureTypes, RenderTypes, Ty, Types};

/// Validate every `@spec` in `program` against the corresponding
/// inferred specs in `module_plan`. Returns a list of diagnostics
/// (empty when all specs hold).
pub fn validate_specs<T: ClosureTypes<Ty = Ty> + RenderTypes>(
    t: &mut T,
    program: &Program,
    ir_module: &Module,
    module_plan: &ModulePlan,
) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    let empty_env = ModuleTypeEnv::new();
    for item in &program.items {
        let Item::Fn(fn_def) = &**item else {
            continue;
        };
        let specs = fn_def
            .attrs
            .iter()
            .filter_map(|a| match a {
                Attribute::Spec(s) => Some(s),
                _ => None,
            })
            .collect::<Vec<_>>();
        if specs.is_empty() {
            continue;
        }
        // The module env is keyed by everything up to the last `.` in
        // the qualified fn name. Top-level fns use "" (empty env).
        let module_path: String = match fn_def.name.rfind('.') {
            Some(i) => fn_def.name[..i].to_string(),
            None => String::new(),
        };
        let env: &ModuleTypeEnv = program.module_type_envs.get(&module_path).unwrap_or(&empty_env);
        let resolved = match resolve_spec_decls(t, specs, env) {
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
            &resolved,
            ir_fn_id,
            ir_fn,
            &fn_def.name,
            fn_def.name_span,
            module_plan,
            &mut diags,
        );
    }
    diags
}

fn validate_one_fn<T: ClosureTypes<Ty = Ty> + RenderTypes>(
    t: &mut T,
    declared_specs: &ResolvedSpecSet,
    fn_id: FnId,
    ir_fn: &FnIr,
    user_name: &str,
    name_span: Span,
    module_plan: &ModulePlan,
    diags: &mut Vec<Diagnostic>,
) {
    let any = t.any();
    for (key, ft) in &module_plan.specs {
        if key.fn_id != fn_id || !key.demand.is_value() {
            continue;
        }
        if key
            .input
            .iter()
            .all(|slot| slot.is_none() || slot == &Some(any.clone()))
        {
            continue;
        } // skip any-key per design
        let inferred_ty = inferred_result_ty(t, ir_fn, ft)
            .or_else(|| module_plan.effective_returns.get(&key.body_key()).cloned())
            .unwrap_or_else(|| t.any());
        if !declared_specs_cover_inferred_spec(t, declared_specs, &key.input, &inferred_ty) {
            let inferred_inputs = key
                .input
                .iter()
                .map(|slot| match slot {
                    Some(ty) => t.display(ty),
                    None => "_".to_string(),
                })
                .collect::<Vec<_>>()
                .join(", ");
            diags.push(Diagnostic::error(
                codes::SPEC_VIOLATION,
                format!(
                    "@spec violation for `{}`: inferred ({}) -> `{}` is not a subtype \
                     of any declared @spec arrow",
                    user_name,
                    inferred_inputs,
                    t.display(&inferred_ty),
                ),
                name_span,
            ));
        }
    }
}

fn inferred_result_ty<T: Types<Ty = Ty>>(t: &mut T, ir_fn: &FnIr, ft: &SpecPlan) -> Option<T::Ty> {
    let mut inferred_result: Option<T::Ty> = None;
    for b in &ir_fn.blocks {
        if let Term::Return(rv) = &b.terminator {
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
    inferred_result
}

#[cfg(test)]
#[path = "spec_check_test.rs"]
mod spec_check_test;
