pub(crate) mod macros;
pub(crate) mod pattern_check;
pub(crate) mod protocols;
pub(crate) mod resolve;
pub(crate) mod spec_check;
pub(crate) mod spec_registry;

use self::resolve::InterfaceTable;
use crate::ast::{Expr, FnClause, FnDef, Item, Pattern, Program, Spanned, TypeExprBody};
use crate::compiler::{Compiler, CompilerWorld, ModuleId};
use crate::diag::codes;
use crate::diag::emit_through;
use crate::diag::{Diagnostic, Diagnostics, SourceMap, Span};
use crate::fz_ir::{CallsiteId, EmitSlot, FnId, Module, rewrite_external_callsite_for_link};
use crate::ir_extern_marshal::resolve_module_types;
use crate::ir_lower::repl_output_frame_names;
use crate::ir_planner::fn_types::CallEdgeTarget;
use crate::ir_planner::{ModulePlan, plan_module, plan_module_from_entry_fns, rewrite_closed_union_protocol_dispatch};
use crate::measurements;
use crate::metadata;
#[cfg(test)]
use crate::parser::Parser;
#[cfg(test)]
use crate::parser::lexer::Lexer;
use crate::pattern_matrix::SubjectDomain;
use crate::telemetry::value::opaque;
use crate::telemetry::{NullTelemetry, Telemetry, next_compile_nonce};
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Ty, Types};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct FrontendOk {
    pub sm: SourceMap,
    pub _prog: Program,
    pub module: Module,
    pub module_plan: ModulePlan,
    pub diagnostics: Diagnostics,
}

pub struct FrontendErr {
    pub sm: SourceMap,
    pub diagnostics: Diagnostics,
}

pub type FrontendResult = Result<FrontendOk, FrontendErr>;

pub(crate) struct ReplEntryOk {
    pub frontend: FrontendOk,
    pub input_frame: Vec<String>,
    pub output_frame: Vec<String>,
    pub entry_item: Rc<Item>,
}

fn fail(sm: SourceMap, d: Diagnostic) -> FrontendErr {
    FrontendErr {
        sm,
        diagnostics: Diagnostics::from_one(d),
    }
}

pub fn check_patterns<T: Types<Ty = Ty> + ClosureTypes + LiteralTypes>(
    t: &mut T,
    prog: &Program,
    module: &Module,
    module_plan: &ModulePlan,
) -> Diagnostics {
    let survivors: HashSet<(String, usize)> = module_plan
        .reachable_specs
        .iter()
        .filter_map(|spec_key| {
            let &idx = module.fn_idx.get(&spec_key.fn_id)?;
            let f = &module.fns[idx];
            let arity = f.block(f.entry).params.len();
            Some((f.name.clone(), arity))
        })
        .collect();
    let domains = fn_subject_domains(t, module, module_plan);
    Diagnostics::from_vec(pattern_check::check_program(t, prog, Some(&survivors), Some(&domains)))
}

fn fn_subject_domains<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
) -> HashMap<(String, usize), Vec<SubjectDomain>> {
    let any = t.any();
    let list_any = t.list(any);
    let mut by_fn: HashMap<(String, usize), Vec<bool>> = HashMap::new();
    for spec_key in module_plan.specs.keys() {
        let Some(&idx) = module.fn_idx.get(&spec_key.fn_id) else {
            continue;
        };
        let name = module.fns[idx].name.clone();
        let arity = spec_key.input.len();
        let entry = by_fn
            .entry((name, arity))
            .or_insert_with(|| vec![true; spec_key.input.len()]);
        for (i, ty) in spec_key.input.iter().enumerate() {
            entry[i] &= match ty {
                Some(ty) => t.is_subtype(ty, &list_any),
                None => false,
            };
        }
    }
    by_fn
        .into_iter()
        .map(|(name_arity, positions)| {
            (
                name_arity,
                positions
                    .into_iter()
                    .map(|is_list| {
                        if is_list {
                            SubjectDomain::List
                        } else {
                            SubjectDomain::Any
                        }
                    })
                    .collect(),
            )
        })
        .collect()
}

fn check_frontend_from_entry_fns<T>(
    t: &mut T,
    prog: &Program,
    module: &Module,
    entry_fn_ids: &[FnId],
    validate_surface: bool,
    tel: &dyn Telemetry,
) -> (Diagnostics, ModulePlan)
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut mt = if entry_fn_ids.is_empty() {
        plan_module(t, module, tel)
    } else {
        plan_module_from_entry_fns(t, module, entry_fn_ids, tel)
    };
    let mut diags = Diagnostics::new();
    if validate_surface {
        diags.extend(Diagnostics::from_vec(spec_check::validate_specs(t, prog, module, &mt)));
        diags.extend(check_patterns(t, prog, module, &mt));
    }
    diags.extend(Diagnostics::from_vec(resolve_module_types(t, module, &mut mt)));
    tel.execute(
        &["fz", "frontend", "checked"],
        &measurements! { diagnostics: diags.len() },
        &metadata! {
            module_path: module.module_path().to_owned(),
            program: opaque(prog),
            module: opaque(module),
            module_plan: opaque(&mt),
        },
    );
    (diags, mt)
}

#[cfg(test)]
pub fn compile_source(src: String, source_name: String) -> FrontendResult {
    let mut t = crate::types::new();
    compile_source_with_types(&mut t, src, source_name, &NullTelemetry)
}

#[cfg(test)]
pub fn compile_source_with_types<T>(t: &mut T, src: String, source_name: String, tel: &dyn Telemetry) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut compiler = Compiler::new();
    compile_source_with_compiler_types(compiler.world_mut(), t, src, source_name, tel)
}

pub fn compile_source_with_compiler_types<T>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    src: String,
    source_name: String,
    tel: &dyn Telemetry,
) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    compile_source_with_compiler_interface_table(compiler, t, src, source_name, InterfaceTable::new(), tel)
}

#[cfg(test)]
pub fn compile_source_with_interface_table<T>(
    t: &mut T,
    src: String,
    source_name: String,
    interface_table: InterfaceTable,
    tel: &dyn Telemetry,
) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut compiler = Compiler::new();
    compile_source_with_compiler_interface_table(compiler.world_mut(), t, src, source_name, interface_table, tel)
}

pub fn compile_source_with_compiler_interface_table<T>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    src: String,
    source_name: String,
    interface_table: InterfaceTable,
    tel: &dyn Telemetry,
) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    use crate::telemetry::TelemetryExt as _;

    let compile_nonce = next_compile_nonce();
    let _compile_span = tel.span(
        &["fz", "compile"],
        metadata! {
            compile_nonce: compile_nonce,
            source_name: source_name.clone(),
        },
    );

    let root = compiler.register_root_source(&source_name, src, tel);
    let parsed = match compiler.ensure_program(root, tel) {
        Ok(parsed) => parsed,
        Err(diagnostic) => {
            let source = compiler.ensure_source(root, tel);
            let mut sm = SourceMap::new();
            sm.add_file(source_name.clone(), source);
            emit_through(tel, Some(&sm), std::slice::from_ref(&diagnostic));
            return Err(FrontendErr {
                sm: SourceMap::new(),
                diagnostics: Diagnostics::new(),
            });
        }
    };
    let sm = parsed.sm;
    let prog = parsed.program;
    tel.event(
        &["fz", "frontend", "parsed"],
        metadata! {
            items: prog.items.len(),
            program: opaque(&prog),
        },
    );
    compiler.compile_program_from_roots(Some(root), Some(root), t, prog, sm, interface_table, tel)
}

pub(crate) fn compile_program_with_types<T>(
    t: &mut T,
    prog: Program,
    sm: SourceMap,
    tel: &dyn Telemetry,
) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut compiler = Compiler::new();
    compile_program_with_compiler_types(compiler.world_mut(), t, prog, sm, tel)
}

pub(crate) fn compile_program_with_compiler_types<T>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    prog: Program,
    sm: SourceMap,
    tel: &dyn Telemetry,
) -> FrontendResult
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    compiler.compile_program_from_roots(None, None, t, prog, sm, InterfaceTable::new(), tel)
}

impl CompilerWorld {
    pub(crate) fn compile_program_from_roots<T>(
        &mut self,
        root_source: Option<ModuleId>,
        lowering_root_source: Option<ModuleId>,
        t: &mut T,
        prog: Program,
        sm: SourceMap,
        interface_table: InterfaceTable,
        tel: &dyn Telemetry,
    ) -> FrontendResult
    where
        T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
    {
        let mut prog = match resolve::flatten_modules_with_compiler_interface_table(
            t,
            self,
            root_source,
            prog,
            interface_table,
            tel,
        ) {
            Ok(prog) => prog,
            Err(e) => return Err(fail(sm, e.to_diagnostic())),
        };
        tel.event(
            &["fz", "frontend", "resolved"],
            metadata! {
                items: prog.items.len(),
                module_interfaces: prog.module_interfaces.len(),
                program: opaque(&prog),
            },
        );
        if let Err(diagnostic) = macros::prepare_compiler_macro_surfaces(self, root_source, &prog, tel) {
            return Err(fail(sm, diagnostic));
        }
        if let Err(e) = macros::expand_program_with_compiler_types(self, root_source, t, &mut prog) {
            return Err(fail(sm, e.to_diagnostic()));
        }
        resolve::add_macro_requested_runtime_interfaces(self, &mut prog, tel);
        tel.event(
            &["fz", "frontend", "macro_expanded"],
            metadata! {
                items: prog.items.len(),
                program: opaque(&prog),
            },
        );
        let mut module = match crate::ir_lower::lower_program_with_compiler(self, lowering_root_source, t, &prog, tel) {
            Ok(module) => module,
            Err(e) => return Err(fail(sm, e.to_diagnostic())),
        };
        tel.event(
            &["fz", "frontend", "lowered"],
            metadata! {
                module_path: module.module_path().to_owned(),
                fns: module.fns.len(),
                module: opaque(&module),
            },
        );
        let planner_entry_fns = planner_entry_fns(self, lowering_root_source, &module);
        let validate_surface = validate_surface_for_plan(self, lowering_root_source, &planner_entry_fns);
        let (diagnostics, mut module_plan) =
            check_frontend_from_entry_fns(t, &prog, &module, &planner_entry_fns, validate_surface, tel);
        apply_planner_rewrites_to_fixed_point(t, &mut module, &mut module_plan, &planner_entry_fns);
        #[cfg(test)]
        self.validate_invariants()
            .expect("frontend compile must leave compiler world consistent");
        Ok(FrontendOk {
            sm,
            _prog: prog,
            module,
            module_plan,
            diagnostics,
        })
    }
}

fn planner_entry_fns(compiler: &CompilerWorld, lowering_root_source: Option<ModuleId>, module: &Module) -> Vec<FnId> {
    let Some(root_source) = lowering_root_source else {
        return Vec::new();
    };
    if !matches!(
        compiler.module(root_source).origin,
        crate::compiler::ModuleOrigin::EmbeddedRuntime
    ) {
        return Vec::new();
    }
    let entry_keys = compiler.runtime_entry_fn_keys(root_source);
    if entry_keys.is_empty() {
        return Vec::new();
    }
    module
        .fns
        .iter()
        .filter(|fn_ir| entry_keys.contains(&(fn_ir.name.clone(), fn_ir.block(fn_ir.entry).params.len())))
        .map(|fn_ir| fn_ir.id)
        .collect()
}

fn validate_surface_for_plan(
    compiler: &CompilerWorld,
    lowering_root_source: Option<ModuleId>,
    planner_entry_fns: &[FnId],
) -> bool {
    let Some(root_source) = lowering_root_source else {
        return true;
    };
    !matches!(
        compiler.module(root_source).origin,
        crate::compiler::ModuleOrigin::EmbeddedRuntime
    ) || planner_entry_fns.is_empty()
}

pub(crate) fn apply_planner_rewrites_to_fixed_point<T>(
    t: &mut T,
    module: &mut Module,
    module_plan: &mut ModulePlan,
    entry_fn_ids: &[FnId],
) where
    T: Types<Ty = Ty> + ClosureTypes + RenderTypes,
{
    // Protocol/direct-call rewrites can reveal later continuations. Iterate to
    // a fixed point so every newly reachable protocol call is planned and
    // rewritten before the interpreter or native backends see the module.
    loop {
        let direct_changed = apply_planned_direct_call_targets(module, module_plan);
        // Closed-domain protocol switch dispatch. A protocol call whose
        // receiver is a closed union of implementing targets (`integer |
        // list(...)`) has no single planned target for direct-call application,
        // so it would stay a call to the `__protocol__` stub and halt. This
        // rewrites such callsites into a TypeTest/If cascade of per-target
        // direct calls, reusing IR that already lowers in every engine.
        let switch_changed = rewrite_closed_union_protocol_dispatch(t, module, module_plan);
        if !(direct_changed || switch_changed) {
            break;
        }
        *module_plan = if entry_fn_ids.is_empty() {
            plan_module(t, module, &NullTelemetry)
        } else {
            plan_module_from_entry_fns(t, module, entry_fn_ids, &NullTelemetry)
        };
    }
}

fn apply_planned_direct_call_targets(module: &mut Module, module_plan: &ModulePlan) -> bool {
    // A physical callsite is shared by every monomorphized spec of its caller.
    // For ordinary calls the resolved target is spec-invariant, but protocol
    // dispatch resolves the *same* callsite to different impls in different
    // specs (`Enum.count/1[Range]` -> `Range.count`, `[Map]` -> `Map.count`).
    // Rewriting the shared IR to one target would force every spec through one
    // impl - last writer wins - so a range would run `Map.count` and crash.
    //
    // Static devirtualization is sound only when the target is invariant across
    // every spec that reaches the callsite. Collect targets per callsite; a
    // callsite with conflicting targets is left as the `__protocol__` stub for
    // `rewrite_closed_union_protocol_dispatch` to turn into a runtime
    // type-switch cascade, which is correct for any receiver.
    let mut target_by_callsite: HashMap<CallsiteId, Option<FnId>> = HashMap::new();
    for spec in module_plan.specs.values() {
        for (callsite, edge) in &spec.call_edges {
            if callsite.slot != EmitSlot::Direct {
                continue;
            }
            if let CallEdgeTarget::Local(target) = &edge.target {
                target_by_callsite
                    .entry(callsite.clone())
                    .and_modify(|agreed| {
                        if *agreed != Some(target.fn_id) {
                            *agreed = None;
                        }
                    })
                    .or_insert(Some(target.fn_id));
            }
        }
    }
    let mut changed = false;
    for (callsite, agreed) in &target_by_callsite {
        if let Some(fn_id) = agreed {
            changed |= rewrite_external_callsite_for_link(module, callsite, *fn_id);
        }
    }
    changed
}

pub(crate) fn compile_repl_expr_with_types<T>(
    t: &mut T,
    prog: Program,
    expr: Spanned<Expr>,
    input_frame: Vec<String>,
    entry_name: String,
    sm: SourceMap,
    tel: &dyn Telemetry,
) -> Result<ReplEntryOk, FrontendErr>
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut compiler = Compiler::new();
    compile_repl_expr_with_compiler_types(compiler.world_mut(), t, prog, expr, input_frame, entry_name, sm, tel)
}

pub(crate) fn compile_repl_expr_with_compiler_types<T>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    mut prog: Program,
    expr: Spanned<Expr>,
    input_frame: Vec<String>,
    entry_name: String,
    sm: SourceMap,
    tel: &dyn Telemetry,
) -> Result<ReplEntryOk, FrontendErr>
where
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let output_frame = repl_output_frame_names(&input_frame, &expr);
    let entry_item = Rc::new(Item::Fn(repl_entry_fn_def(
        &entry_name,
        &input_frame,
        &output_frame,
        expr,
    )));
    prog.items.push(entry_item.clone());
    let frontend = compile_program_with_compiler_types(compiler, t, prog, sm, tel)?;
    if frontend.module.fn_by_name(&entry_name).is_none() {
        return Err(fail(
            frontend.sm,
            Diagnostic::error(
                codes::LOWER_UNSUPPORTED,
                format!("repl entry `{}` not lowered", entry_name),
                Span::DUMMY,
            ),
        ));
    }
    Ok(ReplEntryOk {
        frontend,
        input_frame,
        output_frame,
        entry_item,
    })
}

fn repl_entry_fn_def(entry_name: &str, input_frame: &[String], output_frame: &[String], expr: Spanned<Expr>) -> FnDef {
    let display_name = "__repl_display".to_string();
    let display_expr = Spanned::new(Expr::Var(display_name.clone()), expr.span);
    let bind_display = Spanned::new(
        Expr::Match(
            Spanned::new(Pattern::Var(display_name.clone()), expr.span),
            Box::new(expr),
        ),
        display_expr.span,
    );
    let mut returns = vec![display_expr];
    returns.extend(output_frame.iter().map(|name| Spanned::dummy(Expr::Var(name.clone()))));
    let body = Spanned::new(
        Expr::Block(vec![bind_display, Spanned::dummy(Expr::Tuple(returns))]),
        Span::DUMMY,
    );
    let params = input_frame
        .iter()
        .map(|name| Spanned::dummy(Pattern::Var(name.clone())))
        .collect::<Vec<_>>();
    FnDef {
        name: entry_name.to_string(),
        name_span: Span::DUMMY,
        clauses: vec![FnClause {
            param_annotations: vec![None; params.len()],
            params,
            guard: None,
            body,
            span: Span::DUMMY,
        }],
        is_macro: false,
        is_private: false,
        variadic: false,
        extern_abi: None,
        extern_params: vec![],
        extern_ret_tokens: TypeExprBody(vec![]),
        attrs: vec![],
        span: Span::DUMMY,
    }
}

#[cfg(test)]
mod frontend_test;
