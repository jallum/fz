use super::expr_types::var_as_map_key;
use super::fn_types::{ModulePlan, SpecKey, SpecPlan, spec_key_for_fn};
use super::narrow::{find_emptied_var, narrow_for_if};
use super::prim::type_prim;
use super::purity::{ImpureError, ImpureKind, ImpureTerm, check_pure_codegen, check_pure_term};
use super::type_fn::type_fn;
use crate::fz_ir::{BinOp, FnId, Module, Prim, Stmt, Term, Var};
use crate::types::MapKey;
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub(crate) struct ModulePlanStats {
    pub(crate) matcher_spec_count: usize,
    pub(crate) spec_var_count: usize,
    pub(crate) spec_block_count: usize,
    pub(crate) spec_stmt_count: usize,
    pub(crate) dispatch_count: usize,
    pub(crate) direct_call_count: usize,
    pub(crate) tail_call_count: usize,
    pub(crate) if_count: usize,
    pub(crate) receive_count: usize,
    pub(crate) receive_matched_count: usize,
}

pub(crate) fn module_plan_stats(m: &Module, mt: &ModulePlan) -> ModulePlanStats {
    let mut stats = ModulePlanStats::default();
    for (key, ft) in &mt.specs {
        if !key.demand.is_value() {
            continue;
        }
        let f = m.fn_by_id(key.fn_id);
        if matches!(f.category, crate::fz_ir::FnCategory::Matcher) {
            stats.matcher_spec_count += 1;
        }
        stats.spec_var_count += ft.vars.len();
        stats.dispatch_count += ft.dispatches.len();
        for block in &f.blocks {
            if !ft.reachable_blocks.contains(&block.id) {
                continue;
            }
            stats.spec_block_count += 1;
            stats.spec_stmt_count += block.stmts.len();
            match &block.terminator {
                Term::Call { .. } => stats.direct_call_count += 1,
                Term::TailCall { .. } => stats.tail_call_count += 1,
                Term::If { .. } => stats.if_count += 1,
                Term::Receive { .. } => stats.receive_count += 1,
                Term::ReceiveMatched { .. } => stats.receive_matched_count += 1,
                Term::Goto(..)
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_) => {}
            }
        }
    }
    stats
}

/// For every `Term::If` in a registered-spec fn, publish a dead branch only
/// when every value-demand spec for the enclosing fn proves the same side
/// unreachable.
pub(crate) fn compute_dead_branches<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
) -> HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch> {
    let mut specs_by_fn: HashMap<FnId, Vec<Vec<crate::types::KeySlot>>> = HashMap::new();
    for key in mt.specs.keys() {
        if !key.demand.is_value() {
            continue;
        }
        specs_by_fn
            .entry(key.fn_id)
            .or_default()
            .push(key.input.clone());
    }

    let mut out: HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch> = HashMap::new();

    for f in &m.fns {
        let Some(keys) = specs_by_fn.get(&f.id) else {
            continue;
        };
        let total = keys.len();
        if total == 0 {
            continue;
        }
        for b in &f.blocks {
            let Term::If { cond, .. } = b.terminator else {
                continue;
            };
            let mut dead_then = 0usize;
            let mut dead_else = 0usize;
            for key in keys {
                let Some(ft) = mt.specs.get(&SpecKey::value(f.id, key.clone())) else {
                    continue;
                };
                let mut env: HashMap<Var, crate::types::Ty> =
                    ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let pt_ty = type_prim(t, prim, &env, m, &HashSet::new());
                    env.insert(*v, pt_ty);
                }
                let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
                let mut then_dead = find_emptied_var(t, &env, &then_env).is_some();
                let mut else_dead = find_emptied_var(t, &env, &else_env).is_some();
                // Fallback: when cond's own type is a singleton truthy/falsy
                // value, the opposite branch is unreachable even if
                // `narrow_for_if` found no predicate-specific narrowing.
                let ct = env.get(&cond).cloned().unwrap_or_else(|| t.any());
                let true_ty = t.atom_lit("true");
                let false_ty = t.atom_lit("false");
                let nil_ty = t.nil();
                if t.is_subtype(&ct, &true_ty) {
                    else_dead = true;
                } else if t.is_subtype(&ct, &false_ty) || t.is_subtype(&ct, &nil_ty) {
                    then_dead = true;
                }
                if then_dead {
                    dead_then += 1;
                }
                if else_dead {
                    dead_else += 1;
                }
            }
            // Both-dead means the If itself is unreachable — leave to DCE.
            if dead_then == total && dead_else < total {
                out.insert((f.id, b.id), crate::fz_ir::DeadBranch::Then);
            } else if dead_else == total && dead_then < total {
                out.insert((f.id, b.id), crate::fz_ir::DeadBranch::Else);
            }
        }
    }
    out
}

/// Build the unreachable-arm diagnostic from per-spec dead-var records. The
/// label uses the lowest-id emptied var, and the type note joins that var's
/// pre-narrowing types across contributing specs.
fn emit_unreachable<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &mut T,
    module: &Module,
    fn_name: &str,
    term_span: crate::diag::Span,
    tag: &str,
    bb_id: crate::fz_ir::BlockId,
    dead_records: &[(crate::fz_ir::Var, T::Ty, T::Ty)],
) -> crate::diag::Diagnostic {
    use crate::diag::{Diagnostic, codes::TYPE_UNREACHABLE_ARM};
    // Pick the lowest-id Var across all records for label attribution
    // (stable, matches old single-spec behavior when only one spec).
    let pick = dead_records.iter().min_by_key(|(v, _, _)| v.0).unwrap();
    let (v, _, _) = pick;
    // Join the offending Var's pre-narrow types across every spec that
    // dropped this branch — that's the source-level view of the value.
    let mut joined_old = t.none();
    for (vv, ot, _) in dead_records {
        if *vv == *v {
            joined_old = t.union(joined_old, ot.clone());
        }
    }
    let var_name = module.source.var_name_of(*v);
    let label_subject = match var_name {
        Some(n) => format!("`{}`", n),
        None => "this value".to_string(),
    };
    let var_span = module.source.var_span_of(*v);

    let message = format!("the {} branch is never reachable", tag);
    let type_note = format!(
        "{} here has type `{}`",
        label_subject,
        t.display_for_diag(&joined_old),
    );
    let narrow_note = format!(
        "narrowing for this branch would need `none`, but that intersection \
         is uninhabited (unreachable arm at bb{})",
        bb_id.0,
    );

    let mut d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, message, term_span)
        .with_label(format!("in fn `{}`", fn_name))
        .with_note(type_note)
        .with_note(narrow_note);
    if !var_span.is_dummy() && var_span != term_span {
        d = d.with_secondary(var_span, format!("{} bound here", label_subject));
    }
    d
}

/// Collect planner diagnostics in stable source order.
pub fn collect_diagnostics<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    types: &ModulePlan,
) -> crate::diag::Diagnostics {
    use crate::diag::Diagnostics;
    let mut out = Diagnostics::new();
    collect_unreachable_arm_diagnostics(t, module, types, &mut out);
    collect_stmt_type_diagnostics(t, module, types, &mut out);
    collect_receive_guard_diagnostics(module, &mut out);
    for d in check_matcher_purity(module) {
        out.push(d);
    }
    out
}

fn collect_unreachable_arm_diagnostics<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    module: &Module,
    types: &ModulePlan,
    out: &mut crate::diag::Diagnostics,
) {
    use crate::diag::Span;
    let mut specs_by_fn = value_specs_by_fn(types);
    let adhoc_specs = add_adhoc_specs_for_unregistered_fns(t, module, &mut specs_by_fn);
    for f in sorted_fns(module) {
        let Some(keys) = specs_by_fn.get(&f.id) else {
            continue;
        };
        let total_specs = keys.len();
        if total_specs == 0 {
            continue;
        }

        for b in sorted_blocks(f) {
            let Term::If {
                cond,
                then_b,
                else_b,
                origin,
            } = b.terminator
            else {
                continue;
            };

            // Only warn on user-authored Ifs. Synthesized dispatch
            // (pattern-bind, fn-clause selection, param guards) is lowering
            // scaffolding, not a source-level bug.
            if !matches!(origin, crate::fz_ir::BranchOrigin::User) {
                continue;
            }
            let term_span = module
                .source
                .term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);
            let mut dead_then: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            let mut dead_else: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            for key in keys {
                let ft = spec_for_diag(types, &adhoc_specs, f.id, key);
                let env = env_after_block_stmts(t, module, ft, b);
                let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
                if let Some(d) = find_emptied_var(t, &env, &then_env) {
                    dead_then.push(d);
                }
                if let Some(d) = find_emptied_var(t, &env, &else_env) {
                    dead_else.push(d);
                }
            }
            if dead_then.len() == total_specs {
                out.push(emit_unreachable(
                    t, module, &f.name, term_span, "then", then_b, &dead_then,
                ));
            }
            if dead_else.len() == total_specs {
                out.push(emit_unreachable(
                    t, module, &f.name, term_span, "else", else_b, &dead_else,
                ));
            }
        }
    }
}

fn collect_stmt_type_diagnostics<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    types: &ModulePlan,
    out: &mut crate::diag::Diagnostics,
) {
    for f in module.fns.iter() {
        let ft_owned = fallback_any_spec(t, module, types, f);
        let ft = ft_owned.as_ref().unwrap_or_else(|| {
            types
                .any_spec_for(f.id)
                .expect("fallback exists when no registered spec exists")
        });
        for b in sorted_blocks(f) {
            let mut env: HashMap<Var, crate::types::Ty> =
                ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            let spans = module.source.stmt_spans.get(&(f.id, b.id));
            for (sidx, stmt) in b.stmts.iter().enumerate() {
                let Stmt::Let(v, prim) = stmt;
                collect_dead_binop_diagnostic(t, &f.name, spans, sidx, prim, &env, out);
                collect_opaque_arithmetic_diagnostic(t, &f.name, spans, sidx, prim, &env, out);
                collect_opaque_visibility_diagnostic(
                    t, module, &f.name, spans, sidx, prim, &env, out,
                );
                let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
                env.insert(*v, pt_ty);
            }
        }
    }
}

fn collect_receive_guard_diagnostics(module: &Module, out: &mut crate::diag::Diagnostics) {
    use crate::diag::Diagnostic;
    for f in &module.fns {
        for b in &f.blocks {
            let Term::ReceiveMatched { clauses, .. } = &b.terminator else {
                continue;
            };
            for c in clauses {
                let Some(g_fid) = c.guard else { continue };
                if let Some(reason) = receive_guard_impurity(module.fn_by_id(g_fid)) {
                    let d = Diagnostic::error(
                        crate::diag::codes::TYPE_IMPURE_RECEIVE_GUARD,
                        reason,
                        c.span,
                    )
                    .with_label(format!("in fn `{}`", f.name))
                    .with_note(
                        "guards in `receive` must stay in the pure-codegen subset: \
                         constants, comparisons, type tests, and accessors — \
                         no function calls or allocations",
                    );
                    out.push(d);
                }
            }
        }
    }
}

fn receive_guard_impurity(g_fn: &crate::fz_ir::FnIr) -> Option<String> {
    for gb in &g_fn.blocks {
        if let Err(e) = check_pure_codegen(&gb.stmts) {
            return Some(receive_guard_stmt_impurity(e));
        }
        if let Err(e) = check_pure_term(&gb.terminator) {
            return Some(receive_guard_term_impurity(e));
        }
    }
    None
}

fn receive_guard_stmt_impurity(e: ImpureError) -> String {
    match e {
        ImpureError::Stmt { kind, .. } => match kind {
            ImpureKind::Allocates(what) => format!("guard expression allocates via `{}`", what),
            ImpureKind::Extern => "guard expression calls an extern".into(),
        },
        ImpureError::Term(_) => unreachable!(),
    }
}

fn receive_guard_term_impurity(e: ImpureError) -> String {
    match e {
        ImpureError::Term(ImpureTerm::Call) => {
            "guard expression invokes a function (calls are not allowed)".into()
        }
        ImpureError::Term(ImpureTerm::Receive) => {
            "guard expression contains a `receive` (not allowed)".into()
        }
        ImpureError::Term(ImpureTerm::Halt) => "guard expression halts (not allowed)".into(),
        ImpureError::Stmt { .. } => unreachable!(),
    }
}

fn value_specs_by_fn(types: &ModulePlan) -> HashMap<FnId, Vec<Vec<crate::types::KeySlot>>> {
    let mut specs_by_fn: HashMap<FnId, Vec<Vec<crate::types::KeySlot>>> = HashMap::new();
    for key in types.specs.keys() {
        if key.demand.is_value() {
            specs_by_fn
                .entry(key.fn_id)
                .or_default()
                .push(key.input.clone());
        }
    }
    specs_by_fn
}

fn add_adhoc_specs_for_unregistered_fns<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    specs_by_fn: &mut HashMap<FnId, Vec<Vec<crate::types::KeySlot>>>,
) -> HashMap<FnId, SpecPlan> {
    let mut adhoc_specs = HashMap::new();
    for f in &module.fns {
        if specs_by_fn.contains_key(&f.id) {
            continue;
        }
        let any_key_ty = any_key_for_fn(t, f);
        let ft = type_fn(t, f, module, Some(&any_key_ty));
        adhoc_specs.insert(f.id, ft);
        specs_by_fn
            .entry(f.id)
            .or_default()
            .push(spec_key_for_fn(f, any_key_ty).input);
    }
    adhoc_specs
}

fn fallback_any_spec<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    module: &Module,
    types: &ModulePlan,
    f: &crate::fz_ir::FnIr,
) -> Option<SpecPlan> {
    if types.any_spec_for(f.id).is_some() {
        return None;
    }
    let any_key = any_key_for_fn(t, f);
    Some(type_fn(t, f, module, Some(&any_key)))
}

fn any_key_for_fn<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    f: &crate::fz_ir::FnIr,
) -> Vec<crate::types::Ty> {
    let n_params = f.block(f.entry).params.len();
    let any = t.any();
    t.repeat(any, n_params)
}

fn spec_for_diag<'a>(
    types: &'a ModulePlan,
    adhoc_specs: &'a HashMap<FnId, SpecPlan>,
    fn_id: FnId,
    key: &[crate::types::KeySlot],
) -> &'a SpecPlan {
    types
        .specs
        .get(&SpecKey::value(fn_id, key.to_vec()))
        .or_else(|| adhoc_specs.get(&fn_id))
        .expect("diagnostic spec key must have a registered or ad-hoc plan")
}

fn env_after_block_stmts<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    ft: &SpecPlan,
    b: &crate::fz_ir::Block,
) -> HashMap<Var, crate::types::Ty> {
    let mut env: HashMap<Var, crate::types::Ty> =
        ft.block_envs.get(&b.id).cloned().unwrap_or_default();
    for stmt in &b.stmts {
        let Stmt::Let(v, prim) = stmt;
        let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
        env.insert(*v, pt_ty);
    }
    env
}

fn sorted_fns(module: &Module) -> Vec<&crate::fz_ir::FnIr> {
    let mut fns: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns.sort_by_key(|f| f.id.0);
    fns
}

fn sorted_blocks(f: &crate::fz_ir::FnIr) -> Vec<&crate::fz_ir::Block> {
    let mut blocks: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
    blocks.sort_by_key(|b| b.id.0);
    blocks
}

fn collect_dead_binop_diagnostic<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
    t: &mut T,
    fn_name: &str,
    spans: Option<&Vec<crate::diag::Span>>,
    sidx: usize,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    out: &mut crate::diag::Diagnostics,
) {
    use crate::diag::{Diagnostic, Span, codes::TYPE_DEAD_BINOP};
    let Prim::BinOp(op, lhs, rhs) = prim else {
        return;
    };
    if !matches!(op, BinOp::Eq | BinOp::Neq) {
        return;
    }
    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
    let cross_kind = !t.is_empty(&ta_ty) && !t.is_empty(&tb_ty) && !t.kinds_overlap(&ta_ty, &tb_ty);
    if !cross_kind {
        return;
    }
    let span = spans
        .and_then(|s| s.get(sidx).copied())
        .unwrap_or(Span::DUMMY);
    let constant = if matches!(op, BinOp::Eq) {
        "false"
    } else {
        "true"
    };
    let opname = if matches!(op, BinOp::Eq) { "==" } else { "!=" };
    let message = format!(
        "`{}` is always {}: operand types do not overlap",
        opname, constant,
    );
    let note = format!(
        "left has type `{}`; right has type `{}`",
        t.display_for_diag(&ta_ty),
        t.display_for_diag(&tb_ty),
    );
    out.push(
        Diagnostic::warning(TYPE_DEAD_BINOP, message, span)
            .with_label(format!("in fn `{}`", fn_name))
            .with_note(note),
    );
}

fn collect_opaque_arithmetic_diagnostic<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
    t: &mut T,
    fn_name: &str,
    spans: Option<&Vec<crate::diag::Span>>,
    sidx: usize,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    out: &mut crate::diag::Diagnostics,
) {
    use crate::diag::{Diagnostic, Span};
    let Prim::BinOp(op, lhs, rhs) = prim else {
        return;
    };
    if !matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
    ) {
        return;
    }
    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
    let lhs_opaque = t.opaque_singleton(&ta_ty);
    let rhs_opaque = t.opaque_singleton(&tb_ty);
    let Some((which, tag)) = opaque_operand_label(&lhs_opaque, &rhs_opaque) else {
        return;
    };
    let span = spans
        .and_then(|s| s.get(sidx).copied())
        .unwrap_or(Span::DUMMY);
    let opname = arithmetic_op_name(*op);
    let message = format!(
        "arithmetic `{}` is not defined for opaque type `{}`",
        opname, tag
    );
    let note = format!(
        "{} operand has type `{}`; opaque types are nominally \
         disjoint from `int` and `float`. Use `==` / `!=` for \
         identity comparison.",
        which,
        t.display_for_diag(if which == "left" { &ta_ty } else { &tb_ty }),
    );
    out.push(
        Diagnostic::error(crate::diag::codes::TYPE_OPAQUE_ARITHMETIC, message, span)
            .with_label(format!("in fn `{}`", fn_name))
            .with_note(note),
    );
}

fn collect_opaque_visibility_diagnostic<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    fn_name: &str,
    spans: Option<&Vec<crate::diag::Span>>,
    sidx: usize,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    out: &mut crate::diag::Diagnostics,
) {
    use crate::diag::{Diagnostic, Span};
    let Prim::MapGet(map_v, key_v) = prim else {
        return;
    };
    let mt_ty = env.get(map_v).cloned().unwrap_or_else(|| t.none());
    let opaque_tag = t.opaque_singleton(&mt_ty);
    let key = var_as_map_key(t, *key_v, env);
    let (Some(tag), Some(MapKey::Atom(key))) = (opaque_tag.as_ref(), key.as_ref()) else {
        return;
    };
    if key != "value" || !module.opaque_inners.contains_key(tag.as_str()) {
        return;
    }
    let Err(err) = t.check_opaque_visibility(&mt_ty, fn_module_of(fn_name)) else {
        return;
    };
    let span = spans
        .and_then(|s| s.get(sidx).copied())
        .unwrap_or(Span::DUMMY);
    out.push(
        Diagnostic::error(
            crate::diag::codes::TYPE_OPAQUE_VISIBILITY,
            format!("{}", err),
            span,
        )
        .with_label(format!("in fn `{}`", fn_name)),
    );
}

fn opaque_operand_label<'a>(
    lhs_opaque: &'a Option<String>,
    rhs_opaque: &'a Option<String>,
) -> Option<(&'static str, &'a str)> {
    match (lhs_opaque, rhs_opaque) {
        (Some(name), _) => Some(("left", name.as_str())),
        (_, Some(name)) => Some(("right", name.as_str())),
        _ => None,
    }
}

fn arithmetic_op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        _ => unreachable!(),
    }
}

/// Verify every `FnCategory::Matcher` fn stays pure.
///
/// Matcher stmts must obey the pure-codegen subset. Terminators are laxer than
/// receive guards: TailCall / Goto / If / Halt / Return are allowed, while
/// Call / CallClosure / TailCallClosure / Receive / ReceiveMatched are
/// forbidden because they introduce side effects or allocate continuations.
pub fn check_matcher_purity(module: &Module) -> Vec<crate::diag::Diagnostic> {
    use crate::diag::{Diagnostic, Span};
    use crate::fz_ir::{FnCategory, Term};

    let mut out: Vec<Diagnostic> = Vec::new();
    for f in &module.fns {
        if f.category != FnCategory::Matcher {
            continue;
        }
        let mut reason: Option<String> = None;
        for blk in &f.blocks {
            if let Err(e) = check_pure_codegen(&blk.stmts) {
                reason = Some(match e {
                    ImpureError::Stmt {
                        kind: ImpureKind::Allocates(what),
                        ..
                    } => format!("matcher fn body allocates via `{}`", what),
                    ImpureError::Stmt {
                        kind: ImpureKind::Extern,
                        ..
                    } => "matcher fn body calls an extern".into(),
                    ImpureError::Term(_) => unreachable!(),
                });
                break;
            }
            match &blk.terminator {
                Term::Call { .. } | Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                    reason = Some("matcher fn body invokes a function via Call/CallClosure".into());
                    break;
                }
                Term::Receive { .. } | Term::ReceiveMatched { .. } => {
                    reason = Some("matcher fn body contains a `receive`".into());
                    break;
                }
                Term::Goto(..)
                | Term::If { .. }
                | Term::TailCall { .. }
                | Term::Halt(_)
                | Term::Return(_) => {}
            }
        }
        if let Some(msg) = reason {
            let d = Diagnostic::error(crate::diag::codes::TYPE_IMPURE_MATCHER, msg, Span::DUMMY)
                .with_label(format!("in matcher fn `{}`", f.name))
                .with_note(
                    "Matcher fns own matcher dispatch and must stay pure: no allocation, \
                     no extern, no Call / CallClosure / Receive. Side effects break the \
                     matcher's ability to be inlined back at trivial sites and the eli5 \
                     'matchers are pure routers' guarantee.",
                );
            out.push(d);
        }
    }
    out
}

/// Module path of a qualified fn name. The IR-side `FnIr.name` is dotted
/// (`"Mod.fname"` or `"A.B.fname"`); the planner's opaque-visibility gate
/// compares against the `"Mod"` prefix of the alias's qualified tag (which uses
/// `::` to separate the module from the alias). Top-level fns return the empty
/// string, matching the owner-module convention for top-level / runtime-prelude
/// opaques.
pub(crate) fn fn_module_of(fn_name: &str) -> &str {
    match fn_name.rfind('.') {
        Some(i) => &fn_name[..i],
        None => "",
    }
}
