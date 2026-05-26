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
pub(crate) struct ModuleTypeStats {
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

pub(crate) fn module_type_stats(m: &Module, mt: &ModulePlan) -> ModuleTypeStats {
    let mut stats = ModuleTypeStats::default();
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

/// fz-fyq.2 — for every `Term::If` in a registered-spec fn, decide whether
/// the planner can prove one branch unreachable under cross-spec consensus.
/// A branch is published as `Dead` only when every spec of the enclosing
/// fn agreed the scrutinee narrows to `none` on that side; the rule
/// matches `collect_diagnostics` (fz-pky.1) which is what made the
/// `unreachable-arm` warning sound. Consumers: `ir_branch_fold`
/// (fz-fyq.4) and the unreachable-arm diagnostic (fz-fyq.3).
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
                // Fallback: when cond's own type is a singleton truthy/
                // falsy value, the opposite branch is unreachable even if
                // narrow_for_cond didn't fire (e.g. cond bound directly
                // to a `Const::True`/`Const::False`/`Const::Nil`). This
                // subsumes the cond-singleton fold ir_fold used to do.
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

/// fz-pky.1 — build the unreachable-arm diagnostic from per-spec
/// dead-var records. We join old_t across specs so the type-note
/// reflects every specialization that contributed; new_t is similarly
/// joined for the narrow-note (in practice, when ALL specs found a
/// branch dead, each spec's new_t is `none` — joined, still `none`).
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

/// .11.24.6: scan planner output for unreachable If branches. For each
/// `Term::If(cond, then_b, else_b)`, re-run the branch narrowing under the
/// terminator's pre-env. If either branch's narrowed operand is empty, that
/// branch is unreachable.
///
/// Returns diagnostics in a stable order (sorted by fn position then block id).
/// Each diagnostic carries the offending block's terminator span (when
/// recorded by ir_lower in `Module.source.term_span`); .20.8 will enrich
/// the message with the set-theoretic type vocabulary.
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
    use crate::diag::codes::TYPE_DEAD_BINOP;
    use crate::diag::{Diagnostic, Diagnostics, Span};

    let mut out = Diagnostics::new();

    // fz-pky.1 — per-spec unreachable-arm. A branch is source-level
    // unreachable iff EVERY registered spec of the enclosing fn agrees
    // it's dead. A branch dead in some specs but live in others (e.g.
    // sum's `[]` arm under the narrow `[list(int_set)]` spec, but live
    // under the recursive `[nil | list(int_set)]` spec) is reachable
    // source-side and must NOT warn.
    //
    // Algorithm: for each (FnId, Term::If, branch), count specs where
    // dead vs total specs of the fn. Emit when dead-count equals total.
    //
    // Group specs by FnId.
    let mut specs_by_fn: HashMap<crate::fz_ir::FnId, Vec<Vec<crate::types::KeySlot>>> =
        HashMap::new();
    for key in types.specs.keys() {
        if !key.demand.is_value() {
            continue;
        }
        specs_by_fn
            .entry(key.fn_id)
            .or_default()
            .push(key.input.clone());
    }

    // For diagnostic purposes only: fns with no registered spec
    // (no IR caller, not closure-reachable, not entry-seeded) still
    // contain code the user wrote. Type them under their any-key
    // ad-hoc and run diagnostics against that. This doesn't pollute
    // module_plan.specs — codegen never sees these specs because
    // codegen only compiles reachable fns.
    let mut adhoc_specs: HashMap<crate::fz_ir::FnId, SpecPlan> = HashMap::new();
    for f in &module.fns {
        if specs_by_fn.contains_key(&f.id) {
            continue;
        }
        let n_params = f.block(f.entry).params.len();
        let any_key_ty = {
            let any = t.any();
            t.repeat(any, n_params)
        };
        let ft = type_fn(t, f, module, Some(&any_key_ty));
        adhoc_specs.insert(f.id, ft);
        specs_by_fn
            .entry(f.id)
            .or_default()
            .push(spec_key_for_fn(f, any_key_ty).input);
    }

    let mut fns_sorted: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_sorted.sort_by_key(|f| f.id.0);
    for f in fns_sorted {
        let Some(keys) = specs_by_fn.get(&f.id) else {
            continue;
        };
        let total_specs = keys.len();
        if total_specs == 0 {
            continue;
        }

        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let Term::If {
                cond,
                then_b,
                else_b,
                origin,
            } = b.terminator
            else {
                continue;
            };

            // fz-fyq.3 — only warn on user-authored Ifs. Synthesized
            // dispatch (pattern-bind, fn-clause selection, param guards)
            // is scaffolding the programmer didn't write; the planner can
            // prove some of its branches dead, but that's a property of
            // the lowering, not a bug in the source.
            if !matches!(origin, crate::fz_ir::BranchOrigin::User) {
                continue;
            }

            let term_span = module
                .source
                .term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);

            // For each spec, narrow this If and record whether each
            // branch is dead (and which Var made it dead, for the
            // diagnostic note).
            let mut dead_then: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            let mut dead_else: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            for key in keys {
                let ft = types
                    .specs
                    .get(&SpecKey::value(f.id, key.clone()))
                    .or_else(|| adhoc_specs.get(&f.id))
                    .unwrap();
                let mut env: HashMap<Var, crate::types::Ty> =
                    ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
                    env.insert(*v, pt_ty);
                }
                let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
                if let Some(d) = find_emptied_var(t, &env, &then_env) {
                    dead_then.push(d);
                }
                if let Some(d) = find_emptied_var(t, &env, &else_env) {
                    dead_else.push(d);
                }
            }

            // Emit only when EVERY spec found the branch dead.
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

    // VR.5a (fz-ul4.27.4): flag kind-disjoint equality / inequality. We walk
    // each Let stmt, rebuild the env up to that stmt, and report a
    // type/dead-binop diagnostic when `intersect(t_a, t_b)` is empty. The
    // codegen-side fold (Eq -> FALSE, Neq -> TRUE) is unaffected by the
    // diagnostic; the user just gets a warning that the comparison can never
    // hold.
    for f in module.fns.iter() {
        // Pick any registered spec, or fall back to ad-hoc any-key
        // (same rule as the unreachable-arm scan above).
        let ft_owned: Option<SpecPlan>;
        let ft: &SpecPlan = match types.any_spec_for(f.id) {
            Some(ft) => ft,
            None => {
                let n_params = f.block(f.entry).params.len();
                let any_key = {
                    let any = t.any();
                    t.repeat(any, n_params)
                };
                ft_owned = Some(type_fn(t, f, module, Some(&any_key)));
                ft_owned.as_ref().unwrap()
            }
        };
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let mut env: HashMap<Var, crate::types::Ty> =
                ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            let spans = module.source.stmt_spans.get(&(f.id, b.id));
            for (sidx, stmt) in b.stmts.iter().enumerate() {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::BinOp(op, lhs, rhs) = prim
                    && matches!(op, BinOp::Eq | BinOp::Neq)
                {
                    // Lint only on cross-kind disjointness (int vs atom,
                    // float vs nil, etc.). Within a single axis, two
                    // disjoint literal sets (e.g. `1 == 2`) still fold to
                    // false at codegen but are not surprising to the
                    // reader, so we keep them silent.
                    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
                    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
                    let cross_kind = !t.is_empty(&ta_ty)
                        && !t.is_empty(&tb_ty)
                        && !t.kinds_overlap(&ta_ty, &tb_ty);
                    if cross_kind {
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
                        let d = Diagnostic::warning(TYPE_DEAD_BINOP, message, span)
                            .with_label(format!("in fn `{}`", f.name))
                            .with_note(note);
                        out.push(d);
                    }
                }
                // fz-l4c — arithmetic on opaque-typed operands is a
                // soundness leak. `pid`, `ref`, and user opaque aliases
                // happen to share bit-tag space with `int`, so `self() + 1`
                // computes a number today; reject it at type-check time.
                // Comparisons (`==`, `!=`) remain permitted — pid/ref
                // equality is load-bearing for the selective-receive
                // matcher.
                if let Prim::BinOp(op, lhs, rhs) = prim
                    && matches!(
                        op,
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
                    )
                {
                    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
                    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
                    let lhs_opaque = t.opaque_singleton(&ta_ty);
                    let rhs_opaque = t.opaque_singleton(&tb_ty);
                    if lhs_opaque.is_some() || rhs_opaque.is_some() {
                        let span = spans
                            .and_then(|s| s.get(sidx).copied())
                            .unwrap_or(Span::DUMMY);
                        let opname = match op {
                            BinOp::Add => "+",
                            BinOp::Sub => "-",
                            BinOp::Mul => "*",
                            BinOp::Div => "/",
                            BinOp::Mod => "%",
                            _ => unreachable!(),
                        };
                        let (which, tag) = match (&lhs_opaque, &rhs_opaque) {
                            (Some(name), _) => ("left", name.as_str()),
                            (_, Some(name)) => ("right", name.as_str()),
                            _ => unreachable!(),
                        };
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
                        let d = Diagnostic::error(
                            crate::diag::codes::TYPE_OPAQUE_ARITHMETIC,
                            message,
                            span,
                        )
                        .with_label(format!("in fn `{}`", f.name))
                        .with_note(note);
                        out.push(d);
                    }
                }
                // fz-swt.8 — `handle.value` outside the declaring
                // module is a type error. Detect at MapGet sites where
                // the subject is a singleton opaque, the key is the
                // atom `:value`, the opaque has a recorded inner type
                // (i.e. was declared via `@type t :: opaque T`), and
                // the enclosing fn's module isn't the declaring module.
                if let Prim::MapGet(map_v, key_v) = prim {
                    let mt_ty = env.get(map_v).cloned().unwrap_or_else(|| t.none());
                    let opaque_tag = t.opaque_singleton(&mt_ty);
                    if let (Some(tag), Some(MapKey::Atom(key))) = (
                        opaque_tag.as_ref(),
                        var_as_map_key(t, *key_v, &env).as_ref(),
                    ) && key == "value"
                        && module.opaque_inners.contains_key(tag.as_str())
                        && let Err(err) = t.check_opaque_visibility(&mt_ty, fn_module_of(&f.name))
                    {
                        let span = spans
                            .and_then(|s| s.get(sidx).copied())
                            .unwrap_or(Span::DUMMY);
                        let d = Diagnostic::error(
                            crate::diag::codes::TYPE_OPAQUE_VISIBILITY,
                            format!("{}", err),
                            span,
                        )
                        .with_label(format!("in fn `{}`", f.name));
                        out.push(d);
                    }
                }
                let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
                env.insert(*v, pt_ty);
            }
        }
    }

    // fz-yxs — pure-codegen invariant for receive matchers and guards.
    // Walk every Term::ReceiveMatched; for each clause's guard FnId, walk
    // every block in the guard fn body and reject any impure Prim or
    // impure terminator (Call / Receive / Halt). The matcher itself is
    // backend-materialised from the pattern AST in B3, so there is nothing
    // to check at the IR level for patterns today; the pattern AST
    // grammar already forbids fn calls inside patterns, so the second
    // acceptance bullet ("planner rejects impure pattern") is vacuously
    // satisfied at parse/lowering.
    for f in &module.fns {
        for b in &f.blocks {
            let Term::ReceiveMatched { clauses, .. } = &b.terminator else {
                continue;
            };
            for c in clauses {
                let Some(g_fid) = c.guard else { continue };
                let g_fn = module.fn_by_id(g_fid);
                let guard_span = c.span;
                let mut impure: Option<String> = None;
                for gb in &g_fn.blocks {
                    if let Err(e) = check_pure_codegen(&gb.stmts) {
                        impure = Some(match e {
                            ImpureError::Stmt { kind, .. } => match kind {
                                ImpureKind::Allocates(what) => {
                                    format!("guard expression allocates via `{}`", what)
                                }
                                ImpureKind::Extern => "guard expression calls an extern".into(),
                            },
                            ImpureError::Term(_) => unreachable!(),
                        });
                        break;
                    }
                    if let Err(e) = check_pure_term(&gb.terminator) {
                        impure = Some(match e {
                            ImpureError::Term(ImpureTerm::Call) => {
                                "guard expression invokes a function (calls are not allowed)".into()
                            }
                            ImpureError::Term(ImpureTerm::Receive) => {
                                "guard expression contains a `receive` (not allowed)".into()
                            }
                            ImpureError::Term(ImpureTerm::Halt) => {
                                "guard expression halts (not allowed)".into()
                            }
                            ImpureError::Stmt { .. } => unreachable!(),
                        });
                        break;
                    }
                }
                if let Some(reason) = impure {
                    let d = Diagnostic::error(
                        crate::diag::codes::TYPE_IMPURE_RECEIVE_GUARD,
                        reason,
                        guard_span,
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

    // fz-puj.30 (G1) — purity check for every FnCategory::Matcher fn.
    for d in check_matcher_purity(module) {
        out.push(d);
    }

    out
}

/// fz-puj.30 (G1) — verify every FnCategory::Matcher fn stays pure.
///
/// Matcher fns own matcher dispatch for case / multi-clause / with-else
/// (and ExternMatcher will join when receive migrates to a real IR fn).
/// Stmts must obey the pure-codegen subset (no alloc, no extern).
/// Terminators are laxer than for receive guards:
/// TailCall / Goto / If / Halt / Return are all allowed (TailCall is
/// the matcher's primary leaf dispatch); Call / CallClosure /
/// TailCallClosure / Receive / ReceiveMatched are forbidden because
/// they introduce side effects or allocate continuations.
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

/// fz-swt.8 — module path of a qualified fn name. The IR-side
/// `FnIr.name` is dotted (`"Mod.fname"` or `"A.B.fname"`); the planner's
/// opaque-visibility gate compares against the `"Mod"` prefix of the
/// alias's qualified tag (which uses `::` to separate the module from
/// the alias). Top-level fns return the empty string, matching the
/// owner-module convention for top-level / runtime-prelude opaques.
pub(crate) fn fn_module_of(fn_name: &str) -> &str {
    match fn_name.rfind('.') {
        Some(i) => &fn_name[..i],
        None => "",
    }
}

// True iff `a` and `b` have at least one axis on which both are
// non-empty. Used by the VR.5a `type/dead-binop` lint to distinguish
// "different kinds" (worth surfacing) from "same kind, narrowed to
// disjoint literals" (silent fold).
