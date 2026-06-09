use super::*;
use crate::ast::{AfterClause, MatchClause};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::{PatternBodyId, PatternRow, SourcePatternRows, collect_guard_capture_names};
use crate::dispatch_matrix::pattern::{
    PatternGuardExpr, pattern_dispatch_from_source_with_guard_resolver, prepared_key_name,
};
use crate::fz_ir::{CallsiteIdent, FnCategory, ReceiveAfter, ReceiveClause, Term, Var};
use crate::runtime_type_test_shim;
use crate::types::{Ty, Types};
use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

/// fz-puj.36 (H7) — build a degenerate (N=1) SourcePatternRows from receive clauses.
///
/// The SourcePatternRows input set is the single candidate message column.
/// Each clause produces one PatternRow with `patterns: vec![clause.pattern]`,
/// `preconditions: []`, `guard: clause.guard`, and a caller-supplied
/// `body_id`. Captures/pinned threading is unchanged from receive's
/// existing wiring — those are not SourcePatternRows concerns.
///
/// The SourcePatternRows itself accepts arbitrary patterns; lowering routes it
/// through DispatchMatrix and caches the graph-derived AST-free dispatch plan
/// before any receive probe executes.
pub(crate) fn build_receive_pattern_rows(clauses: &[MatchClause]) -> SourcePatternRows {
    SourcePatternRows {
        input_count: 1,
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| PatternRow {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                guard: c.guard.clone(),
                body_id: i as PatternBodyId,
            })
            .collect(),
    }
}

pub(crate) fn lower_receive<T: Types<Ty = Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    clauses: &[MatchClause],
    after: Option<&AfterClause>,
    is_tail: bool,
    rx_span: Span,
) -> Result<Var, LowerError> {
    if clauses.is_empty() && after.is_none() {
        return Err(LowerError::Unsupported {
            span: rx_span,
            what: "receive with no clauses and no after".into(),
        });
    }

    // After's timeout is lowered into the caller fn first because a
    // non-tail Call inside the timeout expression CPS-splits the current
    // fn — every Var snapshot that follows must come from the post-split
    // env so they belong to the right fn.
    let timeout_var = match after {
        Some(a) => Some(lower_expr(ctx, t, &a.timeout, false)?),
        None => None,
    };

    // Resolve `^name` references against the (possibly post-CPS-split)
    // outer scope. Dedupe by name; preserve first-seen order so backends
    // see a stable layout.
    let mut seen_pinned: HashSet<String> = HashSet::new();
    let mut pinned: Vec<(String, Var)> = Vec::new();
    for clause in clauses {
        let mut names: Vec<String> = Vec::new();
        collect_pattern_pinned_names(&clause.pattern.node, &mut names);
        if let Some(guard) = &clause.guard {
            let mut bound = BTreeSet::new();
            let mut bound_names = Vec::new();
            collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
            for name in bound_names {
                bound.insert(name);
            }
            collect_guard_capture_names(&guard.node, &bound, &mut names);
        }
        for name in names {
            if !seen_pinned.insert(name.clone()) {
                continue;
            }
            let v = ctx.env.get(&name).copied().ok_or_else(|| LowerError::Unbound {
                span: clause.pattern.span,
                name: format!("^{}", name),
            })?;
            pinned.push((name, v));
        }
    }

    // Join cont (post-receive code resumes here); skipped in tail position.
    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(ctx, "receive_join", rx_span, FnCategory::ControlFlowCont))
    };

    // Mint per-clause body / guard fns, and the after body fn.
    struct ClauseSlots {
        bound_names: Vec<String>,
        body: ContFn,
        guard: Option<ContFn>,
    }
    let mut clause_slots: Vec<ClauseSlots> = Vec::with_capacity(clauses.len());
    for (i, clause) in clauses.iter().enumerate() {
        let mut bound_names: Vec<String> = Vec::new();
        collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
        let body = mint_cont_fn(
            ctx,
            format!("rx_clause_{}_body", i),
            clause.span,
            FnCategory::ControlFlowCont,
        );
        let guard = if clause.guard.is_some() {
            Some(mint_cont_fn(
                ctx,
                format!("rx_clause_{}_guard", i),
                clause.span,
                FnCategory::ControlFlowCont,
            ))
        } else {
            None
        };
        clause_slots.push(ClauseSlots {
            bound_names,
            body,
            guard,
        });
    }

    let after_slot: Option<(ContFn, &AfterClause)> = after.map(|a| {
        let body = mint_cont_fn(ctx, "rx_after_body", a.span, FnCategory::ControlFlowCont);
        (body, a)
    });

    // Captures: outer-scope vars threaded into every body/guard/after fn.
    // Snapshot once here; every mint_cont_fn above took the same snapshot
    // (env hasn't changed between mints), so the body fns' capture-param
    // shapes match this list.
    let captures_snap = ctx.visible_locals();
    let captures_vars: Vec<Var> = captures_snap.iter().map(|(_, v)| *v).collect();

    // Build the IR clauses now that we have all the FnIds.
    let ir_clauses: Vec<ReceiveClause> = clauses
        .iter()
        .zip(clause_slots.iter())
        .map(|(c, slot)| ReceiveClause {
            ident: CallsiteIdent::from_source(c.span),
            bound_names: slot.bound_names.clone(),
            guard: slot.guard.as_ref().map(|g| g.id),
            body: slot.body.id,
            span: c.span,
        })
        .collect();

    let ir_after = after_slot.as_ref().map(|(cont, a)| ReceiveAfter {
        ident: CallsiteIdent::from_source(a.span),
        timeout: timeout_var.expect("timeout lowered when after is Some"),
        body: cont.id,
        span: a.span,
    });
    let receive_source_patterns = build_receive_pattern_rows(clauses);
    let mut guard_stack = Vec::new();
    let mut guard_resolver = |name: &str, arity: usize, args: Vec<PatternGuardExpr>| {
        lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
    };
    let receive_dispatch =
        pattern_dispatch_from_source_with_guard_resolver(receive_source_patterns, &mut guard_resolver)
            .map_err(|err| LowerError::Unsupported {
                span: rx_span,
                what: format!("receive dispatch cannot be lowered: {:?}", err),
            })
            .map(|plan| plan.map_type_handle(&mut runtime_type_test_shim::from_legacy_ty))
            .map(Arc::new)?;
    for (index, key) in receive_dispatch.prepared_keys.iter().enumerate() {
        let name = prepared_key_name(index);
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = materialize_prepared_dispatch_key(ctx, key)?;
        pinned.push((name, v));
    }
    let mut dispatch_pinned = Vec::new();
    collect_dispatch_pinned_names_recursive(&receive_dispatch, &mut dispatch_pinned);
    for name in dispatch_pinned {
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = ctx.env.get(&name).copied().ok_or_else(|| LowerError::Unbound {
            span: rx_span,
            name: format!("^{}", name),
        })?;
        pinned.push((name, v));
    }

    // Terminate the caller fn's current block with the ReceiveMatched.
    ctx.set_term_at(
        Term::ReceiveMatched {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            clauses: ir_clauses,
            dispatch: receive_dispatch,
            after: ir_after,
            pinned,
            captures: captures_vars,
        },
        rx_span,
    );

    // Lower each clause body (and any guard) into its own fn. `switch_to_
    // cont_fn` finalises the previously-current fn and switches into the
    // newly-named one; calling it in sequence chains the build-finalise
    // pattern through every body fn.
    let arm_is_tail = join_opt.is_none();
    let clauses_iter = clauses.iter().zip(clause_slots);
    for (clause, slot) in clauses_iter {
        if let Some(g_cont) = &slot.guard {
            let extras = switch_to_cont_fn(ctx, g_cont, slot.bound_names.len());
            for (name, &v) in slot.bound_names.iter().zip(extras.iter()) {
                ctx.bind(name, v);
            }
            let g_val = lower_expr(
                ctx,
                t,
                clause.guard.as_ref().expect("guard cont implies guard expr"),
                /* is_tail */ true,
            )?;
            // Guards return their value to the dispatch caller (B3 will
            // synthesise the dispatch). Use Term::Return so the value
            // appears as the guard fn's result.
            if !ctx.terminated {
                ctx.set_term_at(Term::Return(g_val), clause.span);
                ctx.terminated = true;
            }
        }

        let extras = switch_to_cont_fn(ctx, &slot.body, slot.bound_names.len());
        for (name, &v) in slot.bound_names.iter().zip(extras.iter()) {
            ctx.bind(name, v);
        }
        let result = lower_expr(ctx, t, &clause.body, arm_is_tail)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some((cont, a)) = after_slot {
        let _extras = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, t, &a.body, arm_is_tail)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}
