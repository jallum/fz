use super::*;
use crate::ast::MatchClause;
use crate::diag::Span;
use crate::fz_ir::{Term, Var};

/// fz-puj.36 (H7) — build a degenerate (N=1) PatternMatrix from receive clauses.
///
/// The PatternMatrix subject is a single Var representing the candidate message.
/// Each clause produces one Row with `patterns: vec![clause.pattern]`,
/// `preconditions: []`, `guard: clause.guard`, and a caller-supplied
/// `body_id`. Captures/pinned threading is unchanged from receive's
/// existing wiring — those are not PatternMatrix concerns.
///
/// The PatternMatrix itself accepts arbitrary patterns; lowering turns it into a
/// cached AST-free Matcher before any receive probe executes.
pub(crate) fn build_receive_pattern_matrix(
    msg_var: Var,
    clauses: &[crate::ast::MatchClause],
) -> crate::pattern_matrix::PatternMatrix {
    crate::pattern_matrix::PatternMatrix {
        subjects: vec![msg_var],
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| crate::pattern_matrix::Row {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: c.guard.clone(),
                body_id: i as crate::pattern_matrix::BodyId,
            })
            .collect(),
    }
}

pub(crate) fn lower_receive(
    ctx: &mut LowerCtx,
    clauses: &[MatchClause],
    after: Option<&crate::ast::AfterClause>,
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
        Some(a) => Some(lower_expr(ctx, &a.timeout, false)?),
        None => None,
    };

    // Resolve `^name` references against the (possibly post-CPS-split)
    // outer scope. Dedupe by name; preserve first-seen order so backends
    // see a stable layout.
    let mut seen_pinned: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut pinned: Vec<(String, Var)> = Vec::new();
    for clause in clauses {
        let mut names: Vec<String> = Vec::new();
        collect_pattern_pinned_names(&clause.pattern.node, &mut names);
        if let Some(guard) = &clause.guard {
            let mut bound = std::collections::BTreeSet::new();
            let mut bound_names = Vec::new();
            collect_pattern_bound_names(&clause.pattern.node, &mut bound_names);
            for name in bound_names {
                bound.insert(name);
            }
            crate::pattern_matrix::collect_guard_capture_names(&guard.node, &bound, &mut names);
        }
        for name in names {
            if !seen_pinned.insert(name.clone()) {
                continue;
            }
            let v = ctx
                .env
                .get(&name)
                .copied()
                .ok_or_else(|| LowerError::Unbound {
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
        Some(mint_cont_fn(
            ctx,
            "receive_join",
            rx_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
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
            crate::fz_ir::FnCategory::ControlFlowCont,
        );
        let guard = if clause.guard.is_some() {
            Some(mint_cont_fn(
                ctx,
                format!("rx_clause_{}_guard", i),
                clause.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
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

    let after_slot: Option<(ContFn, &crate::ast::AfterClause)> = after.map(|a| {
        let body = mint_cont_fn(
            ctx,
            "rx_after_body",
            a.span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        );
        (body, a)
    });

    // Captures: outer-scope vars threaded into every body/guard/after fn.
    // Snapshot once here; every mint_cont_fn above took the same snapshot
    // (env hasn't changed between mints), so the body fns' capture-param
    // shapes match this list.
    let captures_snap = ctx.visible_locals();
    let captures_vars: Vec<Var> = captures_snap.iter().map(|(_, v)| *v).collect();

    // Build the IR clauses now that we have all the FnIds.
    let ir_clauses: Vec<crate::fz_ir::ReceiveClause> = clauses
        .iter()
        .zip(clause_slots.iter())
        .map(|(c, slot)| crate::fz_ir::ReceiveClause {
            bound_names: slot.bound_names.clone(),
            guard: slot.guard.as_ref().map(|g| g.id),
            body: slot.body.id,
            span: c.span,
        })
        .collect();

    let ir_after = after_slot
        .as_ref()
        .map(|(cont, a)| crate::fz_ir::ReceiveAfter {
            timeout: timeout_var.expect("timeout lowered when after is Some"),
            body: cont.id,
            span: a.span,
        });
    let receive_pattern_matrix = build_receive_pattern_matrix(crate::fz_ir::Var(0), clauses);
    let mut guard_stack = Vec::new();
    let mut guard_resolver =
        |name: &str, arity: usize, args: Vec<crate::exec::matcher::GuardExpr>| {
            lower_guard_helper_call_to_dispatch(ctx, name, arity, args, &mut guard_stack)
        };
    let receive_matcher = crate::pattern_matrix::compile_pattern_matrix_with_guard_resolver(
        receive_pattern_matrix,
        &mut guard_resolver,
    )
    .map_err(|err| LowerError::Unsupported {
        span: rx_span,
        what: format!("receive matcher cannot be lowered: {:?}", err),
    })
    .map(std::sync::Arc::new)?;
    for (index, key) in receive_matcher.prepared_keys.iter().enumerate() {
        let name = crate::exec::matcher::prepared_key_name(index);
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = materialize_prepared_matcher_key(ctx, key)?;
        pinned.push((name, v));
    }
    let mut matcher_pinned = Vec::new();
    collect_matcher_pinned_names_recursive(&receive_matcher, &mut matcher_pinned);
    for name in matcher_pinned {
        if !seen_pinned.insert(name.clone()) {
            continue;
        }
        let v = ctx
            .env
            .get(&name)
            .copied()
            .ok_or_else(|| LowerError::Unbound {
                span: rx_span,
                name: format!("^{}", name),
            })?;
        pinned.push((name, v));
    }

    // Terminate the caller fn's current block with the ReceiveMatched.
    ctx.set_term_at(
        Term::ReceiveMatched {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            clauses: ir_clauses,
            matcher: receive_matcher,
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
    let clauses_iter = clauses.iter().zip(clause_slots);
    for (clause, slot) in clauses_iter {
        if let Some(g_cont) = &slot.guard {
            let extras = switch_to_cont_fn(ctx, g_cont, slot.bound_names.len());
            for (name, &v) in slot.bound_names.iter().zip(extras.iter()) {
                ctx.bind(name, v);
            }
            let g_val = lower_expr(
                ctx,
                clause
                    .guard
                    .as_ref()
                    .expect("guard cont implies guard expr"),
                /* is_tail */ true,
            )?;
            // Guards return their value to the matcher caller (B3 will
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
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some((cont, a)) = after_slot {
        let _extras = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &a.body, /* is_tail */ true)?;
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
