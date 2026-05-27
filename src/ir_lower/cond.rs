use super::*;
use crate::ast::{Expr, FnDef, Spanned};
use crate::diag::Span;
use crate::fz_ir::{BlockId, Const, Prim, Term, Var};

use crate::pattern_matrix::{BodyId, PatternMatrix, Row};
pub(crate) fn lower_multi_clause<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    fn_def: &FnDef,
    param_vars: &[Var],
    entry: BlockId,
) -> Result<(), LowerError> {
    // fz-qbg.2 — per-clause body continuation fns, mirroring fz-duq's
    // if/case/cond/with shape. The try_blocks + fail_block cascade stays
    // intra-fn (pattern bind and guard tests can't CPS-split — they only
    // emit TypeTest / projection / If). After pattern bind succeeds, the
    // try_block TailCalls a per-clause body cont fn (`fn_clause_N`) with
    // the post-pattern env (outer + pattern bindings). The body lowers in
    // that cont fn so any internal CPS-split stays confined to that
    // clause's lineage; the source-level fn's outer FnIr is fully
    // populated (try cascade + arm TailCalls) before any body lowers.
    //
    // Why the planner cooperates now: fz-qbg.1 made the planner's call graph
    // structural rather than any-key-spec-gated. With that, outer ↔
    // fn_clause_N edges show up in the SCC, widening fires at the
    // per-SCC fixpoint, and the recursive callsite's broadened key
    // (e.g. `[int, int]` for `count`'s tail) lands in the spec set.

    // fz-puj.52.7 — internal dispatch lowers the Matcher inline
    // into the user fn again. The production matcher-fn shape made
    // dispatch visible as ordinary spec-producing fns, duplicating specs
    // for every key. Receive remains the ABI-driven matcher-fn case.
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    let fc = ctx.atoms.intern("function_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(fc)));
    ctx.set_term(Term::Halt(v));

    let matrix_entry = ctx.cur_mut().block(vec![]);
    ctx.cur_mut()
        .set_terminator(entry, Term::Goto(matrix_entry, vec![]));
    ctx.cur_block = Some(matrix_entry);
    ctx.terminated = false;

    let mut rows: Vec<Row> = Vec::with_capacity(fn_def.clauses.len());
    for (i, c) in fn_def.clauses.iter().enumerate() {
        let mut preconditions: Vec<(Var, crate::types::Ty)> = Vec::new();
        for (pv, tok_opt) in param_vars.iter().zip(&c.param_annotations) {
            if let Some(toks) = tok_opt
                && let Ok((ty, _)) =
                    crate::type_expr::parse_type_expr(t, &toks.0, &ctx.combined_type_env)
            {
                preconditions.push((*pv, ty));
            }
        }
        rows.push(Row {
            patterns: c.params.clone(),
            preconditions,
            bindings: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as BodyId,
        });
    }
    let pattern_matrix = PatternMatrix {
        subjects: param_vars.to_vec(),
        rows,
    };

    let mut clause_conts: Vec<Option<ContFn>> = (0..fn_def.clauses.len()).map(|_| None).collect();
    let prev_origin = ctx.branch_origin;
    ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
    {
        let fn_def_ref = fn_def;
        let param_vars_ref = param_vars;
        let clause_conts_ref = &mut clause_conts;
        let mut cb = |ctx: &mut LowerCtx,
                      body_id: BodyId,
                      bindings: Vec<(String, Var)>,
                      preconditions: Vec<(Var, crate::types::Ty)>,
                      guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                      fall_block: BlockId|
         -> Result<(), LowerError> {
            let i = body_id as usize;
            let clause = &fn_def_ref.clauses[i];
            ctx.env.clear();
            ctx.env_order.clear();
            for (pv, pat) in param_vars_ref.iter().zip(&clause.params) {
                bind_param_topname(ctx, *pv, pat);
            }
            for (name, var) in &bindings {
                ctx.bind(name, *var);
            }
            for (pv, ty) in &preconditions {
                let tt = ctx.let_(Prim::TypeTest(*pv, Box::new(ty.clone())));
                let pass_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(tt, pass_b, fall_block);
                ctx.cur_block = Some(pass_b);
                ctx.terminated = false;
            }
            if let Some(g) = &guard {
                let guard_var = lower_expr(ctx, g, false)?;
                let body_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(guard_var, body_b, fall_block);
                ctx.cur_block = Some(body_b);
                ctx.terminated = false;
            }
            let cont = match &clause_conts_ref[i] {
                Some(cont) => cont.clone(),
                None => {
                    let cont = mint_cont_fn(
                        ctx,
                        format!("fn_clause_{}", i),
                        clause.span,
                        crate::fz_ir::FnCategory::MultiClauseCont,
                    );
                    clause_conts_ref[i] = Some(cont.clone());
                    cont
                }
            };
            let capture_vars = cont_call_args(ctx, &cont);
            ctx.set_term(Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::from_source(clause.span),
                callee: cont.id,
                args: capture_vars,
                is_back_edge: false,
            });
            ctx.terminated = true;
            Ok(())
        };
        let result = lower_pattern_matrix_to_current_fn(ctx, pattern_matrix, fail_block, &mut cb);
        ctx.branch_origin = prev_origin;
        result?;
    }

    for (i, clause) in fn_def.clauses.iter().enumerate() {
        let Some(cont) = clause_conts[i].clone() else {
            continue;
        };
        let _ = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
            ctx.terminated = true;
        }
    }

    Ok(())
}
pub(crate) fn lower_if(
    ctx: &mut LowerCtx,
    cond: &Spanned<Expr>,
    then_e: &Spanned<Expr>,
    else_opt: &Option<Box<Spanned<Expr>>>,
    is_tail: bool,
    if_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.2 — Per-arm + (optional) join continuation fns, mirroring
    // the CPS-split protocol from `cps_split_call`. The old block-join
    // design corrupted control flow whenever an arm body contained a
    // non-tail Call (Bug 2) and clobbered self-terminated arms with a
    // Goto-to-join carrying the sentinel Var(0) (Bug 1).
    //
    // Shape (non-tail):
    //   outer fn   : ... ; Term::If(cv, then_b, else_b)
    //   outer.then_b: TailCall(then_fn, [...captures])
    //   outer.else_b: TailCall(else_fn, [...captures])
    //   then_fn     : lower(then_e, is_tail=true) ;
    //                 finalize → TailCall(join_fn, [v, ...captures])
    //   else_fn     : lower(else_e, is_tail=true) ;
    //                 finalize → TailCall(join_fn, [v, ...captures])
    //   join_fn     : becomes ctx.cur. param `join_param` carries the
    //                 if's value. Surrounding code continues here.
    //
    // Shape (tail):
    //   same as above, but no join_fn; arms finalize via Return(v).
    //   ctx.terminated = true on return; ctx.cur is else_fn (or its
    //   inner-CPS-split descendant) — surrounding lower_fn finalizes it.
    //
    // The inliner (`inline_tail_calls_once`) collapses the tiny per-arm
    // and join fns post-IR-build; for non-CPS-splitting arms the
    // final CLIF matches today's block-join shape (often tighter — no
    // join block at all).

    let cv = lower_expr(ctx, cond, false)?;

    let then_cont = mint_cont_fn(
        ctx,
        "if_then",
        if_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );
    let else_cont = mint_cont_fn(
        ctx,
        "if_else",
        if_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );
    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "if_join",
            if_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // Allocate arm blocks in the outer (current) fn.
    let then_b = ctx.cur_mut().block(vec![]);
    let else_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(cv, then_b, else_b);

    // Wire each arm block: TailCall its arm fn with the outer captures.
    // Captures are snapshotted from the outer env *now*; they're the
    // same set we passed to `mint_cont_fn` for then_cont/else_cont/join_opt
    // (which all snapshot identical envs at this moment).
    let captures = ctx.visible_locals();
    let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();

    ctx.cur_block = Some(then_b);
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: then_cont.id,
        args: capture_vars.clone(),
        is_back_edge: false,
    });
    ctx.cur_block = Some(else_b);
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: else_cont.id,
        args: capture_vars,
        is_back_edge: false,
    });

    // Move to then_fn. Finalizes the outer fn (which is now fully populated).
    let _ = switch_to_cont_fn(ctx, &then_cont, 0);
    let tv = lower_expr(ctx, then_e, /* is_tail */ true)?;
    finalize_arm(ctx, tv, join_opt.as_ref());

    // Move to else_fn. Finalizes then_fn (or its CPS-split descendant).
    let _ = switch_to_cont_fn(ctx, &else_cont, 0);
    let ev = if let Some(else_e) = else_opt {
        lower_expr(ctx, else_e, /* is_tail */ true)?
    } else {
        ctx.let_(Prim::Const(Const::Nil))
    };
    finalize_arm(ctx, ev, join_opt.as_ref());

    if let Some(join) = &join_opt {
        // Non-tail: finalize else_fn, switch into join_fn. Surrounding
        // code continues lowering into join_fn with `join_param` as the
        // if's value.
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        // Tail position: both arms finalized via Return. ctx.cur is
        // else_fn (or a downstream CPS-split cont). Caller will finalize
        // it via `ctx.cur.take().build()`.
        ctx.terminated = true;
        Ok(Var(0))
    }
}
