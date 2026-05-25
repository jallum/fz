use super::*;
use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnClause, FnDef, Item,
    MatchClause, Pattern, Program, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, Const, Cont, ExternDecl, ExternId, ExternTy, FnBuilder,
    FnId, Module, ModuleBuilder, Prim, SourceInfo, Term, UnOp, Var,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;


// -----------------------------------------------------------------------------
// fz-duq.1: branching-construct join helpers
// -----------------------------------------------------------------------------
//
// `if`/`case`/`cond`/`with` need to join multiple arm bodies at a single
// "rest of surrounding code" point. The pre-fz-duq design used a join
// *block* inside the current fn — fragile because a non-tail Call in any
// arm body triggers `cps_split_call`, which finalizes the current fn,
// stranding the join block in a built-and-immutable FnIr.
//
// The fix mirrors what `cps_split_call` already does for non-tail Calls:
// each branching construct uses *continuation fns* as joins. Each arm is
// itself a continuation fn so that arm-internal CPS-splits stay confined
// to their own arm's lineage and never finalize the construct's outer
// fn prematurely.
//
// The three helpers below are used by `lower_if`/`lower_case`/`lower_cond`/
// `lower_with`:
//
//   * `mint_cont_fn`           — allocate a FnId + record visible locals.
//   * `switch_to_cont_fn`      — finalize current fn, switch to the cont's
//                                builder, rebind env to cap params.
//   * `finalize_arm`           — at arm's end, emit the right terminator
//                                (Return for tail position, TailCall to
//                                the join fn for non-tail position, or
//                                nothing if the arm self-terminated).
//
// Post-inline, these collapse: a one-call-site cont fn whose body is just
// `Return(param)` gets inlined back by `inline_tail_calls_once`, so the
// final CLIF for a non-CPS-splitting arm is the same as today's block-join
// shape (often tighter — see fz-duq.2 acceptance).

/// Handle to a freshly minted continuation fn (per-arm body or post-construct
/// join). The fn's builder is not yet created; the caller switches into it
/// via `switch_to_cont_fn` when ready to lower its body.
#[derive(Debug, Clone)]
pub(super) struct ContFn {
    id: FnId,
    name: String,
    /// Names + outer-fn Vars of locals captured at the time the fn was
    /// minted. These names become the cont fn's entry params (after the
    /// extras). The Vars are the *outer-fn* Vars (used by callers when
    /// constructing the TailCall args into this fn).
    outer_captured: Vec<(String, Var)>,
    span: Span,
    /// fz-f88.5 — origin tag baked in at mint time.
    category: crate::fz_ir::FnCategory,
}

/// Mint a fresh continuation FnId, snapshot the outer env at this point,
/// and record the span for diagnostics. The builder is created lazily by
/// `switch_to_cont_fn`.
pub(super) fn mint_cont_fn(
    ctx: &mut LowerCtx,
    name: impl Into<String>,
    span: Span,
    category: crate::fz_ir::FnCategory,
) -> ContFn {
    let id = ctx.mb.fresh_fn_id();
    ctx.fn_spans.insert(id, span);
    ContFn {
        id,
        name: name.into(),
        outer_captured: ctx.visible_locals(),
        span,
        category,
    }
}

/// Finalize ctx.cur (adding it to the module) and switch into a fresh
/// builder for `cont`. Allocates an entry block with params:
/// `[extras..., captured...]`. Returns the Vars for the extras (for a
/// per-arm fn there are 0 extras; for a join fn the single extra is the
/// joined value the arms passed in). The env is rebound from
/// `cont.outer_captured`'s names to the fresh captured-param Vars in the
/// new fn.
pub(super) fn switch_to_cont_fn(ctx: &mut LowerCtx, cont: &ContFn, extra_param_count: usize) -> Vec<Var> {
    // Finalize current fn.
    let done = ctx
        .cur
        .take()
        .expect("switch_to_cont_fn: no current fn")
        .build();
    ctx.mb.add_fn(done);

    // Build new fn.
    let mut kbuilder = FnBuilder::new(cont.id, cont.name.clone()).with_category(cont.category);

    // Entry params: extras (e.g. join_param) first, then captured renames.
    let extras: Vec<Var> = (0..extra_param_count)
        .map(|_| kbuilder.fresh_var())
        .collect();
    let cap_params: Vec<Var> = cont
        .outer_captured
        .iter()
        .map(|_| kbuilder.fresh_var())
        .collect();
    let mut entry_params = extras.clone();
    entry_params.extend(cap_params.clone());
    let entry = kbuilder.block(entry_params);

    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont.id);
    ctx.cur_block = Some(entry);
    ctx.terminated = false;

    // Var meta for extras + captured renames so diagnostics can attribute
    // them to the construct's span.
    for v in &extras {
        ctx.var_meta
            .insert((cont.id, *v), (cont.span, String::new()));
    }
    for v in &cap_params {
        ctx.var_meta
            .insert((cont.id, *v), (cont.span, String::new()));
    }

    // Rebind env: clear, then map each captured name to its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _outer_v), nv) in cont.outer_captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }

    extras
}

/// At the end of an arm's body, emit the appropriate terminator.
///
/// - If the arm self-terminated (Return / Halt / inner TailCall),
///   `ctx.terminated` is already true: emit nothing.
/// - If `join` is `Some`, emit `TailCall(join.id, [arm_value, ...captured])`.
///   Captured Vars are re-resolved from `ctx.env` at *this* moment because
///   ctx.cur may have changed (via internal CPS-splits) since the arm
///   started — the captured names point to the current fn's Vars now.
/// - If `join` is `None` (tail position), emit `Return(arm_value)`.
///
/// Sets `ctx.terminated = true` after emission.
pub(super) fn finalize_arm(ctx: &mut LowerCtx, arm_value: Var, join: Option<&ContFn>) {
    if ctx.terminated {
        return;
    }
    if let Some(join) = join {
        let mut tail_args = Vec::with_capacity(1 + join.outer_captured.len());
        tail_args.push(arm_value);
        for (name, _outer_v) in &join.outer_captured {
            let v = ctx.env.get(name).copied().unwrap_or_else(|| {
                panic!(
                    "finalize_arm: captured name `{}` not in env at arm-end",
                    name
                )
            });
            tail_args.push(v);
        }
        ctx.set_term(Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee: join.id,
            args: tail_args,
            is_back_edge: false,
        });
    } else {
        ctx.set_term(Term::Return(arm_value));
    }
    ctx.terminated = true;
}
pub(super) fn cps_split_call_closure(
    ctx: &mut LowerCtx,
    closure_var: Var,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    ctx.set_term_at(
        Term::CallClosure {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            closure: closure_var,
            args: arg_vars,
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    // Result-slot Var inherits the call's span (it's the value the call returns).
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}

/// fz-ul4.19.3: lower a source-level `receive()` into Term::Receive,
/// mirroring cps_split_call's continuation-building. The continuation
/// receives one arg (the message) plus captured Vars.
///
/// For tail position (the source `receive()` is the last expression in a
/// fn), the cont synthesizes `Return(msg)` so the message becomes the
/// fn's return value. Otherwise the cont becomes a normal continuation
/// that's resumed with the message bound to a Var.
pub(super) fn cps_split_receive(
    ctx: &mut LowerCtx,
    call_span: Span,
    is_tail: bool,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    // Terminate current block with Term::Receive.
    ctx.set_term_at(
        Term::Receive {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    // Finalize current fn.
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    // Build the continuation fn. Same shape as cps_split_call's cont:
    // entry params = [result_param, captured...].
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_receive_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    // Rebind env: each captured name -> its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    if is_tail {
        // Tail receive: synthesize `Return(msg)` immediately. The cont
        // fn IS the post-receive fn for the parent; in tail position we
        // just return the message.
        ctx.set_term_at(Term::Return(result_param), call_span);
        ctx.terminated = true;
    }
    Ok(result_param)
}
pub(super) fn cps_split_call(
    ctx: &mut LowerCtx,
    callee: FnId,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    // Terminate current block with the call.
    ctx.set_term_at(
        Term::Call {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee,
            args: arg_vars,
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );

    // Finalize current fn.
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    // Start the continuation fn.
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0))
        .with_category(crate::fz_ir::FnCategory::CpsCont);
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    ctx.var_meta
        .insert((cont_id, result_param), (call_span, String::new()));
    ctx.cur_block = Some(entry);

    // Rebind env: each captured name -> its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}
