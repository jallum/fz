use super::*;
use crate::compiler::source::Span;
use crate::fz_ir::{
    CallsiteIdent, Cont, ContinuationProvenance, ContinuationProvenanceKind, FnBuilder, FnCategory, FnId, Term, Var,
};
use crate::modules::identity::Mfa;

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
// These continuation fns are the lowering-time correctness shape. Later
// phases may choose tighter planned bodies, but lowering must leave a coherent
// CPS module without relying on a cleanup pass to repair it.

/// Handle to a freshly minted continuation fn (per-arm body or post-construct
/// join). The fn's builder is not yet created; the caller switches into it
/// via `switch_to_cont_fn` when ready to lower its body.
#[derive(Debug, Clone)]
pub(crate) struct ContFn {
    pub(super) id: FnId,
    pub(super) name: String,
    /// Names + outer-fn Vars of locals captured at the time the fn was
    /// minted. These names become the cont fn's entry params (after the
    /// extras). The Vars are the *outer-fn* Vars (used by callers when
    /// constructing the TailCall args into this fn).
    pub(super) outer_captured: Vec<(String, Var)>,
    pub(super) span: Span,
    /// fz-f88.5 — origin tag baked in at mint time.
    pub(super) category: FnCategory,
    pub(super) owner_module: String,
    pub(super) owned_cons_captures: Vec<OwnedConsCapture>,
}

#[derive(Debug, Clone)]
pub(crate) struct OwnedConsCapture {
    pub(super) head_name: String,
    pub(super) source_cons: Var,
}

/// Mint a fresh continuation FnId, snapshot the outer env at this point,
/// and record the span for diagnostics. The builder is created lazily by
/// `switch_to_cont_fn`.
pub(crate) fn mint_cont_fn(ctx: &mut LowerCtx, name: impl Into<String>, span: Span, category: FnCategory) -> ContFn {
    let id = ctx.mb.fresh_fn_id();
    ctx.fn_spans.insert(id, span);
    let outer_captured = ctx.visible_locals();
    let owned_cons_captures = owned_cons_captures_for_visible_locals(ctx, &outer_captured);
    ContFn {
        id,
        name: name.into(),
        outer_captured,
        span,
        category,
        owner_module: ctx.current_owner_module.clone(),
        owned_cons_captures,
    }
}

fn owned_cons_captures_for_visible_locals(ctx: &LowerCtx, visible: &[(String, Var)]) -> Vec<OwnedConsCapture> {
    let Some(cur) = ctx.cur.as_ref() else {
        return Vec::new();
    };
    visible
        .iter()
        .filter_map(|(name, head)| {
            cur.owned_cons_reuse_source_for_head(*head)
                .map(|source_cons| OwnedConsCapture {
                    head_name: name.clone(),
                    source_cons,
                })
        })
        .collect()
}

fn capture_call_args(captured: &[(String, Var)], owned_cons: &[OwnedConsCapture]) -> Vec<Var> {
    let mut args: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    args.extend(owned_cons.iter().map(|capture| capture.source_cons));
    args
}

pub(crate) fn cont_call_args(ctx: &LowerCtx, cont: &ContFn) -> Vec<Var> {
    let captured = cont
        .outer_captured
        .iter()
        .map(|(name, original)| (name.clone(), ctx.lookup(name).unwrap_or(*original)))
        .collect::<Vec<_>>();
    capture_call_args(&captured, &cont.owned_cons_captures)
}

struct CaptureParams {
    semantic: Vec<Var>,
    hidden_owned_cons: Vec<Var>,
}

fn capture_params_for(
    builder: &mut FnBuilder,
    captured: &[(String, Var)],
    owned_cons: &[OwnedConsCapture],
) -> CaptureParams {
    CaptureParams {
        semantic: captured.iter().map(|_| builder.fresh_var()).collect(),
        hidden_owned_cons: owned_cons.iter().map(|_| builder.fresh_var()).collect(),
    }
}

fn push_capture_entry_params(entry_params: &mut Vec<Var>, params: &CaptureParams) {
    entry_params.extend(params.semantic.clone());
    entry_params.extend(params.hidden_owned_cons.clone());
}

fn install_capture_metadata(
    builder: &mut FnBuilder,
    captured: &[(String, Var)],
    owned_cons: &[OwnedConsCapture],
    params: &CaptureParams,
) {
    for (capture, source_param) in owned_cons.iter().zip(&params.hidden_owned_cons) {
        if let Some((_, head_param)) = captured
            .iter()
            .zip(&params.semantic)
            .find(|((name, _), _)| name == &capture.head_name)
        {
            builder.record_owned_cons_reuse_capability(*head_param, *source_param);
        }
    }
}

fn add_capture_var_meta(ctx: &mut LowerCtx, fn_id: FnId, span: Span, params: &CaptureParams) {
    for v in params.semantic.iter().chain(&params.hidden_owned_cons) {
        ctx.var_meta.insert((fn_id, *v), (span, String::new()));
    }
}

fn rebind_captured_env(ctx: &mut LowerCtx, captured: &[(String, Var)], params: &CaptureParams) {
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&params.semantic) {
        ctx.bind(name, *nv);
    }
}

fn start_cps_cont_fn(
    ctx: &mut LowerCtx,
    cont_id: FnId,
    name: String,
    call_span: Span,
    captured: Vec<(String, Var)>,
    owned_cons: Vec<OwnedConsCapture>,
) -> Var {
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    let mut kbuilder = FnBuilder::new(cont_id, name)
        .with_category(FnCategory::CpsCont)
        .with_owner_module(ctx.current_owner_module.clone());
    let result_param = kbuilder.fresh_var();
    let capture_params = capture_params_for(&mut kbuilder, &captured, &owned_cons);
    let mut entry_params = vec![result_param];
    push_capture_entry_params(&mut entry_params, &capture_params);
    let entry = kbuilder.block(entry_params);
    install_capture_metadata(&mut kbuilder, &captured, &owned_cons, &capture_params);

    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.fn_spans.insert(cont_id, call_span);
    ctx.var_meta.insert((cont_id, result_param), (call_span, String::new()));
    add_capture_var_meta(ctx, cont_id, call_span, &capture_params);
    ctx.cur_block = Some(entry);
    rebind_captured_env(ctx, &captured, &capture_params);
    result_param
}

/// Finalize ctx.cur (adding it to the module) and switch into a fresh
/// builder for `cont`. Allocates an entry block with params:
/// `[extras..., captured...]`. Returns the Vars for the extras (for a
/// per-arm fn there are 0 extras; for a join fn the single extra is the
/// joined value the arms passed in). The env is rebound from
/// `cont.outer_captured`'s names to the fresh captured-param Vars in the
/// new fn.
pub(crate) fn switch_to_cont_fn(ctx: &mut LowerCtx, cont: &ContFn, extra_param_count: usize) -> Vec<Var> {
    // Finalize current fn.
    let done = ctx.cur.take().expect("switch_to_cont_fn: no current fn").build();
    ctx.mb.add_fn(done);

    // Build new fn.
    let mut kbuilder = FnBuilder::new(cont.id, cont.name.clone())
        .with_category(cont.category)
        .with_owner_module(cont.owner_module.clone());

    // Entry params: extras (e.g. join_param) first, then captured renames.
    let extras: Vec<Var> = (0..extra_param_count).map(|_| kbuilder.fresh_var()).collect();
    let capture_params = capture_params_for(&mut kbuilder, &cont.outer_captured, &cont.owned_cons_captures);
    let mut entry_params = extras.clone();
    push_capture_entry_params(&mut entry_params, &capture_params);
    let entry = kbuilder.block(entry_params);
    install_capture_metadata(
        &mut kbuilder,
        &cont.outer_captured,
        &cont.owned_cons_captures,
        &capture_params,
    );

    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont.id);
    ctx.cur_block = Some(entry);
    ctx.terminated = false;

    // Var meta for extras + captured renames so diagnostics can attribute
    // them to the construct's span.
    for v in &extras {
        ctx.var_meta.insert((cont.id, *v), (cont.span, String::new()));
    }
    add_capture_var_meta(ctx, cont.id, cont.span, &capture_params);

    // Rebind env: clear, then map each captured name to its new param Var.
    rebind_captured_env(ctx, &cont.outer_captured, &capture_params);

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
pub(crate) fn finalize_arm(ctx: &mut LowerCtx, arm_value: Var, join: Option<&ContFn>) {
    if ctx.terminated {
        return;
    }
    if let Some(join) = join {
        let mut tail_args = Vec::with_capacity(1 + join.outer_captured.len() + join.owned_cons_captures.len());
        tail_args.push(arm_value);
        let captured: Vec<(String, Var)> = join
            .outer_captured
            .iter()
            .map(|(name, _outer_v)| {
                let v = ctx
                    .env
                    .get(name)
                    .copied()
                    .unwrap_or_else(|| panic!("finalize_arm: captured name `{}` not in env at arm-end", name));
                (name.clone(), v)
            })
            .collect();
        tail_args.extend(capture_call_args(&captured, &join.owned_cons_captures));
        ctx.set_term(Term::TailCall {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee: join.id,
            args: tail_args,
            is_back_edge: false,
        });
    } else {
        ctx.set_term(Term::Return(arm_value));
    }
    ctx.terminated = true;
}
pub(crate) fn cps_split_call_closure(
    ctx: &mut LowerCtx,
    closure_var: Var,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let owned_cons_captures = owned_cons_captures_for_visible_locals(ctx, &captured);
    let captured_vars = capture_call_args(&captured, &owned_cons_captures);
    let cont_id = ctx.mb.fresh_fn_id();
    let caller = ctx.cur_fn_id.expect("cps_split_call_closure: missing current fn id");

    ctx.set_term_at(
        Term::CallClosure {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            closure: closure_var,
            args: arg_vars.clone(),
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );
    ctx.record_continuation_provenance(
        cont_id,
        ContinuationProvenance {
            caller,
            captured: captured.iter().map(|(_, var)| *var).collect(),
            capture_param_offset: 1,
            kind: ContinuationProvenanceKind::ClosureCall {
                closure: closure_var,
                args: arg_vars.clone(),
            },
        },
    );

    Ok(start_cps_cont_fn(
        ctx,
        cont_id,
        format!("k_{}", cont_id.0),
        call_span,
        captured,
        owned_cons_captures,
    ))
}

pub(crate) fn cps_split_call(
    ctx: &mut LowerCtx,
    callee: FnId,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let owned_cons_captures = owned_cons_captures_for_visible_locals(ctx, &captured);
    let captured_vars = capture_call_args(&captured, &owned_cons_captures);
    let cont_id = ctx.mb.fresh_fn_id();
    let caller = ctx.cur_fn_id.expect("cps_split_call: missing current fn id");

    // Terminate current block with the call.
    ctx.set_term_at(
        Term::Call {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee,
            args: arg_vars.clone(),
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
    );
    ctx.record_continuation_provenance(
        cont_id,
        ContinuationProvenance {
            caller,
            captured: captured.iter().map(|(_, var)| *var).collect(),
            capture_param_offset: 1,
            kind: ContinuationProvenanceKind::DirectCall {
                callee,
                args: arg_vars.clone(),
            },
        },
    );

    Ok(start_cps_cont_fn(
        ctx,
        cont_id,
        format!("k_{}", cont_id.0),
        call_span,
        captured,
        owned_cons_captures,
    ))
}

pub(crate) fn cps_split_external_call(
    ctx: &mut LowerCtx,
    callee: FnId,
    target: Mfa,
    arg_vars: Vec<Var>,
    call_span: Span,
) -> Result<Var, LowerError> {
    let captured = ctx.visible_locals();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    ctx.set_external_direct_term_at(
        Term::Call {
            ident: CallsiteIdent::from_source(call_span),
            callee,
            args: arg_vars,
            continuation: Cont {
                fn_id: cont_id,
                captured: captured_vars.clone(),
            },
        },
        call_span,
        target,
    );

    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0))
        .with_category(FnCategory::CpsCont)
        .with_owner_module(ctx.current_owner_module.clone());
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_fn_id = Some(cont_id);
    ctx.cur_block = Some(entry);
    ctx.terminated = false;
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}
