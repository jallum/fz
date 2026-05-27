use super::fn_types::{
    ModulePlan, ReturnContextPlanKey, SpecKey, display_return_context_plan, display_return_demand,
};
use super::reachable::cont_input_key;
use crate::fz_ir::{Block, CallsiteId, CallsiteIdent, EmitSlot, FnId, Module, Term};

// ----------------------------------------------------------------------
// fz-73m — pretty-printer for ModulePlan (golden spec dump).
// ----------------------------------------------------------------------

/// Deterministic text dump of `ModulePlan`. One stanza per (FnId, key)
/// spec; specs are sorted by FnId, then by lexicographic display-string of
/// the key so the output is stable across runs and HashMap iteration
/// orders.
///
/// Format is intended for golden-file diffing — every line is a comment
/// (`;` prefix) so the file reads like an annotated CLIF dump. Consumers
/// should treat the output as opaque text; the goal is that a human can
/// eyeball "are the inferred types what I expect for this fixture?"
/// without running codegen.
pub fn pretty_module_plan<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
) -> String {
    let any_ty = t.any();
    let mut out = String::new();
    for spec_key in sorted_spec_keys(t, mt) {
        render_spec(t, m, mt, spec_key, &any_ty, &mut out);
    }
    out
}

fn sorted_spec_keys<'a, T>(t: &T, mt: &'a ModulePlan) -> Vec<&'a SpecKey>
where
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
{
    let mut keys: Vec<&SpecKey> = mt.specs.keys().collect();
    keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| {
                crate::types::display_key_slots(t, &a.input)
                    .cmp(&crate::types::display_key_slots(t, &b.input))
            })
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    keys
}

fn render_spec<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    any_ty: &crate::types::Ty,
    out: &mut String,
) {
    let ft = &mt.specs[spec_key];
    let f = m.fn_by_id(spec_key.fn_id);
    render_spec_header(t, m, mt, spec_key, any_ty, out);
    render_fn_constants(m, ft, out);
    render_vars(t, ft, out);
    render_exits(t, m, mt, spec_key, ft, f, any_ty, out);
    out.push('\n');
}

fn render_spec_header<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    any_ty: &crate::types::Ty,
    out: &mut String,
) {
    let f = m.fn_by_id(spec_key.fn_id);
    let arity = f.block(f.entry).params.len();
    out.push_str(&format!(
        "; spec {}({}) #fn={}\n",
        f.name, arity, spec_key.fn_id.0
    ));
    out.push_str(&format!(
        ";   key:    {}\n",
        crate::types::display_key_slots(t, &spec_key.input)
    ));
    out.push_str(&format!(
        ";   demand: {}\n",
        super::fn_types::display_return_demand(t, &spec_key.demand)
    ));
    let ret = mt.effective_returns.get(spec_key);
    out.push_str(&format!(
        ";   return: {}\n",
        ret.map(|ty| t.display(ty))
            .unwrap_or_else(|| t.display(any_ty))
    ));
}

fn render_fn_constants(m: &Module, ft: &super::fn_types::SpecPlan, out: &mut String) {
    if ft.fn_constants.is_empty() {
        return;
    }
    let mut fcs: Vec<(&crate::fz_ir::Var, &FnId)> = ft.fn_constants.iter().collect();
    fcs.sort_by_key(|(v, _)| v.0);
    out.push_str(";   fn_constants:\n");
    for (v, fc) in fcs {
        out.push_str(&format!(
            ";     Var({}) = {}#{}\n",
            v.0,
            fn_name(m, *fc),
            fc.0
        ));
    }
}

fn render_vars<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &T,
    ft: &super::fn_types::SpecPlan,
    out: &mut String,
) {
    let mut vars: Vec<(&crate::fz_ir::Var, &crate::types::Ty)> = ft.vars.iter().collect();
    vars.sort_by_key(|(v, _)| v.0);
    out.push_str(";   vars:\n");
    for (v, ty) in vars {
        out.push_str(&format!(";     Var({}) :: {}\n", v.0, t.display(ty)));
    }
}

fn render_exits<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    f: &crate::fz_ir::FnIr,
    any_ty: &crate::types::Ty,
    out: &mut String,
) {
    let mut blocks: Vec<&Block> = f.blocks.iter().collect();
    blocks.sort_by_key(|b| b.id.0);
    out.push_str(";   exits:\n");
    for b in blocks {
        render_terminator_exit(t, m, mt, spec_key, ft, b, any_ty, out);
    }
}

fn render_terminator_exit<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    any_ty: &crate::types::Ty,
    out: &mut String,
) {
    let bid = b.id.0;
    match &b.terminator {
        Term::Return(v) => {
            let d = ft.vars.get(v).unwrap_or(any_ty);
            out.push_str(&format!(
                ";     blk{} Return Var({})    :: {}\n",
                bid,
                v.0,
                t.display(d)
            ));
        }
        Term::Halt(v) => {
            let d = ft.vars.get(v).unwrap_or(any_ty);
            out.push_str(&format!(
                ";     blk{} Halt Var({})      :: {}\n",
                bid,
                v.0,
                t.display(d)
            ));
        }
        Term::TailCall {
            callee,
            args,
            ident,
            ..
        } => {
            render_tail_call_exit(t, m, spec_key, ft, b, any_ty, *callee, args, ident, out);
        }
        Term::Call {
            ident,
            callee,
            args,
            continuation,
        } => {
            render_call_exit(
                t,
                m,
                mt,
                spec_key,
                ft,
                b,
                any_ty,
                *callee,
                args,
                ident,
                continuation,
                out,
            );
        }
        Term::CallClosure {
            closure,
            args,
            continuation,
            ..
        } => {
            render_call_closure_exit(t, m, mt, ft, b, *closure, args, continuation, out);
        }
        Term::TailCallClosure { closure, args, .. } => {
            render_tail_call_closure_exit(m, ft, b, *closure, args, out);
        }
        Term::Receive { continuation, .. } => {
            render_receive_exit(t, m, mt, ft, b, continuation, out);
        }
        Term::ReceiveMatched {
            clauses,
            after,
            pinned,
            captures,
            ..
        } => {
            render_receive_matched_exit(m, b, clauses, after, pinned, captures, out);
        }
        Term::Goto(target, args) => {
            let arg_vars = vars_str(args);
            out.push_str(&format!(
                ";     blk{} Goto blk{}({})\n",
                bid,
                target.0,
                arg_vars.join(", ")
            ));
        }
        Term::If {
            cond,
            then_b,
            else_b,
            ..
        } => {
            out.push_str(&format!(
                ";     blk{} If Var({}) ? blk{} : blk{}\n",
                bid, cond.0, then_b.0, else_b.0
            ));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn render_tail_call_exit<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
    t: &T,
    m: &Module,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    any_ty: &crate::types::Ty,
    callee: FnId,
    args: &[crate::fz_ir::Var],
    ident: &CallsiteIdent,
    out: &mut String,
) {
    let arg_tys = arg_tys(ft, args, any_ty);
    let arg_vars = vars_str(args);
    out.push_str(&format!(
        ";     blk{} TailCall {}#{}({})\n",
        b.id.0,
        fn_name(m, callee),
        callee.0,
        arg_vars.join(", ")
    ));
    out.push_str(&format!(
        ";              callee_key={}\n",
        tys_str(t, &arg_tys)
    ));
    render_return_use(t, spec_key, ft, ident, EmitSlot::Direct, out);
    render_list_tail_plan(t, spec_key, ft, ident, EmitSlot::Direct, out);
}

#[allow(clippy::too_many_arguments)]
fn render_call_exit<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    any_ty: &crate::types::Ty,
    callee: FnId,
    args: &[crate::fz_ir::Var],
    ident: &CallsiteIdent,
    continuation: &crate::fz_ir::Cont,
    out: &mut String,
) {
    let arg_tys = arg_tys(ft, args, any_ty);
    let arg_vars = vars_str(args);
    let cap_vars = vars_str(&continuation.captured);
    let ck = cont_input_key(t, b, continuation, ft, m, mt);
    out.push_str(&format!(
        ";     blk{} Call {}#{}({})\n",
        b.id.0,
        fn_name(m, callee),
        callee.0,
        arg_vars.join(", ")
    ));
    out.push_str(&format!(
        ";              callee_key={}\n",
        tys_str(&*t, &arg_tys)
    ));
    render_return_use(&*t, spec_key, ft, ident, EmitSlot::Direct, out);
    render_list_tail_plan(&*t, spec_key, ft, ident, EmitSlot::Direct, out);
    render_cont_lines(&*t, m, continuation, &cap_vars, &ck, out);
}

fn render_call_closure_exit<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    closure: crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
    continuation: &crate::fz_ir::Cont,
    out: &mut String,
) {
    let arg_vars = vars_str(args);
    let cap_vars = vars_str(&continuation.captured);
    let ck = cont_input_key(t, b, continuation, ft, m, mt);
    let target = ft.fn_constants.get(&closure).copied();
    let target_str = resolved_target_str(m, target);
    out.push_str(&format!(
        ";     blk{} CallClosure Var({})({}){}\n",
        b.id.0,
        closure.0,
        arg_vars.join(", "),
        target_str
    ));
    render_cont_lines(&*t, m, continuation, &cap_vars, &ck, out);
}

fn render_tail_call_closure_exit(
    m: &Module,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    closure: crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
    out: &mut String,
) {
    let arg_vars = vars_str(args);
    let target = ft.fn_constants.get(&closure).copied();
    let target_str = resolved_target_str(m, target);
    out.push_str(&format!(
        ";     blk{} TailCallClosure Var({})({}){}\n",
        b.id.0,
        closure.0,
        arg_vars.join(", "),
        target_str
    ));
}

fn render_receive_exit<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    ft: &super::fn_types::SpecPlan,
    b: &Block,
    continuation: &crate::fz_ir::Cont,
    out: &mut String,
) {
    let cap_vars = vars_str(&continuation.captured);
    let ck = cont_input_key(t, b, continuation, ft, m, mt);
    out.push_str(&format!(
        ";     blk{} Receive cont {}#{} captured=[{}]\n",
        b.id.0,
        fn_name(m, continuation.fn_id),
        continuation.fn_id.0,
        cap_vars.join(", ")
    ));
    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
}

fn render_receive_matched_exit(
    m: &Module,
    b: &Block,
    clauses: &[crate::fz_ir::ReceiveClause],
    after: &Option<crate::fz_ir::ReceiveAfter>,
    pinned: &[(String, crate::fz_ir::Var)],
    captures: &[crate::fz_ir::Var],
    out: &mut String,
) {
    let pin_vars: Vec<String> = pinned
        .iter()
        .map(|(n, v)| format!("^{}=Var({})", n, v.0))
        .collect();
    let cap_vars = vars_str(captures);
    out.push_str(&format!(
        ";     blk{} ReceiveMatched pinned=[{}] caps=[{}]\n",
        b.id.0,
        pin_vars.join(", "),
        cap_vars.join(", "),
    ));
    for (i, c) in clauses.iter().enumerate() {
        out.push_str(&format!(
            ";              clause[{}] body={}#{} bound=[{}]{}\n",
            i,
            fn_name(m, c.body),
            c.body.0,
            c.bound_names.join(", "),
            match c.guard {
                Some(g) => format!(" guard={}#{}", fn_name(m, g), g.0),
                None => String::new(),
            },
        ));
    }
    if let Some(a) = after {
        out.push_str(&format!(
            ";              after timeout=Var({}) body={}#{}\n",
            a.timeout.0,
            fn_name(m, a.body),
            a.body.0,
        ));
    }
}

fn render_cont_lines<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &T,
    m: &Module,
    continuation: &crate::fz_ir::Cont,
    cap_vars: &[String],
    key: &[crate::types::Ty],
    out: &mut String,
) {
    out.push_str(&format!(
        ";              cont {}#{} captured=[{}]\n",
        fn_name(m, continuation.fn_id),
        continuation.fn_id.0,
        cap_vars.join(", ")
    ));
    out.push_str(&format!(";              cont_key={}\n", tys_str(t, key)));
}

fn render_return_use<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &T,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    ident: &CallsiteIdent,
    slot: EmitSlot,
    out: &mut String,
) {
    let cid = CallsiteId::new(spec_key.fn_id, ident, slot);
    if let Some(return_use) = ft.return_uses.get(&cid) {
        out.push_str(&format!(
            ";              return_use={}\n",
            display_return_demand(t, return_use)
        ));
    }
}

fn render_list_tail_plan<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes,
>(
    t: &T,
    spec_key: &SpecKey,
    ft: &super::fn_types::SpecPlan,
    ident: &CallsiteIdent,
    slot: EmitSlot,
    out: &mut String,
) {
    let cid = CallsiteId::new(spec_key.fn_id, ident, slot);
    if let Some(plan) = ft
        .return_context_plans
        .get(&ReturnContextPlanKey::new(spec_key, &cid))
    {
        out.push_str(&format!(
            ";              list_tail_plan={}\n",
            display_return_context_plan(t, plan)
        ));
    }
}

fn fn_name(m: &Module, fid: FnId) -> String {
    m.fns
        .iter()
        .find(|f| f.id == fid)
        .map(|f| f.name.clone())
        .unwrap_or_else(|| format!("?fn{}", fid.0))
}

fn vars_str(vars: &[crate::fz_ir::Var]) -> Vec<String> {
    vars.iter().map(|v| format!("Var({})", v.0)).collect()
}

fn arg_tys(
    ft: &super::fn_types::SpecPlan,
    args: &[crate::fz_ir::Var],
    any_ty: &crate::types::Ty,
) -> Vec<crate::types::Ty> {
    args.iter()
        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
        .collect()
}

fn tys_str<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &T,
    ts: &[crate::types::Ty],
) -> String {
    let parts: Vec<String> = ts.iter().map(|ty| t.display(ty)).collect();
    format!("[{}]", parts.join(", "))
}

fn resolved_target_str(m: &Module, target: Option<FnId>) -> String {
    match target {
        Some(fid) => format!(" [resolved={}#{}]", fn_name(m, fid), fid.0),
        None => String::new(),
    }
}
