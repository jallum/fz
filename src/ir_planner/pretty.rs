use super::fn_types::{ModulePlan, SpecKey, SpecPlan, display_return_demand, display_return_strategy};
use super::reachable::cont_input_key;
use crate::fz_ir::{
    Block, CallsiteId, CallsiteIdent, Cont, DirectCallTarget, EmitSlot, FnId, FnIr, Module, PhysicalCapability,
    ReceiveAfter, ReceiveClause, Term, Var,
};
use crate::types::{ClosureTypes, RenderTypes, Ty, Types, display_key_slots};

// Pretty-printer for ModulePlan golden spec dumps.

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
pub fn pretty_module_plan<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
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
    T: Types<Ty = Ty> + ClosureTypes + RenderTypes,
{
    let mut keys: Vec<&SpecKey> = mt.specs.keys().collect();
    keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| display_key_slots(t, &a.input).cmp(&display_key_slots(t, &b.input)))
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    keys
}

fn render_spec<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    any_ty: &Ty,
    out: &mut String,
) {
    let ft = &mt.specs[spec_key];
    let f = m.fn_by_id(spec_key.fn_id);
    render_spec_header(t, m, mt, spec_key, any_ty, out);
    render_callable_capabilities(m, ft, out);
    render_physical_capabilities(f, out);
    render_vars(t, ft, out);
    render_exits(t, m, mt, spec_key, ft, f, any_ty, out);
    out.push('\n');
}

fn render_spec_header<T: Types<Ty = Ty> + RenderTypes>(
    t: &T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    any_ty: &Ty,
    out: &mut String,
) {
    let f = m.fn_by_id(spec_key.fn_id);
    let arity = f.block(f.entry).params.len();
    out.push_str(&format!("; spec {}({}) #fn={}\n", f.name, arity, spec_key.fn_id.0));
    out.push_str(&format!(";   key:    {}\n", display_key_slots(t, &spec_key.input)));
    out.push_str(&format!(";   demand: {}\n", display_return_demand(t, &spec_key.demand)));
    let ret = mt.effective_returns.get(&spec_key.body_key());
    out.push_str(&format!(
        ";   return: {}\n",
        ret.map(|ty| t.display(ty)).unwrap_or_else(|| t.display(any_ty))
    ));
}

fn render_callable_capabilities(m: &Module, ft: &SpecPlan, out: &mut String) {
    use super::fn_types::CallableCapability;

    if ft.callable_capabilities.is_empty() {
        return;
    }
    let mut capabilities: Vec<_> = ft.callable_capabilities.iter().collect();
    capabilities.sort_by_key(|(v, _)| v.0);
    out.push_str(";   callable_capabilities:\n");
    for (v, capability) in capabilities {
        match capability {
            CallableCapability::KnownFn(fid) => out.push_str(&format!(
                ";     Var({}) = KnownFn({}#{})\n",
                v.0,
                fn_name(m, *fid),
                fid.0
            )),
            CallableCapability::KnownClosure { fn_id, captures, .. } => out.push_str(&format!(
                ";     Var({}) = KnownClosure({}#{}, {} captures)\n",
                v.0,
                fn_name(m, *fn_id),
                fn_id.0,
                captures.len()
            )),
            CallableCapability::OpaqueCallable => out.push_str(&format!(";     Var({}) = OpaqueCallable\n", v.0)),
        }
    }
}

fn render_physical_capabilities(f: &FnIr, out: &mut String) {
    if f.physical_capabilities.is_empty() {
        return;
    }
    let mut physical = f.physical_capabilities.clone();
    physical.sort_by_key(|cap| cap.source.0);
    out.push_str(";   physical_capabilities:\n");
    for cap in physical {
        match cap.capability {
            PhysicalCapability::OwnedConsReuse { head } => {
                out.push_str(&format!(
                    ";     owned_cons_source param=Var({}) head=Var({})\n",
                    cap.source.0, head.0
                ));
            }
        }
    }
}

fn render_vars<T: Types<Ty = Ty> + RenderTypes>(t: &T, ft: &SpecPlan, out: &mut String) {
    let mut vars: Vec<(&Var, &Ty)> = ft.vars.iter().collect();
    vars.sort_by_key(|(v, _)| v.0);
    out.push_str(";   vars:\n");
    for (v, ty) in vars {
        out.push_str(&format!(";     Var({}) :: {}\n", v.0, t.display(ty)));
    }
}

fn render_exits<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    f: &FnIr,
    any_ty: &Ty,
    out: &mut String,
) {
    let mut blocks: Vec<&Block> = f.blocks.iter().collect();
    blocks.sort_by_key(|b| b.id.0);
    out.push_str(";   exits:\n");
    for b in blocks {
        render_terminator_exit(t, m, mt, spec_key, ft, b, any_ty, out);
    }
}

fn render_terminator_exit<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    b: &Block,
    any_ty: &Ty,
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
            callee, args, ident, ..
        } => {
            render_tail_call_exit(t, m, spec_key, ft, b, any_ty, callee, args, ident, out);
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
                callee,
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
            cond, then_b, else_b, ..
        } => {
            out.push_str(&format!(
                ";     blk{} If Var({}) ? blk{} : blk{}\n",
                bid, cond.0, then_b.0, else_b.0
            ));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn render_tail_call_exit<T: Types<Ty = Ty> + RenderTypes>(
    t: &T,
    m: &Module,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    b: &Block,
    any_ty: &Ty,
    callee: &DirectCallTarget,
    args: &[Var],
    ident: &CallsiteIdent,
    out: &mut String,
) {
    let arg_tys = arg_tys(ft, args, any_ty);
    let arg_vars = vars_str(args);
    match callee {
        DirectCallTarget::Local(callee) => out.push_str(&format!(
            ";     blk{} TailCall {}#{}({})\n",
            b.id.0,
            fn_name(m, *callee),
            callee.0,
            arg_vars.join(", ")
        )),
        DirectCallTarget::ProviderBoundary(target) => out.push_str(&format!(
            ";     blk{} TailCall {}({})\n",
            b.id.0,
            target,
            arg_vars.join(", ")
        )),
    }
    out.push_str(&format!(";              callee_key={}\n", tys_str(t, &arg_tys)));
    if matches!(callee, DirectCallTarget::Local(_)) {
        render_return_use(t, spec_key, ft, ident, EmitSlot::Direct, out);
    }
}

#[allow(clippy::too_many_arguments)]
fn render_call_exit<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    b: &Block,
    any_ty: &Ty,
    callee: &DirectCallTarget,
    args: &[Var],
    ident: &CallsiteIdent,
    continuation: &Cont,
    out: &mut String,
) {
    let arg_tys = arg_tys(ft, args, any_ty);
    let arg_vars = vars_str(args);
    let cap_vars = vars_str(&continuation.captured);
    let ck = cont_input_key(t, b, continuation, ft, m, mt);
    match callee {
        DirectCallTarget::Local(callee) => out.push_str(&format!(
            ";     blk{} Call {}#{}({})\n",
            b.id.0,
            fn_name(m, *callee),
            callee.0,
            arg_vars.join(", ")
        )),
        DirectCallTarget::ProviderBoundary(target) => out.push_str(&format!(
            ";     blk{} Call {}({})\n",
            b.id.0,
            target,
            arg_vars.join(", ")
        )),
    }
    out.push_str(&format!(";              callee_key={}\n", tys_str(&*t, &arg_tys)));
    if matches!(callee, DirectCallTarget::Local(_)) {
        render_return_use(&*t, spec_key, ft, ident, EmitSlot::Direct, out);
    }
    render_cont_lines(&*t, m, continuation, &cap_vars, &ck, out);
}

fn render_call_closure_exit<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    m: &Module,
    mt: &ModulePlan,
    ft: &SpecPlan,
    b: &Block,
    closure: Var,
    args: &[Var],
    continuation: &Cont,
    out: &mut String,
) {
    let arg_vars = vars_str(args);
    let cap_vars = vars_str(&continuation.captured);
    let ck = cont_input_key(t, b, continuation, ft, m, mt);
    let target = ft.known_fn(&closure);
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

fn render_tail_call_closure_exit(m: &Module, ft: &SpecPlan, b: &Block, closure: Var, args: &[Var], out: &mut String) {
    let arg_vars = vars_str(args);
    let target = ft.known_fn(&closure);
    let target_str = resolved_target_str(m, target);
    out.push_str(&format!(
        ";     blk{} TailCallClosure Var({})({}){}\n",
        b.id.0,
        closure.0,
        arg_vars.join(", "),
        target_str
    ));
}

fn render_receive_matched_exit(
    m: &Module,
    b: &Block,
    clauses: &[ReceiveClause],
    after: &Option<ReceiveAfter>,
    pinned: &[(String, Var)],
    captures: &[Var],
    out: &mut String,
) {
    let pin_vars: Vec<String> = pinned.iter().map(|(n, v)| format!("^{}=Var({})", n, v.0)).collect();
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

fn render_cont_lines<T: Types<Ty = Ty> + RenderTypes>(
    t: &T,
    m: &Module,
    continuation: &Cont,
    cap_vars: &[String],
    key: &[Ty],
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

fn render_return_use<T: Types<Ty = Ty> + RenderTypes>(
    t: &T,
    spec_key: &SpecKey,
    ft: &SpecPlan,
    ident: &CallsiteIdent,
    slot: EmitSlot,
    out: &mut String,
) {
    let cid = CallsiteId::new(spec_key.fn_id, ident, slot);
    if let Some(return_use) = ft.return_use(&cid) {
        out.push_str(&format!(
            ";              return_use={}\n",
            display_return_demand(t, return_use)
        ));
    }
    if let Some(contract) = ft.return_contract(&cid) {
        out.push_str(&format!(
            ";              return_contract={} target_demand={}\n",
            display_return_strategy(t, &contract.strategy),
            display_return_demand(t, &contract.target.demand)
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

fn vars_str(vars: &[Var]) -> Vec<String> {
    vars.iter().map(|v| format!("Var({})", v.0)).collect()
}

fn arg_tys(ft: &SpecPlan, args: &[Var], any_ty: &Ty) -> Vec<Ty> {
    args.iter()
        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
        .collect()
}

fn tys_str<T: Types<Ty = Ty> + RenderTypes>(t: &T, ts: &[Ty]) -> String {
    let parts: Vec<String> = ts.iter().map(|ty| t.display(ty)).collect();
    format!("[{}]", parts.join(", "))
}

fn resolved_target_str(m: &Module, target: Option<FnId>) -> String {
    match target {
        Some(fid) => format!(" [resolved={}#{}]", fn_name(m, fid), fid.0),
        None => String::new(),
    }
}
