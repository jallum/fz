use super::fn_types::{ModuleTypes, SpecKey};
use super::reachable::cont_input_key;
use crate::fz_ir::{Block, FnId, Module, Term};

// ----------------------------------------------------------------------
// fz-73m — pretty-printer for ModuleTypes (golden spec dump).
// ----------------------------------------------------------------------

/// Deterministic text dump of `ModuleTypes`. One stanza per (FnId, key)
/// spec; specs are sorted by FnId, then by lexicographic display-string of
/// the key so the output is stable across runs and HashMap iteration
/// orders.
///
/// Format is intended for golden-file diffing — every line is a comment
/// (`;` prefix) so the file reads like an annotated CLIF dump. Consumers
/// should treat the output as opaque text; the goal is that a human can
/// eyeball "are the inferred types what I expect for this fixture?"
/// without running codegen.
pub fn pretty_module_types<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModuleTypes,
) -> String {
    fn tys_str<
        T: crate::types::Types<Ty = crate::types::Ty>
            + crate::types::ClosureTypes
            + crate::types::RenderTypes,
    >(
        t: &T,
        ts: &[crate::types::Ty],
    ) -> String {
        let parts: Vec<String> = ts.iter().map(|ty| t.display(ty)).collect();
        format!("[{}]", parts.join(", "))
    }

    let any_ty = t.any();
    let fn_name = |fid: FnId| -> String {
        m.fns
            .iter()
            .find(|f| f.id == fid)
            .map(|f| f.name.clone())
            .unwrap_or_else(|| format!("?fn{}", fid.0))
    };

    let mut keys: Vec<&SpecKey> = mt.specs.keys().collect();
    keys.sort_by(|a, b| {
        a.0.0.cmp(&b.0.0).then_with(|| {
            crate::types::display_key_slots(&*t, &a.1)
                .cmp(&crate::types::display_key_slots(&*t, &b.1))
        })
    });

    let mut out = String::new();
    for spec_key in keys {
        let (fid, key) = spec_key;
        let ft = &mt.specs[spec_key];
        let f = m.fn_by_id(*fid);
        let entry = f.block(f.entry);
        let arity = entry.params.len();

        out.push_str(&format!("; spec {}({}) #fn={}\n", f.name, arity, fid.0));
        out.push_str(&format!(
            ";   key:    {}\n",
            crate::types::display_key_slots(&*t, key)
        ));

        let ret = mt.effective_returns.get(spec_key);
        out.push_str(&format!(
            ";   return: {}\n",
            ret.map(|ty| t.display(ty))
                .unwrap_or_else(|| t.display(&any_ty))
        ));

        if !ft.fn_constants.is_empty() {
            let mut fcs: Vec<(&crate::fz_ir::Var, &FnId)> = ft.fn_constants.iter().collect();
            fcs.sort_by_key(|(v, _)| v.0);
            out.push_str(";   fn_constants:\n");
            for (v, fc) in fcs {
                out.push_str(&format!(";     Var({}) = {}#{}\n", v.0, fn_name(*fc), fc.0));
            }
        }

        let mut vars: Vec<(&crate::fz_ir::Var, &crate::types::Ty)> = ft.vars.iter().collect();
        vars.sort_by_key(|(v, _)| v.0);
        out.push_str(";   vars:\n");
        for (v, ty) in vars {
            out.push_str(&format!(";     Var({}) :: {}\n", v.0, t.display(ty)));
        }

        let mut blocks: Vec<&Block> = f.blocks.iter().collect();
        blocks.sort_by_key(|b| b.id.0);
        out.push_str(";   exits:\n");
        for b in blocks {
            let bid = b.id.0;
            match &b.terminator {
                Term::Return(v) => {
                    let d = ft.vars.get(v).unwrap_or(&any_ty);
                    out.push_str(&format!(
                        ";     blk{} Return Var({})    :: {}\n",
                        bid,
                        v.0,
                        t.display(d)
                    ));
                }
                Term::Halt(v) => {
                    let d = ft.vars.get(v).unwrap_or(&any_ty);
                    out.push_str(&format!(
                        ";     blk{} Halt Var({})      :: {}\n",
                        bid,
                        v.0,
                        t.display(d)
                    ));
                }
                Term::TailCall { callee, args, .. } => {
                    let arg_tys: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    out.push_str(&format!(
                        ";     blk{} TailCall {}#{}({})\n",
                        bid,
                        fn_name(*callee),
                        callee.0,
                        arg_vars.join(", ")
                    ));
                    out.push_str(&format!(
                        ";              callee_key={}\n",
                        tys_str(&*t, &arg_tys)
                    ));
                }
                Term::Call {
                    ident: _,
                    callee,
                    args,
                    continuation,
                } => {
                    let arg_tys: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
                    out.push_str(&format!(
                        ";     blk{} Call {}#{}({})\n",
                        bid,
                        fn_name(*callee),
                        callee.0,
                        arg_vars.join(", ")
                    ));
                    out.push_str(&format!(
                        ";              callee_key={}\n",
                        tys_str(&*t, &arg_tys)
                    ));
                    out.push_str(&format!(
                        ";              cont {}#{} captured=[{}]\n",
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                Term::CallClosure {
                    ident: _,
                    closure,
                    args,
                    continuation,
                } => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
                    let target = ft.fn_constants.get(closure).copied();
                    let target_str = match target {
                        Some(fid) => format!(" [resolved={}#{}]", fn_name(fid), fid.0),
                        None => String::new(),
                    };
                    out.push_str(&format!(
                        ";     blk{} CallClosure Var({})({}){}\n",
                        bid,
                        closure.0,
                        arg_vars.join(", "),
                        target_str
                    ));
                    out.push_str(&format!(
                        ";              cont {}#{} captured=[{}]\n",
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let target = ft.fn_constants.get(closure).copied();
                    let target_str = match target {
                        Some(fid) => format!(" [resolved={}#{}]", fn_name(fid), fid.0),
                        None => String::new(),
                    };
                    out.push_str(&format!(
                        ";     blk{} TailCallClosure Var({})({}){}\n",
                        bid,
                        closure.0,
                        arg_vars.join(", "),
                        target_str
                    ));
                }
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
                    out.push_str(&format!(
                        ";     blk{} Receive cont {}#{} captured=[{}]\n",
                        bid,
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                // fz-yxs — selective receive: render clauses (with body
                // fn ids + bound names) and the after clause if present.
                Term::ReceiveMatched {
                    clauses,
                    after,
                    pinned,
                    captures,
                    ..
                } => {
                    let pin_vars: Vec<String> = pinned
                        .iter()
                        .map(|(n, v)| format!("^{}=Var({})", n, v.0))
                        .collect();
                    let cap_vars: Vec<String> =
                        captures.iter().map(|v| format!("Var({})", v.0)).collect();
                    out.push_str(&format!(
                        ";     blk{} ReceiveMatched pinned=[{}] caps=[{}]\n",
                        bid,
                        pin_vars.join(", "),
                        cap_vars.join(", "),
                    ));
                    for (i, c) in clauses.iter().enumerate() {
                        out.push_str(&format!(
                            ";              clause[{}] body={}#{} bound=[{}]{}\n",
                            i,
                            fn_name(c.body),
                            c.body.0,
                            c.bound_names.join(", "),
                            match c.guard {
                                Some(g) => format!(" guard={}#{}", fn_name(g), g.0),
                                None => String::new(),
                            },
                        ));
                    }
                    if let Some(a) = after {
                        out.push_str(&format!(
                            ";              after timeout=Var({}) body={}#{}\n",
                            a.timeout.0,
                            fn_name(a.body),
                            a.body.0,
                        ));
                    }
                }
                Term::Goto(target, args) => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
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
        out.push('\n');
    }
    out
}
