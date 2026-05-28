use crate::fz_ir::{FnIr, Module, OwnedConsReuseCredit, Prim, Term, Var, prim_uses_var};

pub fn prune_borrowed_owned_cons_reuse_credits(module: &mut Module) {
    for f in &mut module.fns {
        prune_fn_borrowed_reuse_credits(f);
    }
}

fn prune_fn_borrowed_reuse_credits(f: &mut FnIr) {
    if f.owned_cons_reuse_credits.is_empty() {
        return;
    }
    let ignored_params = ignored_entry_params(f);
    let credits = std::mem::take(&mut f.owned_cons_reuse_credits);
    f.owned_cons_reuse_credits = credits
        .into_iter()
        .filter(|credit| credit_source_is_owned(f, &ignored_params, *credit))
        .collect();
}

fn ignored_entry_params(f: &FnIr) -> std::collections::HashSet<Var> {
    f.block(f.entry)
        .params
        .iter()
        .zip(&f.ignored_entry_params)
        .filter_map(|(param, ignored)| ignored.then_some(*param))
        .collect()
}

fn credit_source_is_owned(
    f: &FnIr,
    ignored_params: &std::collections::HashSet<Var>,
    credit: OwnedConsReuseCredit,
) -> bool {
    let source_is_hidden_transport = ignored_params.contains(&credit.source_cons);
    for block in &f.blocks {
        for stmt in &block.stmts {
            let crate::fz_ir::Stmt::Let(_, prim) = stmt;
            if prim_publishes_credit_source(prim, credit.source_cons) {
                return false;
            }
        }
        if term_publishes_credit_source(
            &block.terminator,
            credit.source_cons,
            source_is_hidden_transport,
        ) {
            return false;
        }
    }
    true
}

fn prim_publishes_credit_source(prim: &Prim, source_cons: Var) -> bool {
    match prim {
        Prim::Extern(_, _)
        | Prim::ListHead(_)
        | Prim::ListTail(_)
        | Prim::IsEmptyList(_)
        | Prim::TypeTest(_, _) => false,
        _ => prim_uses_var(prim, source_cons),
    }
}

fn term_publishes_credit_source(term: &Term, source_cons: Var, hidden_transport: bool) -> bool {
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } => {
            !hidden_transport && args.contains(&source_cons)
        }
        Term::If { cond, .. } | Term::Return(cond) | Term::Halt(cond) => *cond == source_cons,
        Term::TailCallClosure { args, .. } => args.contains(&source_cons),
        Term::Call { args, .. } | Term::CallClosure { args, .. } => args.contains(&source_cons),
        Term::Receive { continuation, .. } => {
            !hidden_transport && continuation.captured.contains(&source_cons)
        }
        Term::ReceiveMatched {
            after,
            pinned,
            captures,
            ..
        } => {
            after
                .as_ref()
                .is_some_and(|after| after.timeout == source_cons)
                || pinned.iter().any(|(_, v)| *v == source_cons)
                || captures.contains(&source_cons)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{ExternArg, ExternId, ExternTy, FnBuilder, FnId, ModuleBuilder};

    #[test]
    fn extern_arguments_do_not_prune_owned_cons_reuse_credits() {
        let mut b = FnBuilder::new(FnId(0), "extern_arg");
        let source = b.fresh_var();
        let entry = b.block(vec![source]);
        let head = b.let_(entry, Prim::ListHead(source));
        b.record_owned_cons_reuse_credit(head, source);
        b.let_(
            entry,
            Prim::Extern(ExternId(0), vec![ExternArg::fixed(source, ExternTy::Any)]),
        );
        b.set_terminator(entry, Term::Return(head));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut module = mb.build();

        prune_borrowed_owned_cons_reuse_credits(&mut module);

        assert_eq!(module.fns[0].owned_cons_reuse_credits.len(), 1);
        assert_eq!(
            module.fns[0].owned_cons_reuse_credits[0].source_cons,
            source
        );
    }
}
