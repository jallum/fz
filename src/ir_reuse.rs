use crate::fz_ir::{FnIr, Module, OwnedConsReuseCredit, Var};

pub fn prune_borrowed_owned_cons_reuse_credits(module: &mut Module) {
    let effect_module = Module {
        externs: module.externs.clone(),
        extern_idx: module.extern_idx.clone(),
        ..Module::default()
    };

    for f in &mut module.fns {
        prune_fn_borrowed_reuse_credits(&effect_module, f);
    }
}

fn prune_fn_borrowed_reuse_credits(module: &Module, f: &mut FnIr) {
    if f.owned_cons_reuse_credits.is_empty() {
        return;
    }
    let ignored_params = ignored_entry_params(f);
    let credits = std::mem::take(&mut f.owned_cons_reuse_credits);
    f.owned_cons_reuse_credits = credits
        .into_iter()
        .filter(|credit| credit_source_is_owned(module, f, &ignored_params, *credit))
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
    module: &Module,
    f: &FnIr,
    ignored_params: &std::collections::HashSet<Var>,
    credit: OwnedConsReuseCredit,
) -> bool {
    let source_is_hidden_transport = ignored_params.contains(&credit.source_cons);
    for block in &f.blocks {
        for stmt in &block.stmts {
            let crate::fz_ir::Stmt::Let(_, prim) = stmt;
            if crate::ir_effects::prim_publishes_var(module, prim, credit.source_cons) {
                return false;
            }
        }
        if crate::ir_effects::term_publishes_var(
            &block.terminator,
            credit.source_cons,
            source_is_hidden_transport,
        ) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{
        ExternArg, ExternDecl, ExternId, ExternTy, FnBuilder, FnId, ModuleBuilder, Prim, Term,
    };
    use crate::types::Types;

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
        module.extern_idx.insert(ExternId(0), 0);
        let mut types = crate::types::ConcreteTypes;
        module.externs.push(ExternDecl {
            id: ExternId(0),
            fz_name: "keeps_nothing".to_owned(),
            symbol: "keeps_nothing".to_owned(),
            params: vec![ExternTy::Any],
            variadic: false,
            ret: ExternTy::Unit,
            ret_descr: types.any(),
        });

        prune_borrowed_owned_cons_reuse_credits(&mut module);

        assert_eq!(module.fns[0].owned_cons_reuse_credits.len(), 1);
        assert_eq!(
            module.fns[0].owned_cons_reuse_credits[0].source_cons,
            source
        );
    }
}
