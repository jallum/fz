use crate::fz_ir::{Module, Prim, Term, Var, prim_uses_var};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct IrEffects {
    pub allocates: bool,
    pub publishes_same_heap_refs: bool,
    pub observes_allocation: bool,
    pub deep_copies: bool,
    pub scheduler_boundary: bool,
    pub materialization_boundary: bool,
    pub externally_observable: bool,
    pub halts: bool,
    pub extern_retains_arguments: bool,
}

pub(crate) fn prim_effects(module: &Module, prim: &Prim) -> IrEffects {
    match prim {
        Prim::Extern(eid, _) => {
            let decl = module.extern_by_id(*eid);
            let observes_allocation = decl.symbol == "fz_process_heap_alloc_stats";
            let deep_copies = matches!(decl.symbol.as_str(), "fz_send");
            let scheduler_boundary = matches!(
                decl.symbol.as_str(),
                "fz_send" | "fz_spawn" | "fz_spawn_opt"
            );
            IrEffects {
                observes_allocation,
                deep_copies,
                scheduler_boundary,
                externally_observable: true,
                halts: decl.ret == crate::fz_ir::ExternTy::Never,
                extern_retains_arguments: false,
                ..IrEffects::default()
            }
        }
        Prim::MakeTuple(_)
        | Prim::DestTupleBegin { .. }
        | Prim::DestTupleSet { .. }
        | Prim::DestFreeze { .. }
        | Prim::MakeList(_, _)
        | Prim::DestListBegin { .. }
        | Prim::DestListCons { .. }
        | Prim::DestListFreeze { .. }
        | Prim::MakeClosure(_, _, _)
        | Prim::MakeMap(_)
        | Prim::MapUpdate(_, _)
        | Prim::DestMapBegin { .. }
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze { .. }
        | Prim::MakeBitstring(_)
        | Prim::ConstBitstring(_, _)
        | Prim::BitReaderInit(_) => IrEffects {
            allocates: true,
            publishes_same_heap_refs: true,
            ..IrEffects::default()
        },
        Prim::Const(_)
        | Prim::BinOp(_, _, _)
        | Prim::UnOp(_, _)
        | Prim::ListHead(_)
        | Prim::ListTail(_)
        | Prim::IsEmptyList(_)
        | Prim::TupleField(_, _)
        | Prim::MapGet(_, _)
        | Prim::MatcherMapGet(_, _)
        | Prim::IsMatcherMapMiss(_)
        | Prim::BitReadField { .. }
        | Prim::BitReaderDone(_)
        | Prim::TypeTest(_, _)
        | Prim::Brand(_, _) => IrEffects::default(),
    }
}

pub(crate) fn term_effects(term: &Term) -> IrEffects {
    match term {
        Term::Call { .. } | Term::CallClosure { .. } => IrEffects {
            publishes_same_heap_refs: true,
            ..IrEffects::default()
        },
        Term::Receive { .. } | Term::ReceiveMatched { .. } => IrEffects {
            publishes_same_heap_refs: true,
            scheduler_boundary: true,
            materialization_boundary: true,
            externally_observable: true,
            ..IrEffects::default()
        },
        Term::Halt(_) => IrEffects {
            publishes_same_heap_refs: true,
            externally_observable: true,
            halts: true,
            ..IrEffects::default()
        },
        Term::Return(_)
        | Term::Goto(_, _)
        | Term::TailCall { .. }
        | Term::TailCallClosure { .. } => IrEffects {
            publishes_same_heap_refs: true,
            ..IrEffects::default()
        },
        Term::If { .. } => IrEffects::default(),
    }
}

pub(crate) fn prim_publishes_var(module: &Module, prim: &Prim, var: Var) -> bool {
    let effects = prim_effects(module, prim);
    effects.publishes_same_heap_refs && prim_uses_var(prim, var)
}

pub(crate) fn term_publishes_var(term: &Term, var: Var, hidden_transport: bool) -> bool {
    if !term_effects(term).publishes_same_heap_refs {
        return false;
    }
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } => {
            !hidden_transport && args.contains(&var)
        }
        Term::TailCallClosure { args, .. } => args.contains(&var),
        Term::Call { args, .. } | Term::CallClosure { args, .. } => args.contains(&var),
        Term::Return(value) | Term::Halt(value) => *value == var,
        Term::Receive { continuation, .. } => {
            !hidden_transport && continuation.captured.contains(&var)
        }
        Term::ReceiveMatched {
            after,
            pinned,
            captures,
            ..
        } => {
            after.as_ref().is_some_and(|after| after.timeout == var)
                || pinned.iter().any(|(_, pinned)| *pinned == var)
                || captures.contains(&var)
        }
        Term::If { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{ExternDecl, ExternId, ExternTy};
    use crate::types::Types;

    fn module_with_extern(symbol: &str, ret: ExternTy) -> Module {
        let mut module = Module::new();
        module.extern_idx.insert(ExternId(0), 0);
        let mut types = crate::types::ConcreteTypes;
        module.externs.push(ExternDecl {
            id: ExternId(0),
            fz_name: symbol.to_owned(),
            symbol: symbol.to_owned(),
            params: vec![ExternTy::Any],
            variadic: false,
            ret,
            ret_descr: types.any(),
        });
        module
    }

    #[test]
    fn extern_arguments_are_not_retained_by_default() {
        let module = module_with_extern("user_extern", ExternTy::Any);
        let effects = prim_effects(
            &module,
            &Prim::Extern(
                ExternId(0),
                vec![crate::fz_ir::ExternArg::fixed(Var(0), ExternTy::Any)],
            ),
        );

        assert!(effects.externally_observable);
        assert!(!effects.extern_retains_arguments);
        assert!(!effects.publishes_same_heap_refs);
    }

    #[test]
    fn send_is_deep_copy_scheduler_boundary_not_same_heap_publish() {
        let module = module_with_extern("fz_send", ExternTy::Unit);
        let effects = prim_effects(
            &module,
            &Prim::Extern(
                ExternId(0),
                vec![crate::fz_ir::ExternArg::fixed(Var(0), ExternTy::Any)],
            ),
        );

        assert!(effects.deep_copies);
        assert!(effects.scheduler_boundary);
        assert!(!effects.publishes_same_heap_refs);
    }

    #[test]
    fn heap_stats_observes_allocation() {
        let module = module_with_extern("fz_process_heap_alloc_stats", ExternTy::Any);
        let effects = prim_effects(&module, &Prim::Extern(ExternId(0), vec![]));

        assert!(effects.observes_allocation);
        assert!(effects.externally_observable);
    }
}
