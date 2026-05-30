use crate::fz_ir::{Module, Prim, Term};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct IrEffects {
    pub allocates: bool,
    pub observes_allocation: bool,
    pub scheduler_boundary: bool,
    pub externally_observable: bool,
    pub halts: bool,
    /// Calls through a value whose target the planner cannot see (a closure
    /// call). Opaque because the callee's effects are unknown, so it is a
    /// conservative barrier to return-context motion until the target is
    /// resolved.
    pub calls_opaque: bool,
}

pub(crate) fn prim_effects(module: &Module, prim: &Prim) -> IrEffects {
    match prim {
        Prim::Extern(eid, _) => {
            let decl = module.extern_by_id(*eid);
            let observes_allocation = decl.symbol == "fz_process_heap_alloc_stats";
            let scheduler_boundary = matches!(
                decl.symbol.as_str(),
                "fz_send" | "fz_spawn" | "fz_spawn_opt"
            );
            IrEffects {
                observes_allocation,
                scheduler_boundary,
                externally_observable: true,
                halts: decl.ret == crate::fz_ir::ExternTy::Never,
                ..IrEffects::default()
            }
        }
        Prim::MakeTuple(_)
        | Prim::MakeStruct { .. }
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
            ..IrEffects::default()
        },
        Prim::Const(_)
        | Prim::BinOp(_, _, _)
        | Prim::UnOp(_, _)
        | Prim::ListHead(_)
        | Prim::ListTail(_)
        | Prim::IsEmptyList(_)
        | Prim::TupleField(_, _)
        | Prim::StructField(_, _)
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
        Term::Call { .. } | Term::TailCall { .. } => IrEffects::default(),
        Term::CallClosure { .. } | Term::TailCallClosure { .. } => IrEffects {
            calls_opaque: true,
            ..IrEffects::default()
        },
        Term::Receive { .. } | Term::ReceiveMatched { .. } => IrEffects {
            scheduler_boundary: true,
            externally_observable: true,
            ..IrEffects::default()
        },
        Term::Halt(_) => IrEffects {
            externally_observable: true,
            halts: true,
            ..IrEffects::default()
        },
        Term::Return(_) | Term::Goto(_, _) => IrEffects::default(),
        Term::If { .. } => IrEffects::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{ExternDecl, ExternId, ExternTy, Var};
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
    fn externs_are_observable_without_scheduler_effects_by_default() {
        let module = module_with_extern("user_extern", ExternTy::Any);
        let effects = prim_effects(
            &module,
            &Prim::Extern(
                ExternId(0),
                vec![crate::fz_ir::ExternArg::fixed(Var(0), ExternTy::Any)],
            ),
        );

        assert!(effects.externally_observable);
        assert!(!effects.scheduler_boundary);
    }

    #[test]
    fn send_is_scheduler_visible() {
        let module = module_with_extern("fz_send", ExternTy::Unit);
        let effects = prim_effects(
            &module,
            &Prim::Extern(
                ExternId(0),
                vec![crate::fz_ir::ExternArg::fixed(Var(0), ExternTy::Any)],
            ),
        );

        assert!(effects.scheduler_boundary);
        assert!(effects.externally_observable);
    }

    #[test]
    fn heap_stats_observes_allocation() {
        let module = module_with_extern("fz_process_heap_alloc_stats", ExternTy::Any);
        let effects = prim_effects(&module, &Prim::Extern(ExternId(0), vec![]));

        assert!(effects.observes_allocation);
        assert!(effects.externally_observable);
    }
}
