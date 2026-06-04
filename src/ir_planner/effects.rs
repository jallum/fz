use super::fn_types::EffectSummary;
use crate::fz_ir::{ExternTy, Module, Prim, Term};

/// Classifies the local effects of a single primitive: whether it allocates,
/// observes allocation, is externally observable, reaches the scheduler, or
/// halts. Planner capability validation reads this one classifier rather than
/// carrying parallel publication rules.
pub(crate) fn prim_effects(module: &Module, prim: &Prim) -> EffectSummary {
    match prim {
        Prim::Extern(_, eid, _) => {
            let decl = module.extern_by_id(*eid);
            let reads_allocation_stats = decl.symbol == "fz_process_heap_alloc_stats";
            let scheduler_visible = matches!(decl.symbol.as_str(), "fz_send" | "fz_spawn" | "fz_spawn_opt");
            EffectSummary {
                reads_allocation_stats,
                scheduler_visible,
                observable: true,
                halts: decl.ret == ExternTy::Never,
                ..EffectSummary::default()
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
        | Prim::BitReaderInit(_) => EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        },
        Prim::Const(_)
        | Prim::MakeFnRef(_, _)
        | Prim::BinOp(_, _, _)
        | Prim::UnOp(_, _)
        | Prim::ListHead(_)
        | Prim::ListTail(_)
        | Prim::IsEmptyList(_)
        | Prim::IsListCons(_)
        | Prim::TupleField(_, _)
        | Prim::StructField(_, _)
        | Prim::MapGet(_, _)
        | Prim::MatcherMapGet(_, _)
        | Prim::IsMatcherMapMiss(_)
        | Prim::BitReadField { .. }
        | Prim::BitReaderDone(_)
        | Prim::TypeTest(_, _)
        | Prim::Brand(_, _) => EffectSummary::default(),
    }
}

/// Classifies the local effects contributed by a block terminator: closure
/// calls are opaque, receive is a scheduler boundary, halt is externally
/// observable.
pub(crate) fn term_effects(term: &Term) -> EffectSummary {
    match term {
        Term::Call { .. } | Term::TailCall { .. } => EffectSummary::default(),
        Term::CallClosure { .. } | Term::TailCallClosure { .. } => EffectSummary {
            calls_opaque: true,
            ..EffectSummary::default()
        },
        Term::ReceiveMatched { .. } => EffectSummary {
            scheduler_visible: true,
            observable: true,
            ..EffectSummary::default()
        },
        Term::Halt(_) => EffectSummary {
            observable: true,
            halts: true,
            ..EffectSummary::default()
        },
        Term::Return(_) | Term::Goto(_, _) => EffectSummary::default(),
        Term::If { .. } => EffectSummary::default(),
    }
}

#[cfg(test)]
#[path = "effects_test.rs"]
mod effects_test;
