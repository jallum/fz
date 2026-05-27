use super::fn_types::EffectSummary;
use crate::fz_ir::{Module, Prim, Term};

pub(crate) fn prim_effect_summary(m: &Module, prim: &Prim) -> EffectSummary {
    match prim {
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
        | Prim::BitReaderInit(_) => EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        },
        Prim::Extern(eid, _) => {
            let decl = m.extern_by_id(*eid);
            let reads_allocation_stats = decl.symbol == "fz_process_heap_alloc_stats";
            let scheduler_visible = matches!(
                decl.symbol.as_str(),
                "fz_send" | "fz_spawn" | "fz_spawn_opt" | "fz_self"
            );
            EffectSummary {
                observable: true,
                reads_allocation_stats,
                scheduler_visible,
                halts: decl.ret == crate::fz_ir::ExternTy::Never,
                ..EffectSummary::default()
            }
        }
        _ => EffectSummary::default(),
    }
}

pub(crate) fn term_local_effect_summary(term: &Term) -> EffectSummary {
    match term {
        Term::Receive { .. } | Term::ReceiveMatched { .. } => EffectSummary {
            observable: true,
            scheduler_visible: true,
            ..EffectSummary::default()
        },
        Term::Halt(_) => EffectSummary {
            observable: true,
            halts: true,
            ..EffectSummary::default()
        },
        _ => EffectSummary::default(),
    }
}
