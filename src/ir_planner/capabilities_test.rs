use super::super::fn_types::EffectSummary;

#[test]
fn motion_gate_blocks_on_observable_barriers_not_on_allocation() {
    // Allocation alone is invisible — it is the moment of a barrier observer
    // (print/extern/stats/scheduler/halt/opaque) that forbids relocation.
    assert!(!EffectSummary::default().blocks_return_context_motion());
    assert!(
        !EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        }
        .blocks_return_context_motion()
    );
    for barrier in [
        EffectSummary {
            observable: true,
            ..EffectSummary::default()
        },
        EffectSummary {
            reads_allocation_stats: true,
            ..EffectSummary::default()
        },
        EffectSummary {
            scheduler_visible: true,
            ..EffectSummary::default()
        },
        EffectSummary {
            halts: true,
            ..EffectSummary::default()
        },
        EffectSummary {
            calls_opaque: true,
            ..EffectSummary::default()
        },
    ] {
        assert!(barrier.blocks_return_context_motion());
    }
}
