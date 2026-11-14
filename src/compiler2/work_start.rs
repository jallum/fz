use fz_engine::{ClientReason, WorkStart};

/// The compiler's reasons for starting a job, observation-only: a reason never
/// changes which job runs or in what order, it only tags each work-start so a
/// running test can distinguish the compiler's sanctioned entry points from
/// anything else. The engine adds its own `ChangedRevisionWake` and
/// `Unclassified` (see `fz_engine::WorkStart`).
///
/// The pull-based northstar (`../pull-based.html`, `.agent/docs/telemetry.md`)
/// allows exactly these ways, with `ChangedRevisionWake`, for a job to start:
///
/// - `Ignition`: an external submission (`World::submit_code`,
///   `submit_module_interface`, `submit_root`) enqueuing the one job that
///   begins that submission's own work. This is the front door, not a job
///   commanding another job.
/// - `ActivationPublished`: `World::demand_recorded_needs` demanding the
///   first analysis of an activation `complete_job` just published --
///   `Activation(key)` without a settled `ActivationAnalyzed(key)` is a
///   recorded need the instant it is published. Root entries and
///   caller-discovered callees both use this one path.
/// - `GateExpansion`: `World::park_on_gates`'s own redirect, whenever a job
///   named by any of the reasons above is not yet runnable: instead of
///   starting that job to discover from inside its own body the same fact it
///   is missing, the still-missing gate's own producer is demanded instead,
///   and the job is parked on it. That producer is a different job than the
///   one that was named, so every caller's gate detour is tallied here,
///   uniformly, never folded into whichever reason asked for the job that
///   turned out to be gated. This is load-bearing for `ActivationPublished`
///   in particular: its own dedup invariant (`work_start_reason_test.rs`)
///   requires exactly one credit per activation, the call that actually
///   places its job on the agenda, never the prerequisites it waited out
///   along the way.
/// - `BlockedWaiterExpansion`: the fact->producer map
///   (`World::demand_fact_producer`) expanding a job's own wait to its
///   single producer the moment that wait is recorded
///   (`World::demand_recorded_needs`, at completion) -- the bounded
///   product-pull's own fact-wait loop
///   (`product_drive::drive_product_fact_wait`) uses this reason too, when
///   the demanded producer is itself runnable; a further gate detour from
///   there is `GateExpansion` instead.
///
/// A start that names none of these is counted under
/// `WorkStart::Unclassified`, which is exactly what trips the running
/// pull-only guard (`work_start_reason_test`'s `pull_only_guard_holds_for_*`
/// cases).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WorkStartReason {
    Ignition,
    ActivationPublished,
    GateExpansion,
    BlockedWaiterExpansion,
}

impl ClientReason for WorkStartReason {
    type Counts = [u64; 4];

    fn slot(self) -> usize {
        self as usize
    }

    fn name(self) -> &'static str {
        match self {
            WorkStartReason::Ignition => "ignition",
            WorkStartReason::ActivationPublished => "activation_published",
            WorkStartReason::GateExpansion => "gate_expansion",
            WorkStartReason::BlockedWaiterExpansion => "blocked_waiter_expansion",
        }
    }
}

impl WorkStartReason {
    /// Every reason a job can start under, in the order telemetry spells
    /// them: the compiler's reasons and the engine's own, interleaved. The
    /// telemetry writer and its readers all iterate this list.
    pub const TELEMETRY_ORDER: [WorkStart<WorkStartReason>; 6] = [
        WorkStart::Client(WorkStartReason::Ignition),
        WorkStart::ChangedRevisionWake,
        WorkStart::Client(WorkStartReason::ActivationPublished),
        WorkStart::Client(WorkStartReason::GateExpansion),
        WorkStart::Client(WorkStartReason::BlockedWaiterExpansion),
        WorkStart::Unclassified,
    ];
}

/// The scheduler's work-start attribution, over the compiler's reasons.
pub type WorkStartTally = fz_engine::WorkStartTally<WorkStartReason>;

/// The scheduler's request accounting, over the compiler's reasons.
pub type WorkLedger = fz_engine::WorkLedger<WorkStartReason>;
