//! The running pull-only guard: every job entering the agenda on a
//! production-driven path must be attributable to a sanctioned
//! `WorkStartReason` (see `scheduler.rs`), and no producer may discover work
//! by scanning the whole fact table (`Scheduler::fact_keys`).
//!
//! Each case drives one fixture through the real front door (`submit_code` +
//! `submit_root`, exactly the CLI/product path) to its backend product and
//! reads the World's cumulative `WorkStartTally`. The guard asserts two
//! things (a whole-fact-table scan is no longer a thing a producer can even
//! reach for: `Scheduler::fact_keys` does not exist):
//!
//! - `unsanctioned_work_starts() == 0` — no job entered the agenda under
//!   `WorkStartReason::Unclassified`. A future enqueue call site that forgets
//!   to pass a sanctioned reason — the shape a reintroduced `follow_up`-style
//!   push would take — lands here by construction and trips this red.
//! - `ignition == 1` — `Ignition` tags ONLY the true external front-door
//!   work-starts that actually place a job on the agenda. For a single-file,
//!   single-root fixture that is `submit_code`'s `IndexCode` alone:
//!   `submit_root`'s own first demand always finds `SeedRoot`'s
//!   `FunctionDefined` gate missing (the root function is never defined yet
//!   at that instant), so it is a gate detour -- `GateExpansion` -- not a
//!   bare `SeedRoot` start. This is the soundness assertion: it fails if any
//!   internal (mid-job) caller ever drives a job as `Ignition` again — the
//!   exact hole this guard originally exposed in `ensure_runtime_module` (a
//!   runtime module minted mid-job via `submit_code`, mislabeled the
//!   external front door). With that push eliminated, `unsanctioned == 0`
//!   holds because there is no misclassified push left, not because one is
//!   hidden under `Ignition`.
//!
//! NOTE ON THE GUARD'S BOUNDARY: this catches an *untagged* enqueue (a new
//! call site that omits a reason → `Unclassified`). It does not by itself
//! catch a deliberately *mislabeled* push (a new internal caller that passes,
//! say, `Ignition` by hand). The `ignition == N` assertion is the backstop
//! for exactly that class: if the external ignition count ever exceeds the
//! true front-door count, an internal caller mislabeled its work-start.

use std::collections::HashSet;

use super::drive::Job;
use super::{CodeSubmission, Compiler2, ExecutableNeed, FactKey, FactUse, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;

/// `submit_code`'s own `IndexCode` is the only external ignition for a
/// single-file, single-root fixture. `ScopeCode` is only enqueued by
/// `submit_code` when a root already exists, which it does not at
/// `submit_code` time here (the root is submitted after), so it is not an
/// ignition — it is pulled. `submit_root`'s own first demand always finds
/// `SeedRoot`'s `FunctionDefined` gate missing at this instant -- nothing has
/// driven yet, so the root function is never defined -- so it is always a
/// gate detour (`GateExpansion`), never a bare `SeedRoot` start.
const EXTERNAL_IGNITIONS: u64 = 1;

fn assert_pull_only(name: &str, source: &str) {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let tally = compiler
        .drive_root_backend_work_starts(root_id)
        .unwrap_or_else(|error| panic!("{name} should drive to its backend product: {error}"));

    assert_eq!(
        tally.unsanctioned_work_starts(),
        0,
        "{name}: {} job(s) entered the agenda without an attributable sanctioned WorkStartReason \
         -- this is exactly the shape a reintroduced push would take",
        tally.unsanctioned_work_starts(),
    );
    assert_eq!(
        tally.ignition, EXTERNAL_IGNITIONS,
        "{name}: Ignition fired {} times but only {EXTERNAL_IGNITIONS} external front-door \
         ignitions exist (one submit_code, one submit_root) -- any excess is an internal \
         (mid-job) caller mislabeling its work-start as the external front door",
        tally.ignition,
    );
}

#[test]
fn pull_only_guard_holds_for_quicksort() {
    assert_pull_only(
        "fixtures2/00001_quicksort_plus_foo.fz",
        include_str!("../../fixtures2/00001_quicksort_plus_foo.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_enum_reduce_operator_ref() {
    assert_pull_only(
        "fixtures/00181_enum_reduce_operator_ref.fz",
        include_str!("../../fixtures/00181_enum_reduce_operator_ref.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_macro_quote_unquote() {
    assert_pull_only(
        "fixtures/00111_macro_quote_unquote.fz",
        include_str!("../../fixtures/00111_macro_quote_unquote.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_nested_call_from_outside_module() {
    assert_pull_only(
        "fixtures/00059_nested_call_from_outside.fz",
        include_str!("../../fixtures/00059_nested_call_from_outside.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_protocol_impl_dispatch() {
    assert_pull_only(
        "fixtures/00272_protocol_impl_dispatch.fz",
        include_str!("../../fixtures/00272_protocol_impl_dispatch.fz"),
    );
}

/// fz-tfn.5: root entries and caller-discovered callees are ordinary published
/// `Activation` edges. Their analyses must enter through the same frontier,
/// with no root-specific ignition path beside it. The root's `SeedRoot`
/// conclusion must retain the exact keying dependencies before its published
/// activation enters that frontier.
#[test]
fn root_entries_and_caller_discovered_callees_share_the_activation_frontier() {
    let telemetry = ConfiguredTelemetry::new();
    let macro_definition_consumers = std::rc::Rc::new(std::cell::RefCell::new(HashSet::<Job>::new()));
    let observed_macro_consumers = std::rc::Rc::clone(&macro_definition_consumers);
    let source_work = std::rc::Rc::new(std::cell::RefCell::new((0_u64, 0_u64, 0_u64, 0_u64)));
    let observed_source_work = std::rc::Rc::clone(&source_work);
    let demand_work = std::rc::Rc::new(std::cell::RefCell::new((0_u64, 0_u64, HashSet::<Job>::new())));
    let observed_demand_work = std::rc::Rc::clone(&demand_work);
    let demand_wake_causes = std::rc::Rc::new(std::cell::RefCell::new([0_u64; 5]));
    let observed_demand_wake_causes = std::rc::Rc::clone(&demand_wake_causes);
    let analyzed_activations = std::rc::Rc::new(std::cell::RefCell::new(Vec::<super::ActivationKey>::new()));
    let observed_analyzed_activations = std::rc::Rc::clone(&analyzed_activations);
    telemetry.attach_raw_event2::<super::World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            let mut source_work = observed_source_work.borrow_mut();
            source_work.0 += 1;
            source_work.1 += u64::from(matches!(completion.job, Job::ScopeCode(_)));
            source_work.2 += u64::from(matches!(completion.job, Job::DefineModule(_)));
            source_work.3 += u64::from(matches!(completion.job, Job::DeriveExecutableFacts(_)));
            if let Job::AnalyzeActivation(activation) = &completion.job {
                observed_analyzed_activations.borrow_mut().push(activation.clone());
            }
            let mut demand_work = observed_demand_work.borrow_mut();
            match &completion.job {
                Job::DeriveRuntimeDemand(_) => {
                    demand_work.0 += 1;
                    demand_work.2.insert(completion.job.clone());
                }
                Job::DeriveCallableConstructionTarget(_) => {
                    demand_work.2.insert(completion.job.clone());
                }
                _ => {}
            }
            for wake in &completion.wakes {
                if wake.disposition == super::WakeDisposition::Enqueued
                    && let super::DependencyKey::Fact(FactKey::FunctionDefined(function)) = wake.cause.fact()
                    && world.function_definition(*function).1.is_macro
                {
                    observed_macro_consumers.borrow_mut().insert(wake.job.clone());
                }
                if wake.disposition == super::WakeDisposition::Enqueued
                    && matches!(wake.job, Job::DeriveRuntimeDemand(_))
                {
                    demand_work.1 += 1;
                    let cause = match &wake.cause {
                        super::FactUse::Current(super::DependencyKey::Fact(FactKey::CallableConstructionTarget(_))) => {
                            0
                        }
                        super::FactUse::Settled(super::DependencyKey::Fact(FactKey::ExecutableFacts(_))) => 1,
                        super::FactUse::Current(super::DependencyKey::Fact(FactKey::RuntimeDemandInput(_))) => 2,
                        super::FactUse::Current(super::DependencyKey::Fact(FactKey::RuntimeDemandInputs(_)))
                        | super::FactUse::Concluded(super::DependencyKey::Fact(FactKey::RuntimeDemandInputs(_))) => 3,
                        super::FactUse::Current(super::DependencyKey::Fact(FactKey::ExecutableFacts(_))) => 4,
                        cause => panic!("unexpected RuntimeDemand wake prerequisite: {cause:?}"),
                    };
                    observed_demand_wake_causes.borrow_mut()[cause] += 1;
                }
            }
        },
    );
    let macro_product_consumers = std::rc::Rc::new(std::cell::RefCell::new(HashSet::<Job>::new()));
    let observed_product_consumers = std::rc::Rc::clone(&macro_product_consumers);
    telemetry.attach_raw_event1::<super::AppliedStep<Job, super::DependencyKey>, _>(
        &["fz", "compiler2", "work_graph", "dependencies_moved"],
        move |_, _, _, step| {
            for wake in &step.wakes {
                if wake.disposition == super::WakeDisposition::Enqueued
                    && let super::DependencyKey::Product(address) = wake.cause.fact()
                    && matches!(address.key, super::ProductKey::RootBackendProduct(_))
                {
                    observed_product_consumers.borrow_mut().insert(wake.job.clone());
                }
            }
        },
    );
    let mut compiler = Compiler2::new(telemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/00420_enum_take_drop_split.fz".to_string()),
        text: include_str!("../../fixtures/00420_enum_take_drop_split.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let starts = compiler
        .drive_root_backend_work_starts(root)
        .expect("the activation-edge fixture should settle its backend product");
    let (demand_completions, demand_wake_starts, demanded_formula_keys) = &*demand_work.borrow();
    // fz-5xp.30: 3 -> 2. One generic arithmetic helper path reaches its
    // result/status fact directly, rather than becoming a macro-definition
    // consumer; the retained consumers still take both exact dependencies.
    assert_eq!(macro_definition_consumers.borrow().len(), 2);
    assert_eq!(
        *macro_definition_consumers.borrow(),
        *macro_product_consumers.borrow(),
        "the two macro consumers resume on their definition and then on their exact retained content"
    );
    assert_eq!(
        *source_work.borrow(),
        // Applied work steps in total, then the `ScopeCode`, `DefineModule`
        // and `DeriveExecutableFacts` steps among them, for this one fixture
        // compiled to its backend product.
        //
        // What the shape of the numbers says: the fixture reaches `==`, `<`
        // and `>`, whose Kernel definitions carry a typed clause per numeric
        // pair plus an `any`/`any` catch-all that calls `compare/2`. Every
        // operator site lowers and plans that whole family, which is why the
        // total is large; the module and executable-fact tallies stay small
        // because the fixture's operands are all integers, so each site
        // settles on one clause and the catch-all is never reached. Tuple-
        // field demands join as prefixes, so a field one consumer reads stays
        // distinct from a field another ignores and each such field earns its
        // own demand evaluation. The drain arbiter certifies a whole clean
        // cone at once instead of one layer per stall, so the executable-fact
        // tally no longer double-counts layers re-arbitrated after they were
        // already proven final. Publishing a function's source from the walk
        // that scoped it removes one source job per reached function.
        // A job gated on a fact its subject already carries never starts to
        // discover that fact missing, then wake once the fact lands
        // (`Job::missing_gates`).
        // fz-afu.2: 3170 -> 3168. `World::submit_root` no longer enqueues
        // `SeedRoot` directly; it demands `RootEntry` through the same
        // gate-checked path every other job uses. `SeedRoot(main)` used to
        // run 3 times -- an ignition run that discovered its own gate, one
        // more rediscovering the second, then the real run -- and now runs
        // once, removing its two blocked-only applied steps.
        // fz-afu.3: 3168 -> 2794. A run missing a callee's answer waits for it
        // instead of concluding on `ignore`, so no caller re-runs to revise
        // what it concluded.
        // fz-afu.10: 2794 -> 2797. DeriveInputDemand falls 197 -> 190: a
        // caller reads each callee's concluded answer instead of walking the
        // callee's body. AnalyzeActivation rises 888 -> 898. Four of those
        // runs are `InputDemand` wakes: a protocol callback's answer covers
        // the implementations defined so far, and with callers now reading
        // that answer, each new implementation moves more of them, which
        // re-keys their activations. The other six are callee `ReturnType`
        // (369 -> 373 enqueued, 25 -> 26 coalesced) and `Recursive`
        // (46 -> 47) wakes.
        // fz-afu.11: 2797 -> 2771. The callback no longer joins over
        // `ProtocolDispatch`'s arms: it is a leaf with no forwards and no
        // protocol reads, answered from its own arity alone. An
        // implementation defined later never revises it or the callers built
        // on it, so the four extra `InputDemand` wakes fz-afu.10 added above
        // are gone with the join.
        // fz-p8p.19: 2771 -> 2747. The exhaustiveness check that used to run
        // per function head is gone; redundancy is checked from the compiled
        // dispatch plan instead, which removes its own source job from every
        // function that declared a contract.
        // fz-xxd.3: 2747 -> 2761. +18 DeriveFunctionContract: eighteen Kernel
        // operator externs this fixture lowers but never calls. Their
        // declarations used to be resolved a second time inside
        // `LowerFunction`, where no job was counted; now their own contract
        // job resolves them once. AnalyzeActivation falls by 4.
        // fz-xxd.11: 2761 -> 2715 -> 2696, net of LowerFunction -28,
        // PlanEntryDispatch -18, DeriveFunctionContract -18,
        // AnalyzeActivation -19. The eighteen Kernel operator externs this
        // fixture never calls no longer get a LowerFunction or
        // PlanEntryDispatch job at all, and -- since nothing needs their
        // body to compute static callees any more -- most no longer get
        // their FunctionContract demanded either. AnalyzeActivation's own
        // fall is `analyze_activation_gates` (`Job::missing_gates`): each
        // called extern's activation used to start once blocked on its own
        // `EntryDispatch`, changing nothing, before its real run; the gate
        // now holds the job back until `EntryDispatch` (and, for a
        // non-extern, `LoweredBody`) already exists, so the ten blocked
        // extern runs never happen, and nine more ordinary-caller runs a
        // caller no longer needs to re-settle after them fall with them.
        // fz-afu.13: 2696 -> 2688. A need now starts its producer the instant
        // it is recorded instead of waiting for a later drain sweep to
        // discover it; the eight fewer applied steps are blocked-only runs
        // the sweep used to take before its real run, now skipped entirely.
        (2688, 9, 19, 232),
        "ordinary generic helper work has the exact source/module/executable-fact census"
    );
    // Every applied work step is a run, and every run is charged to exactly
    // one `WorkStartReason` the moment `Scheduler::record_run_start` commits
    // it -- never twice, since a job popped and parked without running is
    // charged nothing until the wake that later re-queues it runs instead.
    assert_eq!(
        starts.total(),
        source_work.borrow().0,
        "the work-start tally charges exactly one reason per applied run",
    );
    // Two consumers wait for macro definitions directly; content readiness
    // then wakes those same consumers through the retained product dependency.
    assert_eq!(
        starts.changed_revision_wake - demand_wake_starts,
        // fz-5xp.30: 1430 -> 1447. The generic result/status helper facts
        // publish sixteen additional non-demand changed revisions.
        // The typed `==` clauses and their externs publish non-demand changed
        // revisions of their own.
        // Each ordering operator's `any`/`any` clause publishes one non-demand
        // changed revision, and this fixture reaches `<` and `>`.
        // A function's source and its consumable fact are one publication now,
        // so each reached body costs one changed revision instead of two.
        // A job gated on a fact its subject already carries never starts to
        // discover that fact missing, then wake once the fact lands
        // (`Job::missing_gates`).
        // fz-afu.2: 781 -> 779. `SeedRoot(main)`'s two now-eliminated
        // blocked-only runs (see above) each published one non-demand
        // changed revision on their way to discovering their own gate.
        // fz-afu.10: 779 -> 757. DeriveInputDemand's wakes fall 94 -> 63: the
        // 84 it took from callee `EntryDispatch` and `StaticCallees` facts,
        // one per callee its walk discovered, become 57 wakes on concluded
        // callee answers, and `ProtocolDispatch` shifts wake it 10 -> 6 times.
        // AnalyzeActivation's nine extra runs (see above) add nine.
        // fz-afu.11: 757 -> 731. `ProtocolDispatch` no longer shifts the
        // callback's wake at all -- the callback reads no protocol fact, so
        // those six wakes and the extra `InputDemand` wakes they fed (above)
        // both go with the join.
        // fz-p8p.19: 731 -> 707. The exhaustiveness check that used to run
        // per function head is gone; redundancy is checked from the compiled
        // dispatch plan instead, which removes its own changed revision from
        // every function that declared a contract.
        // fz-xxd.3: 707 -> 705.
        // fz-xxd.11: 705 -> 719 -> 702. Removing the caller-side wait on an
        // extern callee's `LoweredBody` (it has none) briefly raised this to
        // 719: some caller activations used to wait on that `LoweredBody`
        // together with the callee's `EntryDispatch`/`ReturnType`, and
        // AND-semantics coalesced their settlement into one wake attributed
        // to whichever fact -- always the FunctionContract-gated
        // LowerFunction publishing `LoweredBody` late -- settled last; with
        // that fact out of the wait set, the same two settle events
        // (EntryDispatch, then ReturnType) surfaced as two wakes instead of
        // one. `analyze_activation_gates` (`Job::missing_gates`) removes the
        // root cause instead: an extern's own `AnalyzeActivation` no longer
        // starts before its `EntryDispatch` exists, so it never wakes again
        // on that fact once the gate is satisfied, and the ten new
        // `EntryDispatch` wakes fz-xxd.11 measured are gone with it, along
        // with the coalescing artifact that split them.
        // fz-afu.13: 702 -> 1045. A need now starts its producer the instant
        // it is recorded instead of waiting for a drain sweep, so a caller
        // with many call sites -- this fixture's `main/0` makes thirty-eight
        // `dbg` calls -- wakes once per callee answer as each lands, rather
        // than once per drain after a sweep happened to let several land
        // first (see `main/0`'s own repeated analysis, below). The reason
        // tally itself was previously double-counting
        // a job popped, found gated, and re-enqueued later (every `enqueue`
        // path now records its reason and charges it once, at the moment a
        // job is actually popped to run, in `Scheduler::record_run_start`);
        // correcting that tally is what moves this number from a transient
        // 1156 (the inflated, double-counted reading) to this exact 1045.
        1045,
        "ordinary generic helper facts have the exact non-demand changed-revision census",
    );
    assert_eq!(
        starts.blocked_waiter_expansion,
        // fz-5xp.30: 1162 -> 1184 (as the count beyond the 304-key demand
        // frontier, below). The ordinary generic result/status contracts
        // retain twenty-two more blocked prerequisite waits.
        // The typed `==` clauses retain blocked prerequisite waits of their own.
        // A consumer of a function's source no longer waits behind a copy job,
        // so each reached body retains one blocked prerequisite fewer.
        // fz-afu.2: 1113 -> 1103. `SeedRoot(main)`'s gate chain used to be
        // rediscovered hop by hop through the blocked-waiter sweep; it now
        // demands through `submit_root`'s own ignition call and the
        // `root_frontier` standing demand instead, so those hops move off
        // this count rather than adding to it.
        // fz-afu.10: 1103 -> 1127, all of it DeriveInputDemand (102 -> 126
        // starts). A caller composes from its callees' answers, so each
        // callee its walk used to cross inline now derives an answer of its
        // own, started by the caller that waits for it: 103 -> 127 distinct
        // functions. Those starts replace re-runs rather than adding to them
        // -- DeriveInputDemand runs fall 197 -> 190.
        // fz-xxd.3: 1127 -> 1145. An extern's `LowerFunction` is gated on its
        // `FunctionContract`, so each of the eighteen new contract jobs above
        // is started by expanding that blocked waiter to its producer.
        // fz-xxd.11: 1145 -> 1071 -> 426 (still above the demand frontier's
        // 304 keys). `AnalyzeActivation` now gates on `FunctionDefined`,
        // `EntryDispatch` and (for a non-extern) `LoweredBody`
        // (`analyze_activation_gates`), so it never starts to discover one of
        // those three missing and then wait for it -- the blocked-waiter
        // sweep first had that many fewer stalled jobs to expand
        // (1145 -> 1071). Uniformly tallying every gate detour under
        // `GateExpansion`, not only `ActivationFrontier`'s, then moves the
        // 645 detours this blocked-waiter sweep itself still triggered --
        // a still-missing gate's own producer getting demanded, the same
        // event `GateExpansion` already named elsewhere -- out of this count
        // (1071 -> 426, i.e. 730 raw before the 304-key subtraction below).
        // fz-afu.13: 730 -> 282, now BELOW the 304-key demand frontier for
        // the first time. The drain-time blocked-waiter sweep this reason
        // used to also count is gone entirely (`World::demand_recorded_needs`
        // expands each wait once, the moment it is recorded, instead of a
        // later sweep revisiting every still-blocked job); what is left is
        // only the direct expansions a completion's own waits trigger, which
        // no longer dominates the demand frontier's own key count, so the
        // two counts are compared directly instead of by subtraction.
        282,
        "the blocked-waiter census includes only the prerequisites each completion's own waits expand",
    );
    assert_eq!(
        (*demand_completions, *demand_wake_starts, *demand_wake_causes.borrow()),
        // `DeriveRuntimeDemand` completions, the wakes that enqueued them,
        // and those wakes split by the prerequisite that caused each one:
        // construction target, settled executable facts, one exact runtime-
        // demand input, the whole input vector, and unclassified.
        //
        // The last slot is zero because every wake names the fact that moved.
        // The exact-input slot carries the wakes the whole-input-vector slot
        // would otherwise absorb: a formula that reads one target's inputs
        // wakes on that input alone. Tuple-field demands join as prefixes, so
        // fields distinct consumers read stay distinct, and each one is its
        // own completion woken on that same exact cause. The drain arbiter's
        // whole-cone certification removes the re-arbitration wakes that used
        // to inflate the whole-input-vector slot. A job gated on a fact its
        // subject already carries never starts to discover that fact
        // missing, then wake once the fact lands (`Job::missing_gates`) --
        // the settled-executable-facts slot drops to zero since that wake
        // was entirely the discovery bounce.
        // fz-afu.3: (937, 705) -> (563, 331), every cause slot falling. A run
        // missing a callee's answer waits for it instead of concluding on a
        // guess, so the wakes that re-ran callers to revise their guesses
        // are gone. A wait for a callee's concluded answer is counted in the
        // whole-input-vector slot, since it names that vector.
        // fz-afu.13: (563, 331, [24, 0, 79, 228, 0]) -> (562, 562,
        // [24, 232, 79, 227, 0]). One fewer `DeriveRuntimeDemand` completion:
        // a formula that used to settle in two runs under the drain sweep's
        // batching now settles in one, its need started the instant it was
        // recorded. The settled-executable-facts slot, zero since xxd.11
        // removed the discovery bounce for `AnalyzeActivation`, reappears
        // here for `DeriveRuntimeDemand`: starting a formula's producer the
        // moment its need is recorded can still start it before
        // `ExecutableFacts` itself is settled, so it wakes again once that
        // settles, the same discovery-bounce shape in a different job. The
        // whole-input-vector slot falls by one, the single wake the new
        // settled-executable-facts slot intercepts earlier than before.
        (562, 562, [24, 232, 79, 227, 0]),
        "every demand completion and ordinary helper wake retains its precise cause",
    );
    assert_eq!(
        demanded_formula_keys.len(),
        // fz-5xp.30: the ordinary generic result/status boundary contributes
        // four exact RuntimeDemand/construction-target keys.
        304,
        "the demand frontier retains every ordinary generic helper key",
    );
    assert_eq!(
        (starts.ignition, starts.activation_published, starts.unclassified),
        // fz-5xp.30: 261 -> 265. Four ordinary generic result/status helper
        // activations enter through the same attributed frontier.
        // fz-afu.10: 265 -> 266. `Enum.drop_positive/2` is now analyzed once
        // while its accumulator is still only `empty_list()`, so it names an
        // intermediate `Enum.drop_positive_finish/1` activation,
        // `({empty_list(), int})`, before the settled `({list(int), int})`.
        // `drop_positive_finish/1`'s own input demand is derived once,
        // identically; only the order its caller runs in moved.
        // fz-xxd.3: 266 -> 264. `Kernel.dbg/1`, `Kernel.fz_dbg_value/1`, and
        // the `{empty_list(), int}` shapes of `Enum.drop_positive_finish/1`
        // and `Enum.take_positive_finish/1` are no longer activated;
        // `Range.reduce_while_step/6` and `List.reduce_while_step/3` each gain
        // one activation.
        // fz-xxd.11: activation_frontier 264 -> 276 -> 266.
        // `AnalyzeActivation` now gates on `FunctionDefined`, `EntryDispatch`
        // and (for a non-extern) `LoweredBody` (`analyze_activation_gates`).
        // Ten called Kernel operator externs -- `fz_dbg_value`, `fz_panic`,
        // and `fz_op_{add,sub,div,rem,lt,gt,eq,eq_ii}` -- reach the frontier
        // before their own `EntryDispatch` exists, so each was credited twice
        // under the raw `started>0` count: once when its missing gate was
        // expanded, again once the gate cleared and its `AnalyzeActivation`
        // was actually queued (confirmed by tracing every credited key: ten
        // repeat, no others). A still-missing gate's own producer is a
        // different job than the activation waiting on it, so it is now
        // tallied under `GateExpansion` instead
        // (`World::demand_producer_if_needed`), and the frontier credits only
        // the call that actually places the activation's own job on the
        // agenda. That retires the false ten: 276 raw credits, 266 distinct
        // activations. The two above fz-xxd.3's 264 predate this fix --
        // reverting `require_callee_prerequisites` and both `keying.rs` gates
        // and re-measuring still gives 266 -- so `analyze_activation_gates`
        // itself, landed after fz-xxd.3 pinned 264, is what changed which
        // activations this fixture's frontier discovers. fz-afu.13 leaves
        // 266 unchanged -- the set of activations recorded is the same; only
        // when each one's analysis starts moved earlier.
        // fz-xxd.11: ignition 2 -> 1. `submit_root`'s own first demand always
        // finds `SeedRoot`'s `FunctionDefined` gate missing -- the root
        // function is never defined yet at that instant -- so it was always
        // a gate detour, not a bare `SeedRoot` start; `GateExpansion` now
        // covers that detour uniformly for every reason, not only
        // `ActivationFrontier`'s, so it moves out of `Ignition` here too.
        // Only `submit_code`'s own `IndexCode` remains a bare ignition.
        // fz-afu.13: activation_frontier is renamed activation_published --
        // every analysis it credits is now demanded the instant it is
        // recorded (`World::demand_recorded_needs`) rather than discovered by
        // a later drain sweep. 266 -> 265: one fewer distinct activation
        // reaches the frontier at all (see the census below). Of the 265
        // that do, only 255 place their own job on the agenda directly; the
        // other ten are each still gated on their own `EntryDispatch`, so the
        // call that actually starts each one is the gate detour that clears
        // that gate, tallied under `GateExpansion` rather than this reason
        // (`World::demand_producer_if_needed`'s blocked branch now records
        // the reason current when a job is popped to run, not the reason it
        // was first demanded under -- see `Scheduler::record_run_start`). Ten
        // is also the count xxd.11 named for the same shape of gate detour,
        // one layer up (raw credits vs. distinct activations); the two tens
        // are not independently confirmed to be the same ten functions.
        (1, 255, 0),
        "ordinary generic helper activations preserve the pull-only frontier",
    );

    let world = compiler.world();
    let analyzed_activations = analyzed_activations.borrow();
    // fz-xxd.11 (base): every distinct activation is analyzed exactly once --
    // 266 completions, 266 distinct keys, no repeats at all.
    // fz-afu.13: 266 -> 875 completions over 265 distinct keys (below), a
    // repeat rate this test did not previously have to state because the
    // assertion reaching this far always failed first on an earlier number
    // in this same test. `main/0` alone accounts for 45 of those completions
    // (one activation key, re-run 45 times); it makes thirty-eight `dbg`
    // calls, each reading one callee's answer, and a need started the
    // instant it is recorded wakes `main/0` again on each answer landing
    // rather than once after a drain let several land together. This is a
    // genuine, measured, reproducible cost of removing the drain-time
    // batching the sweep used to provide for free, surfaced here rather than
    // hidden behind a pin that never got this far before; it has not been
    // weighed against fz-afu.13's own net job-count win (2696 -> 2688, still
    // a decrease) or diagnosed against the separately-tracked schedule-
    // dependent convergence behavior already known on this exact fixture.
    assert_eq!(
        analyzed_activations.len(),
        875,
        "the fixture's total AnalyzeActivation completions, repeats included",
    );
    let frontier_analyses = analyzed_activations.iter().cloned().collect::<HashSet<_>>();
    assert_eq!(
        frontier_analyses.len(),
        265,
        "the demand frontier's distinct activations, deduplicated across repeats",
    );

    let root_entry = world.root_entry(root);
    let (root_claims, root_reads) = world.standing_claims_and_reads(&Job::SeedRoot(root));
    assert!(root_reads.contains(&FactUse::settled(FactKey::Recursive(root_entry.function))));
    assert!(root_reads.contains(&FactUse::settled(FactKey::InputDemand(root_entry.function))));
    let mut root_activations = root_claims.into_iter().filter_map(|fact| match fact {
        FactKey::Activation(key) => Some(key),
        _ => None,
    });
    let root_activation = root_activations
        .next()
        .expect("SeedRoot must publish its keyed activation");
    assert!(
        root_activations.next().is_none(),
        "SeedRoot must publish one entry activation"
    );
    assert!(
        frontier_analyses.contains(&root_activation),
        "the InputDemand-keyed root activation must enter through the shared frontier",
    );
    assert!(
        frontier_analyses
            .iter()
            .any(|activation| activation.function != root_entry.function),
        "caller-discovered callees must use the same frontier as the root entry",
    );
}
