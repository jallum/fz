//! The running pull-only guard: every job entering the agenda on a
//! production-driven path must be attributable to a sanctioned
//! `WorkStartReason` (see `scheduler.rs`), and no producer may discover work
//! by scanning the whole fact table (`Scheduler::fact_keys`).
//!
//! Each case drives one fixture through the real front door (`submit_code` +
//! `submit_root`, exactly the CLI/product path) to its backend product and
//! reads the World's cumulative `WorkStartTally`. The guard asserts three
//! things:
//!
//! - `unsanctioned_work_starts() == 0` — no job entered the agenda under
//!   `WorkStartReason::Unclassified`. A future enqueue call site that forgets
//!   to pass a sanctioned reason — the shape a reintroduced `follow_up`-style
//!   push would take — lands here by construction and trips this red.
//! - `root_scans == 0` — no producer discovered work by scanning the whole
//!   fact table.
//! - `ignition == 2` — `Ignition` tags ONLY the true external front-door
//!   work-starts (one `submit_code`'s `IndexCode`, one `submit_root`'s
//!   `SeedRoot`). This is the soundness assertion: it fails if any internal
//!   (mid-job) caller ever drives a job as `Ignition` again — the exact hole
//!   this guard originally exposed in `ensure_runtime_module` (a runtime
//!   module minted mid-job via `submit_code`, mislabeled the external front
//!   door). With that push eliminated, `unsanctioned == 0` holds because
//!   there is no misclassified push left, not because one is hidden under
//!   `Ignition`.
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

/// One `submit_code` (its `IndexCode`) plus one `submit_root` (its `SeedRoot`)
/// are the only external ignitions for a single-file, single-root fixture.
/// `ScopeCode` is only enqueued by `submit_code` when a root already exists,
/// which it does not at `submit_code` time here (the root is submitted after),
/// so it is not an ignition — it is pulled.
const EXTERNAL_IGNITIONS: u64 = 2;

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
        tally.root_scans, 0,
        "{name}: {} whole-fact-table scan(s) were taken -- a root-scan discovered work instead of \
         following a named dependency",
        tally.root_scans,
    );
    assert_eq!(
        tally.drain_discovery_sweeps, 0,
        "{name}: {} global drain-discovery sweep(s) were taken instead of following exact pending indexes",
        tally.drain_discovery_sweeps,
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
        "fixtures2/00181_enum_reduce_operator_ref.fz",
        include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_macro_quote_unquote() {
    assert_pull_only(
        "fixtures2/00111_macro_quote_unquote.fz",
        include_str!("../../fixtures2/00111_macro_quote_unquote.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_nested_call_from_outside_module() {
    assert_pull_only(
        "fixtures2/00059_nested_call_from_outside.fz",
        include_str!("../../fixtures2/00059_nested_call_from_outside.fz"),
    );
}

#[test]
fn pull_only_guard_holds_for_protocol_impl_dispatch() {
    assert_pull_only(
        "fixtures2/00272_protocol_impl_dispatch.fz",
        include_str!("../../fixtures2/00272_protocol_impl_dispatch.fz"),
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
    telemetry.attach_raw_event2::<super::World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            let mut source_work = observed_source_work.borrow_mut();
            source_work.0 += 1;
            source_work.1 += u64::from(matches!(completion.job, Job::ScopeCode(_)));
            source_work.2 += u64::from(matches!(completion.job, Job::DefineModule(_)));
            source_work.3 += u64::from(matches!(completion.job, Job::DeriveExecutableFacts(_)));
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
                        super::FactUse::Current(super::DependencyKey::Fact(FactKey::RuntimeDemandInputs(_))) => 3,
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
        name: Some("fixtures2/00420_enum_take_drop_split.fz".to_string()),
        text: include_str!("../../fixtures2/00420_enum_take_drop_split.fz").to_string(),
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
        // own demand evaluation.
        // Direct callable observations change the continuation-ladder order
        // without changing its identities or terminal artifacts. Every extra
        // round remains attached to the fact movement that caused it.
        (3822, 11, 19, 232),
        "ordinary generic helper work has the exact source/module/executable-fact census"
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
        // The same nine continuation rounds publish one retained changed
        // revision each; they remain non-demand work because the frontier has
        // already selected their exact demand keys.
        1201,
        "ordinary generic helper facts have the exact non-demand changed-revision census",
    );
    assert_eq!(
        starts.blocked_waiter_expansion - demanded_formula_keys.len() as u64,
        // fz-5xp.30: 1162 -> 1184. The ordinary generic result/status
        // contracts retain twenty-two more blocked prerequisite waits.
        // The typed `==` clauses retain blocked prerequisite waits of their own.
        1113,
        "the blocked-waiter census includes every ordinary generic helper prerequisite",
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
        // own completion woken on that same exact cause.
        (1169, 937, [58, 232, 165, 482, 0]),
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
        (
            starts.ignition,
            starts.activation_frontier,
            starts.unclassified,
            starts.root_scans,
            starts.drain_discovery_sweeps
        ),
        // fz-5xp.30: 261 -> 265. Four ordinary generic result/status helper
        // activations enter through the same attributed frontier.
        (2, 265, 0, 0, 0),
        "ordinary generic helper activations preserve the pull-only frontier",
    );

    let world = compiler.world();
    let frontier_analyses = world.activation_frontier_starts();
    assert_eq!(
        starts.activation_frontier,
        frontier_analyses.len() as u64,
        "the session tally must count the exact typed frontier starts",
    );
    let frontier_analyses = frontier_analyses.iter().cloned().collect::<HashSet<_>>();
    assert_eq!(
        frontier_analyses.len(),
        starts.activation_frontier as usize,
        "an activation may enter through the frontier only once",
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
