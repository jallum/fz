//! The running pull-only guard: every job entering the agenda on a
//! production-driven path must be attributable to a sanctioned
//! `WorkStartReason` (see `crates/fz-engine/src/scheduler.rs`), and no producer may discover work
//! by scanning the whole fact table (`Scheduler::fact_keys`).
//!
//! Each case drives one fixture through the real front door (`submit_code` +
//! `submit_root`, exactly the CLI/product path) to its backend product and
//! reads the World's cumulative `WorkStartTally`. The guard asserts two
//! things (a whole-fact-table scan is no longer a thing a producer can even
//! reach for: `Scheduler::fact_keys` does not exist):
//!
//! - `unsanctioned_work_starts() == 0` — no job entered the agenda under
//!   `WorkStart::Unclassified`. A future enqueue call site that forgets
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

use crate::fast_hash::HashSet;

use super::drive::Job;
use super::{CodeSubmission, Compiler2, ExecutableNeed, FactKey, RootSubmission};
use crate::compiler2::WorkStartReason;
use crate::telemetry::ConfiguredTelemetry;
use fz_engine::{FactUse, WorkStart};

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
        tally[WorkStartReason::Ignition.into()],
        EXTERNAL_IGNITIONS,
        "{name}: Ignition fired {} times but only {EXTERNAL_IGNITIONS} external front-door \
         ignitions exist (one submit_code, one submit_root) -- any excess is an internal \
         (mid-job) caller mislabeling its work-start as the external front door",
        tally[WorkStartReason::Ignition.into()],
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
    let macro_definition_consumers = std::rc::Rc::new(std::cell::RefCell::new(HashSet::<Job>::default()));
    let observed_macro_consumers = std::rc::Rc::clone(&macro_definition_consumers);
    let source_work = std::rc::Rc::new(std::cell::RefCell::new((0_u64, 0_u64, 0_u64, 0_u64)));
    let observed_source_work = std::rc::Rc::clone(&source_work);
    let demand_work = std::rc::Rc::new(std::cell::RefCell::new((0_u64, 0_u64, HashSet::<Job>::default())));
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
                if wake.admission == fz_engine::Admission::Started
                    && let super::DependencyKey::Fact(FactKey::FunctionDefined(function)) = wake.cause.fact()
                    && world.function_definition(*function).1.is_macro
                {
                    observed_macro_consumers.borrow_mut().insert(wake.job.clone());
                }
                if wake.admission == fz_engine::Admission::Started
                    && matches!(wake.job, Job::DeriveRuntimeDemand(_))
                {
                    demand_work.1 += 1;
                    let cause = match &wake.cause {
                        fz_engine::FactUse::Current(super::DependencyKey::Fact(FactKey::CallableConstructionTarget(_))) => {
                            0
                        }
                        fz_engine::FactUse::Settled(super::DependencyKey::Fact(FactKey::ExecutableFacts(_))) => 1,
                        fz_engine::FactUse::Current(super::DependencyKey::Fact(FactKey::RuntimeDemandInput(_))) => 2,
                        fz_engine::FactUse::Current(super::DependencyKey::Fact(FactKey::RuntimeDemandInputs(_)))
                        | fz_engine::FactUse::Concluded(super::DependencyKey::Fact(FactKey::RuntimeDemandInputs(_))) => 3,
                        fz_engine::FactUse::Current(super::DependencyKey::Fact(FactKey::ExecutableFacts(_))) => 4,
                        cause => panic!("unexpected RuntimeDemand wake prerequisite: {cause:?}"),
                    };
                    observed_demand_wake_causes.borrow_mut()[cause] += 1;
                }
            }
        },
    );
    let macro_product_consumers = std::rc::Rc::new(std::cell::RefCell::new(HashSet::<Job>::default()));
    let observed_product_consumers = std::rc::Rc::clone(&macro_product_consumers);
    telemetry.attach_raw_event1::<fz_engine::AppliedStep<Job, super::DependencyKey>, _>(
        &["fz", "compiler2", "work_graph", "dependencies_moved"],
        move |_, _, _, step| {
            for wake in &step.wakes {
                if wake.admission == fz_engine::Admission::Started
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
    assert_eq!(macro_definition_consumers.borrow().len(), 4);
    assert_eq!(
        *macro_definition_consumers.borrow(),
        *macro_product_consumers.borrow(),
        "the macro consumers resume on their definition and then on their exact retained content"
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
        // cone at once, so the executable-fact tally counts each layer once.
        // A function's source is published by the walk that scoped it, so no
        // separate source job runs per reached function.
        // A job gated on a fact its subject already carries never starts to
        // discover that fact missing, then wake once the fact lands
        // (`Job::missing_gates`).
        (2801, 15, 31, 190),
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
        starts[WorkStart::ChangedRevisionWake] - demand_wake_starts,
        1229,
        "ordinary generic helper facts have the exact non-demand changed-revision census",
    );
    assert_eq!(
        starts[WorkStartReason::BlockedWaiterExpansion.into()],
        454,
        "the blocked-waiter census includes only the prerequisites each completion's own waits expand",
    );
    assert_eq!(
        (*demand_completions, *demand_wake_starts, *demand_wake_causes.borrow()),
        // `DeriveRuntimeDemand` completions, the wakes that enqueued them,
        // and those wakes split by the prerequisite that caused each one:
        // construction target, settled executable facts, one exact runtime-
        // demand input, the whole input vector, and unclassified.
        // The last slot is zero because every wake names the fact that moved.
        (408, 410, [24, 190, 0, 196, 0]),
        "every demand completion and ordinary helper wake retains its precise cause",
    );
    assert_eq!(
        demanded_formula_keys.len(),
        228,
        "the demand frontier retains every ordinary generic helper key",
    );
    assert_eq!(
        (
            starts[WorkStartReason::Ignition.into()],
            starts[WorkStartReason::ActivationPublished.into()],
            starts[WorkStart::Unclassified],
        ),
        (1, 0, 0),
        "ordinary generic helper activations preserve the pull-only frontier",
    );

    let world = compiler.world();
    let analyzed_activations = analyzed_activations.borrow();
    // `main/0`'s thirty-eight `dbg` calls each read one callee's answer,
    // and each read waits for its callee's concluded answer, so `main/0`
    // is woken once per callee, on its concluded answer, rather than once
    // per intermediate revision that callee happens to publish on its own
    // way there.
    assert_eq!(
        analyzed_activations.len(),
        663,
        "the fixture's total AnalyzeActivation completions, repeats included",
    );
    let frontier_analyses = analyzed_activations.iter().cloned().collect::<HashSet<_>>();
    // Grouped by `FunctionId` alone, the same 105 distinct functions reach
    // the frontier, but several are reached under fewer distinct `arrow`
    // shapes: a caller that propagates a callee's unconcluded,
    // soon-to-be-revised answer into a further call analyzes that call
    // under a guessed input, then is re-analyzed again once the real
    // answer arrives, so each guessed shape inflates this count without
    // naming a new function.
    assert_eq!(
        frontier_analyses.len(),
        223,
        "the demand frontier's distinct activations, deduplicated across repeats",
    );

    let root_entry = world.root_entry(root);
    let (root_claims, root_reads) = world.standing_claims_and_reads(&Job::SeedRoot(root));
    // `main/0` takes no arguments, so it is self-keyed by construction
    // (R1): `SeedRoot` never reads its `Recursive` or `InputDemand` at all,
    // since nothing needs to key an activation that carries no type
    // variables.
    assert!(!root_reads.contains(&FactUse::settled(FactKey::Recursive(root_entry.function))));
    assert!(!root_reads.contains(&FactUse::settled(FactKey::InputDemand(root_entry.function))));
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

/// An indexed module names the scope that encloses it, so the scheduler can
/// hold its definition until that scope exists. A run started earlier finds
/// no scope to define the module in and stops.
#[test]
fn a_module_is_not_started_before_its_enclosing_scope_exists() {
    let source = "\
defmodule Outer do
  defmodule Inner do
    def one(), do: 1
  end
  def two(), do: Inner.one() + 1
end
def main(), do: Outer.two()
";
    let telemetry = ConfiguredTelemetry::new();
    let early_starts = std::rc::Rc::new(std::cell::RefCell::new(Vec::<String>::new()));
    let observed = std::rc::Rc::clone(&early_starts);
    telemetry.attach_raw_event2::<super::World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| {
            let Job::DefineModule(module) = &completion.job else {
                return;
            };
            for wait in &completion.blocked {
                match wait.fact() {
                    super::DependencyKey::Fact(FactKey::CodeScoped(_)) => {}
                    super::DependencyKey::Fact(FactKey::ModuleDefined(parent)) if parent != module => {}
                    _ => continue,
                }
                observed
                    .borrow_mut()
                    .push(format!("{:?} stopped for {wait:?}", completion.job));
            }
        },
    );
    let mut compiler = Compiler2::new(telemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("nested_modules.fz".to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_backend_work_starts(root)
        .expect("the program should drive to its backend product");
    let early_starts = early_starts.borrow();
    assert!(
        early_starts.is_empty(),
        "a module was started before the scope that encloses it existed:\n{}",
        early_starts.join("\n")
    );
}
