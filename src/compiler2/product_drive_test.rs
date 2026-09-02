//! Regression coverage for the shared `RootBackendProduct` pull-drive seam:
//! one loop (`product_drive::drive_root_backend_product`) reports its four
//! failure shapes through a `ProductDriveError` hook so the interp front door
//! (`String`) and the backend product job (`FatalError`) keep their distinct
//! error surfaces byte-for-byte, even though the loop that discovers the
//! failure lives once.
//!
//! The first block of tests calls the trait implementations directly rather
//! than forcing a genuine product-pull stall through a fixture: the loop
//! control-flow itself is already exercised end-to-end by every other
//! compiler2 test that drives a root to a backend product (`compiler2_test`,
//! `transport_contract_test`, `drive_test`, ...), so the risk unique to this
//! seam is the `ProductDriveError` dispatch — that is what those tests pin.
//! Only `fact_wait_budget_exceeded` and `did_not_settle` keep a direct-call
//! test per error type: their `*_end_to_end` counterparts below can only
//! assert a message prefix (the exact `fact`/`last_wait` suffix they format
//! at runtime bakes in incidental interned ids — `FunctionId`/`Ty` — that
//! shift with unrelated compiler changes), so the direct tests are the only
//! place the full `{:?}`-formatted template is pinned exactly. The other two
//! error types (`no_ready_producer`, `job_failed`) have no such gap — their
//! end-to-end counterparts already assert the full template exactly — so
//! their direct-call tests were redundant and are deleted.
//!
//! The second block (`*_end_to_end` below) proves the wiring itself: that a
//! genuine failure inside `drive_root_backend_product` reaches the hook with
//! the right `root`/`fact`/`job` arguments, not just that the hook formats
//! them correctly in isolation. `fact_wait_budget_exceeded` and
//! `did_not_settle` go through `drive_root_backend_product_with_budgets`, a
//! test-only budget seam (`product_drive.rs`) — the production entry point
//! always calls it with the real 50,000-job budget for both parameters, so
//! this changes no production behavior.

use super::World;
use super::drive::FactKey;
use super::drive::Job;
use super::facts::FactUse;
use super::identity::{ExecutableNeed, RootId};
use super::product_drive::ProductDriveError;
use super::pull::{ProductKey, PullWait};
use super::scheduler::{DriveOutcome, FatalError};
use super::{CodeSubmission, Compiler2, RootSubmission};
use crate::telemetry::{Capture, ConfiguredTelemetry};

fn diagnostic_message(event: &crate::telemetry::capture::OwnedEvent) -> &str {
    event
        .diagnostic
        .as_ref()
        .map(|diagnostic| diagnostic.message.as_str())
        .expect("diagnostic event missing diagnostic payload")
}

fn some_fact() -> FactUse<FactKey> {
    FactUse::settled(FactKey::BackendProgram(RootId::for_test(7)))
}

/// fz-k22.13 regression: JIT-compiling one fixed root twice, in two
/// independent `Compiler2`/`World`/`Types` instances within the same test
/// process, must reach the exact same outcome -- both the success/failure
/// shape and, on failure, the byte-identical diagnostic text.
///
/// This is not an inert test: `RandomState` reseeds per `HashMap`/`HashSet`
/// instantiation even within one process, not just across process runs, so
/// two fresh interners built in one test function genuinely land on
/// different iteration orders wherever an order-dependence survives -- the
/// same hazard `enum_predicate_search.fz` exposed run-to-run at the `fz2`
/// CLI before this fix (a different closure-target ABI diagnostic on almost
/// every invocation). `compile_root_jit` is the exact API `fz2 run` calls.
#[test]
fn compiling_the_same_root_twice_through_the_jit_reaches_the_same_outcome() {
    fn compile_enum_predicate_search() -> Result<crate::fz_ir::FnId, String> {
        let tel = ConfiguredTelemetry::new();
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures2/behavior/enum_predicate_search.fz".to_string()),
            text: include_str!("../../fixtures2/behavior/enum_predicate_search.fz").to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler.compile_root_jit(root).map(|(_compiled, entry)| entry)
    }

    let outcome_a = compile_enum_predicate_search();
    let outcome_b = compile_enum_predicate_search();

    assert_eq!(
        outcome_a.is_ok(),
        outcome_b.is_ok(),
        "compiling the same root twice must succeed or fail identically, got {outcome_a:?} vs {outcome_b:?}"
    );
    if let (Err(error_a), Err(error_b)) = (&outcome_a, &outcome_b) {
        assert_eq!(
            error_a, error_b,
            "compiling the same root twice must report a byte-identical diagnostic"
        );
    }
}

/// Compiles `enum_predicate_search` and reports both halves of the determinism
/// contract: the ordered sequence of jobs the drive actually ran (observed
/// through the production `fz.compiler2.job` span, not a test-only hook) and
/// the `BackendProgram` it published.
fn compile_enum_predicate_search() -> (Vec<Job>, super::BackendProgram) {
    let tel = ConfiguredTelemetry::new();
    let jobs: std::rc::Rc<std::cell::RefCell<Vec<Job>>> = Default::default();
    let recorded = std::rc::Rc::clone(&jobs);
    tel.attach_raw_span1_2::<Job, World, super::JobCompletion, _, _, _>(
        &["fz", "compiler2", "job"],
        move |_, _, _, job| recorded.borrow_mut().push(job.clone()),
        |_, _, _, _, _, _| {},
        |_, _, _, _| {},
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/behavior/enum_predicate_search.fz".to_string()),
        text: include_str!("../../fixtures2/behavior/enum_predicate_search.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .compile_root_jit(root)
        .unwrap_or_else(|error| panic!("expected the fixture to compile, got {error}"));
    let program = compiler.world().backend_program(root);
    (jobs.take(), program)
}

/// Same input, same work — the CAUSAL half of the determinism contract.
///
/// One of THREE properties, none of which subsumes another: the canonical
/// external form (`compiler2::canon`) measures the ARTIFACT, raw `Ty` equality
/// below measures the BOOKKEEPING, and this test measures the CAUSE.
///
/// Job order is not an implementation detail. It decides which conclusion lands
/// first at a keep-first merge, and it decides the order fresh types reach the
/// interner, whose ids are arena positions. So a run-to-run difference here is
/// what makes the published `BackendProgram` irreproducible, and it is where a
/// determinism defect actually lives.
///
/// Its sibling below asserts the end state instead. Both are needed and neither
/// subsumes the other: this one names the cause and fails at the first swapped
/// pair; that one proves nothing downstream reintroduced a hazard. Byte
/// equality alone is a 1.5MB inequality message that names nothing (fz-f98.19).
#[test]
fn compiling_the_same_root_twice_runs_the_same_jobs_in_the_same_order() {
    let (jobs_a, _) = compile_enum_predicate_search();
    let (jobs_b, _) = compile_enum_predicate_search();

    let divergence = jobs_a.iter().zip(jobs_b.iter()).position(|(a, b)| a != b);
    assert!(
        divergence.is_none() && jobs_a.len() == jobs_b.len(),
        "compiling the same root twice must run the same jobs in the same order; \
         first run drove {} jobs, second drove {}{}",
        jobs_a.len(),
        jobs_b.len(),
        divergence.map_or(String::new(), |at| format!(
            ", and they first diverge at job {at}:\n  first:  {:?}\n  second: {:?}",
            jobs_a[at], jobs_b[at]
        )),
    );
}

/// The END STATE of the determinism contract: same input, byte-identical
/// artifact -- including every raw `Ty` an executable's signature or body
/// carries, not just the executable inventory's shape.
///
/// This is the BOOKKEEPING property, one of three (see the sibling above for
/// the CAUSE, and `compiler2::canon` for the ARTIFACT). Raw `Ty` equality is a
/// valid comparand HERE and nowhere else. A `Ty` is an arena index in one
/// `World`, so comparing ids across two worlds is normally far too strong a bar
/// -- one extra incidental intern shifts every later id without changing what
/// the program means. What makes it sound in this test is that both compiles
/// run the same binary over the same input in one process: the code path is
/// identical, so the ONLY thing that can renumber the arena is nondeterminism.
/// Under those conditions "different ids" implies "different work order", which
/// is a real defect.
///
/// Do not lift this comparison to cross-process, cross-version, or
/// cached-artifact equivalence. That is what `compiler2::canon` is for, and it
/// answers a strictly different question: it is blind to renumbering, so it
/// would pass on fz-f98.19's defect (the same 836 types minted in a permuted
/// order) that this test catches. It also cannot be faked from `{:?}` --
/// `HashMap`'s own Debug order is unstable, so a Debug-derived rendering
/// differs run to run even when the structs are equal.
///
/// fz-k22.21 raised this past bare success/failure (the JIT-outcome check
/// above), and fz-k22.28 pinned the folds that minted types AS THEY ITERATED
/// (`jobs/runtime_demand.rs`'s per-cone member list and per-value
/// callable-flow list, `World::demand_activation_frontier_analyses`'s
/// frontier). fz-f98.19 is the same disease one layer down: the folds that
/// reorder JOB WAKES, whose effect on the interner is second-order. Its cause
/// is named by the sibling test above; this one additionally catches a
/// nondeterminism that never reaches job order -- an unordered fold inside a
/// single job that only reorders what it emits -- so neither test subsumes the
/// other.
#[test]
fn compiling_the_same_root_twice_publishes_byte_identical_backend_programs() {
    let (_, program_a) = compile_enum_predicate_search();
    let (_, program_b) = compile_enum_predicate_search();

    assert_eq!(
        program_a, program_b,
        "compiling the same root twice must publish a byte-identical BackendProgram -- \
         including raw Ty numbering, not just the same executable inventory"
    );
}

/// The `add1` fixture, submitted and rooted at `main/0`: the shared "ordinary,
/// fully resolvable root" setup the `fact_wait_budget_exceeded`/
/// `did_not_settle` end-to-end tests drive through the budget seam.
fn add1_world(_tel: &ConfiguredTelemetry) -> (World, RootId) {
    let mut world = World::new();
    world.submit_code(
        Some("fixtures2/behavior/add1.fz".to_string()),
        include_str!("../../fixtures2/behavior/add1.fz").to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    (world, root)
}

#[test]
fn string_error_reports_fact_wait_budget_exceeded() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new();
    let root = RootId::for_test(7);
    let fact = some_fact();

    let message = <String as ProductDriveError>::fact_wait_budget_exceeded(&world, &tel, root, &fact);

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product path exceeded fact-wait budget for {:?}",
            root.as_u32(),
            fact
        )
    );
}

#[test]
fn string_error_reports_did_not_settle_with_last_wait() {
    let tel = ConfiguredTelemetry::new();
    let world = World::new();
    let root = RootId::for_test(7);
    let last_wait = Some((ProductKey::RootBackendProduct(root), vec![PullWait::Fact(some_fact())]));

    let message = <String as ProductDriveError>::did_not_settle(&world, &tel, root, last_wait.clone());

    assert_eq!(
        message,
        format!(
            "compiler2 root {} product backend did not settle; last wait: {last_wait:?}",
            root.as_u32()
        )
    );
}

#[test]
fn fatal_error_diagnostic_reports_fact_wait_budget_exceeded() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let world = World::new();
    let root = RootId::for_test(7);
    let fact = some_fact();

    <FatalError as ProductDriveError>::fact_wait_budget_exceeded(&world, &tel, root, &fact);

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("fact-wait budget exhaustion should emit an error diagnostic");
    let message = diagnostic_message(&event);
    assert_eq!(
        message,
        format!(
            "compiler2 backend product for root {} exceeded fact-wait budget for {:?}",
            root.as_u32(),
            fact
        )
    );
}

// --- end-to-end: genuine drive failures reaching each hook ---------------

/// `no_ready_producer`: a root submitted for a function name that is never
/// defined by any submitted code. `produce_root_backend_product`'s keying
/// waits (`RootEntry`, `DispatchMask`, `Recursive`) are all still unsettled
/// -- `SeedRoot` claims `RootEntry` as an output on its very first
/// (still-blocked) run, but a blocked publisher's claims stay dirty
/// (`Scheduler::complete`: "pausing is not recanting"), so `RootEntry`
/// itself never reads as settled either. Every one of the three keying
/// waits is an equally genuine dead end here, so which one this hook names
/// is the order the pull-drive tries them in -- pinned deterministically
/// (`drive_root_backend_product_with_budgets` sorts a multi-wait
/// `PullOutcome` before processing it), not an accident of hash iteration.
/// This is a real dead end reachable from ordinary (if buggy) input -- a
/// typo'd entry-point name -- not a fabricated one.
#[test]
fn string_error_end_to_end_no_ready_producer_from_undefined_root_entry() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "totally_undefined_entry".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root)
        .expect_err("a root naming an entry no code ever defines should never settle");

    let fact = FactUse::settled(FactKey::RootEntry(root));
    assert_eq!(
        error,
        format!(
            "compiler2 root {} product path waited on {:?} with no ready producer; unresolved={:?}",
            root.as_u32(),
            fact,
            // Read after the fact so the assertion mirrors exactly what the
            // hook itself reports, not a separately reconstructed guess.
            compiler.world().work_graph.unresolved()
        ),
        "the String path should report the undefined entry's RootEntry keying wait, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_no_ready_producer_from_undefined_root_entry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = World::new();
    let root = world.submit_root(None, "totally_undefined_entry".to_string(), 0, ExecutableNeed::Value);

    world.demand(Job::BuildBackendProduct(root));
    let outcome = super::drive::ExecutionContext::new(&mut world, &tel).drive_for(None);
    assert!(
        matches!(&outcome, DriveOutcome::Fatal { job } if *job == Job::BuildBackendProduct(root)),
        "the backend product job should fail fatally when its entry is never defined, got: {outcome:?}"
    );

    let fact = FactUse::settled(FactKey::RootEntry(root));
    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("no-ready-producer should emit an error diagnostic");
    let message = diagnostic_message(&event);
    assert_eq!(
        message,
        format!(
            "compiler2 backend product for root {} waited on {:?} with no ready producer",
            root.as_u32(),
            fact
        ),
        "the FatalError path should report the undefined entry's RootEntry keying wait"
    );
}

/// `fact_wait_budget_exceeded`: an ordinary, fully resolvable root (`add1`),
/// driven through the test-only budget seam with the inner per-fact-wait job
/// budget forced to zero. `drive_product_fact_wait`'s budget check runs after
/// every job unconditionally, so the very first job any real fact-wait runs
/// already exceeds a budget of zero -- this is the same check production
/// hits at 50,001 jobs, just forced early so the test stays fast.
#[test]
fn string_error_end_to_end_fact_wait_budget_exceeded_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, root) = add1_world(&tel);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<_, String>(
        &mut world,
        &tel,
        root,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
        0,
    );
    let error = match result {
        Ok(_) => panic!("a zero fact-wait budget should trip on the first job any real fact-wait runs"),
        Err(error) => error,
    };
    assert!(
        error.contains(&format!(
            "compiler2 root {} product path exceeded fact-wait budget for",
            root.as_u32()
        )),
        "should report the fact-wait budget exceeded template, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_fact_wait_budget_exceeded_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let (mut world, root) = add1_world(&tel);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<_, FatalError>(
        &mut world,
        &tel,
        root,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
        0,
    );
    assert_eq!(
        result.err(),
        Some(FatalError),
        "a zero fact-wait budget should trip fatally on a real drive"
    );

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("fact-wait budget exhaustion should emit an error diagnostic");
    let message = diagnostic_message(&event);
    assert!(
        message.starts_with(&format!(
            "compiler2 backend product for root {} exceeded fact-wait budget for",
            root.as_u32()
        )),
        "should report the fact-wait budget exceeded template, got: {message}"
    );
}

/// `did_not_settle`: the same ordinary `add1` root, driven with the outer
/// product-stack budget forced small enough that the stack pull cannot reach
/// a settled `RootBackendProduct` before the budget runs out, while the inner
/// fact-wait budget stays generous so real jobs run and populate `last_wait`
/// with genuine content (not `None`).
#[test]
fn string_error_end_to_end_did_not_settle_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let (mut world, root) = add1_world(&tel);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<_, String>(
        &mut world,
        &tel,
        root,
        3,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
    );
    let error = match result {
        Ok(_) => panic!("a product-stack budget of 3 should exhaust before add1's product settles"),
        Err(error) => error,
    };
    assert!(
        error.starts_with(&format!(
            "compiler2 root {} product backend did not settle; last wait: Some(",
            root.as_u32()
        )),
        "should report did-not-settle with a populated last wait, got: {error}"
    );
}

/// `job_failed`: a runtime root submitted against a `defmacro` entry.
/// `jobs::root::seed_root` rejects a `RootKind::Runtime` root whose function
/// `is_macro` before it publishes anything, returning `Err(FatalError)`
/// straight from `jobs::run`. `SeedRoot` is the sole producer named by every
/// one of `produce_root_backend_product`'s keying waits
/// (`RootEntry`/`DispatchMask`/`Recursive`) and is already agenda-queued
/// from the root's own ignition, so it runs -- and fails -- inside
/// `drive_product_fact_wait`'s own job loop while satisfying the first of
/// those waits, not somewhere else in the pipeline: a genuine, minimal
/// construction of the seam under test, not a fabricated one.
#[test]
fn string_error_end_to_end_job_failed_from_runtime_root_targeting_a_macro() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_only_root.fz".to_string()),
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "inc".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root)
        .expect_err("a runtime root targeting a macro entry must fail, not silently succeed");

    // `produce_root_backend_product`'s keying waits are all still unsettled
    // (`RootEntry`, `DispatchMask`, `Recursive`), and `SeedRoot` -- the only
    // producer any of the three names -- is already agenda-queued from the
    // root's own ignition, so it runs while satisfying the *first* wait the
    // pull-drive tries. That order is pinned deterministically (a
    // multi-wait `PullOutcome` is sorted before processing), not an
    // accident of hash iteration: `RootEntry`, not `Recursive`, even though
    // `SeedRoot` never gets far enough to publish either fact on this
    // rejecting run.
    let fact = FactUse::settled(FactKey::RootEntry(root));
    let job = Job::SeedRoot(root);
    assert_eq!(
        error,
        format!(
            "compiler2 root {} product path failed while producing {:?}: {:?}",
            root.as_u32(),
            fact,
            job
        ),
        "the String path should report the RootEntry fact-wait's SeedRoot job failure, got: {error}"
    );
}

#[test]
fn fatal_error_end_to_end_job_failed_from_runtime_root_targeting_a_macro() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut world = World::new();
    world.submit_code(
        Some("macro_only_root.fz".to_string()),
        "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n".to_string(),
    );
    let root = world.submit_root(None, "inc".to_string(), 1, ExecutableNeed::Value);

    world.demand(Job::BuildBackendProduct(root));
    let outcome = super::drive::ExecutionContext::new(&mut world, &tel).drive_for(None);
    assert!(
        matches!(&outcome, DriveOutcome::Fatal { job } if *job == Job::BuildBackendProduct(root)),
        "the backend product job should fail fatally when its root targets a macro, got: {outcome:?}"
    );

    // `job_failed` forwards the failed job's own `FatalError` unchanged, so
    // exactly one diagnostic reaches telemetry: `SeedRoot`'s own
    // `emit_root_error`, not a second one from this boundary.
    assert_eq!(
        capture.count(&["fz", "diag", "error"]),
        1,
        "job_failed must not emit a diagnostic on top of the failing job's own"
    );
    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("SeedRoot's macro rejection should emit an error diagnostic");
    let message = diagnostic_message(&event);
    assert_eq!(
        message, "compiler2 runtime root cannot target macro `inc/1`",
        "should surface SeedRoot's own rejection message unchanged"
    );
}

#[test]
fn fatal_error_end_to_end_did_not_settle_on_a_real_drive() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let (mut world, root) = add1_world(&tel);

    let result = super::product_drive::drive_root_backend_product_with_budgets::<_, FatalError>(
        &mut world,
        &tel,
        root,
        3,
        super::product_drive::PRODUCT_DRIVE_BUDGET,
    );
    assert_eq!(
        result.err(),
        Some(FatalError),
        "a product-stack budget of 3 should exhaust fatally before add1's product settles"
    );

    let event = capture
        .last(&["fz", "diag", "error"])
        .expect("did-not-settle should emit an error diagnostic");
    let message = diagnostic_message(&event);
    // Unlike the interp front door's `String` error, the backend job's
    // diagnostic never carries the `last_wait` detail -- preserved as-is.
    assert_eq!(
        message,
        format!("compiler2 backend product for root {} did not settle", root.as_u32())
    );
}

/// A settled product depends only on settled products.
///
/// `ProductMemo::dependency_reaches` -- the recursive-group gate and the strong
/// component behind it -- walks only the dependencies of products that have not
/// settled. Its justification is that a wait cycle cannot run through a settled
/// product: reading one returns the value it already holds, so nothing waits on
/// it and it waits on nothing. This test pins the memo state that makes that
/// true, and so makes skipping settled products lossless rather than merely
/// safe: if a settled product could depend on an unsettled one, a real cycle
/// could route through it and the walk would answer `false` where the answer is
/// `true`, waiting on a dependency that is waiting back.
///
/// A closure passed through a runtime-library reducer is the shape that builds
/// the widest graph: callable constructions, transport shapes, runtime demand
/// and executable facts all take part, and the two recursive kinds both appear.
#[test]
fn settled_products_depend_only_on_settled_products() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("settled_dependencies.fz".to_string()),
        "fn main() do\n  dbg(Enum.reduce([1, 2, 3], 0, fn (x, acc) -> acc + x end))\nend\n".to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);

    let (_program, driver) = super::product_drive::drive_root_backend_product::<_, String>(&mut world, &tel, root)
        .expect("the reducer root should settle");
    let memo = driver.session().memo();

    let unsettled = memo
        .dependency_edges()
        .filter(|(reader, _)| memo.is_settled(reader))
        .filter(|(_, dependency)| !memo.is_settled(dependency))
        .map(|(reader, dependency)| (reader.kind(), dependency.kind()))
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        unsettled.is_empty(),
        "settled products should hold no dependency on an unsettled product, \
         or a wait cycle could route through one: {unsettled:?}"
    );

    // Guard against the assertion above passing vacuously: the two kinds whose
    // recursive groups the walk serves must both be present and both self-loop,
    // so this drive really did exercise the graph the walk is pruning.
    let kinds = memo
        .dependency_edges()
        .map(|(reader, dependency)| (reader.kind(), dependency.kind()))
        .collect::<std::collections::BTreeSet<_>>();
    for kind in ["transport_shape", "callable_construction"] {
        assert!(
            kinds.contains(&(kind, kind)),
            "{kind} should depend on its own kind here, or this drive is not exercising \
             the recursive groups the walk serves (edges: {kinds:?})"
        );
    }
}

/// The demand ascent's height and its per-member re-derivation count do not
/// grow with the size of the program.
///
/// `RuntimeDemand(E)` is settled by a Jacobi ascent over a whole cone of
/// executables, so it has three independent ways to get expensive: the cone can
/// be too big, the ascent can climb too far, or members can re-derive too often.
/// The last two are properties of the lattice and the dirty-set skipping, not of
/// the program, and they must stay that way -- if either started scaling with
/// program size, demand would be super-linear and no amount of scoping the cone
/// would fix it. Doubling the number of identical call sites doubles the cone
/// and must leave both alone.
///
/// The cone SIZE is deliberately not asserted here. A cone is collected
/// transitively and stops only at executables whose demand already settled, so
/// from a cold root it spans the whole reachable call graph and grows with the
/// program by construction. That is what `fz-zg4` is about; this test guards the
/// two numbers that are supposed to be flat so that ticket can be judged by the
/// one that is not.
#[test]
fn the_demand_ascent_height_does_not_grow_with_the_program() {
    fn tallest_cone(call_sites: usize) -> crate::compiler2::DemandConeSettlement {
        let tel = ConfiguredTelemetry::new();
        let tallest = std::rc::Rc::new(std::cell::RefCell::new(None::<crate::compiler2::DemandConeSettlement>));
        let sink = std::rc::Rc::clone(&tallest);
        tel.attach_raw_event1::<crate::compiler2::DemandConeSettlement, _>(
            &["fz", "compiler2", "demand", "cone", "settled"],
            move |_, _, _, cone| {
                let mut sink = sink.borrow_mut();
                if sink.is_none_or(|tallest| cone.members > tallest.members) {
                    *sink = Some(*cone);
                }
            },
        );

        let mut source = String::from("fn main() do\n  xs = [1, 2, 3, 4]\n");
        for bound in 0..call_sites {
            source.push_str(&format!("  dbg(Enum.find(xs, fn (x) -> x > {bound} end))\n"));
        }
        source.push_str("end\n");

        let mut world = World::new();
        world.submit_code(Some("demand_ascent.fz".to_string()), source);
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        super::product_drive::drive_root_backend_product::<_, String>(&mut world, &tel, root)
            .expect("the call-site root should settle");

        let cone = tallest.borrow().expect("a demand cone should settle for this root");
        assert!(cone.members > 0, "a settled cone should report its members");
        cone
    }

    let small = tallest_cone(2);
    let large = tallest_cone(4);

    assert!(
        large.members > small.members,
        "doubling the call sites should grow the cone, or this is not measuring what it thinks: \
         {} vs {} members",
        small.members,
        large.members
    );
    assert_eq!(
        small.rounds, large.rounds,
        "the ascent climbs a lattice, not a program: its round count should not move when the \
         program grows ({} members took {} rounds, {} members took {})",
        small.members, small.rounds, large.members, large.rounds
    );

    // Re-derivations per member is what the dirty set buys: a member whose reads
    // did not move that round is skipped, so the ratio reflects how often a
    // member's inputs actually move -- a lattice property. Compared as a ratio
    // rather than a total, since the total is expected to grow with the cone.
    let ratio = |cone: crate::compiler2::DemandConeSettlement| cone.derivations as f64 / cone.members as f64;
    assert!(
        (ratio(large) - ratio(small)).abs() < 1.0,
        "per-member re-derivation should not grow with the program: {:.2} at {} members vs \
         {:.2} at {} members",
        ratio(small),
        small.members,
        ratio(large),
        large.members
    );
}
