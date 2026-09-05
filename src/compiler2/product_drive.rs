//! Shared retained root-product request and pull-drive boundary.
//!
//! Backend and native front doors use one session lifecycle and one stack-based
//! pull to the same fixed point: pop a product key, pull it, and expand its
//! exact product/fact waits until the requested root product settles or the
//! budget runs out. A native pull publishes the backend product it discovers
//! before lowering continues. The test-only bounded runner returns its fresh
//! driver so failure-contract tests can inspect it. `ProductDriveError` keeps
//! the production `String` and scheduler `FatalError` surfaces distinct without
//! duplicating the loop.
use std::rc::Rc;

use super::drive::{ExecutionContext, FactKey};
use super::facts::{FactReadiness, FactUse};
use super::identity::RootId;
use super::pull::{
    ProductDriver, ProductFailure, ProductKey, ProductProjection, ProductSessions, ProductValue, PullOutcome, PullWait,
    WorldProductProducers,
};
use super::scheduler::{DriveOutcome, FatalError, WorkStartReason};
use super::semantic::SemanticOrd;
use super::world::World;
use super::{BackendProgram, Job};
use crate::telemetry::RawSpanGuard as _;

/// A retry-budgeted stack expansion of this size backs both the outer product
/// pull and the inner fact-wait job drive, matching the pre-unification
/// budgets in both call sites.
pub(super) const PRODUCT_DRIVE_BUDGET: u64 = 50_000;

/// Reports the ways a root-product pull-drive can fail.
///
/// Each method receives the settled `World` so an implementation can read
/// context (e.g. `World::unresolved_waits`) or emit a diagnostic; the loop
/// itself only ever constructs `Self` through these hooks, so the two
/// consumers keep their own error text/type without duplicating the loop
/// that discovers the failure.
pub(crate) trait ProductDriveError: Sized {
    /// A job the fact-wait ran to satisfy `fact` failed. `source` is the
    /// `FatalError` `jobs::run` returned (already diagnostic-bearing).
    fn job_failed<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
        job: &Job,
        source: FatalError,
    ) -> Self;
    /// The fact-wait's agenda drained with no ready producer for `fact`.
    fn no_ready_producer<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
    ) -> Self;
    /// The fact-wait for `fact` ran more jobs than the budget allows.
    fn fact_wait_budget_exceeded<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
    ) -> Self;
    /// The outer product-pull stack exhausted its budget before the requested
    /// product settled. `last_wait` is the last product key and waits observed,
    /// when any wait was ever recorded.
    fn did_not_settle<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        last_wait: Option<(ProductKey, Vec<PullWait>)>,
    ) -> Self;
    fn product_failed<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        product: &ProductKey,
        failure: ProductFailure,
    ) -> Self;
}

/// Test-only fresh-session drive used by the bounded failure-contract tests.
#[cfg(test)]
pub(crate) fn drive_root_backend_product<'a, T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &'a T,
    root: RootId,
) -> Result<(Rc<BackendProgram>, ProductDriver<'a, T>), E> {
    drive_root_backend_product_with_budgets(world, tel, root, PRODUCT_DRIVE_BUDGET, PRODUCT_DRIVE_BUDGET)
}

/// The loop `drive_root_backend_product` runs, parameterized on the outer
/// product-stack budget and the inner per-prerequisite job budget. This is a
/// test-only seam: `drive_root_backend_product` always passes
/// `PRODUCT_DRIVE_BUDGET` for both, so production behavior is byte-identical
/// to before the split. Tests pass a small budget to force
/// `did_not_settle`/`fact_wait_budget_exceeded` on a genuine drive without
/// spending the real 50,000-job budget doing it. Production retains the same
/// loop's session through `drive_retained_root_backend_product`.
#[cfg(test)]
pub(super) fn drive_root_backend_product_with_budgets<
    'a,
    T: crate::telemetry::RawSpanTelemetry,
    E: ProductDriveError,
>(
    world: &mut World,
    tel: &'a T,
    root: RootId,
    product_stack_budget: u64,
    fact_wait_budget: u64,
) -> Result<(Rc<BackendProgram>, ProductDriver<'a, T>), E> {
    let mut driver = ProductDriver::new(tel, root);
    let program = drive_root_backend_product_with_driver(
        world,
        tel,
        root,
        &mut driver,
        None,
        product_stack_budget,
        fact_wait_budget,
    )?;
    Ok((program, driver))
}

pub(crate) fn drive_retained_root_backend_product<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    sessions: &mut ProductSessions,
    root: RootId,
) -> Result<(Rc<BackendProgram>, Option<ProductProjection>), E> {
    with_retained_root_request(world, tel, sessions, root, |world, tel, sessions, driver, _| {
        drive_active_root_backend_product(world, tel, sessions, root, driver)
    })
}

pub(crate) fn drive_retained_root_native_program<T: crate::telemetry::RawSpanTelemetry>(
    world: &mut World,
    tel: &T,
    sessions: &mut ProductSessions,
    root: RootId,
    timeout: Option<std::time::Duration>,
) -> Result<Rc<super::NativeProgram>, String> {
    with_reconciled_root_request(world, tel, sessions, root, timeout, |world, tel, sessions, driver| {
        let key = ProductKey::NativeProgram(root);
        let (value, _) = drive_root_product_with_driver::<T, String>(
            world,
            tel,
            root,
            key,
            driver,
            Some(sessions),
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
        )?;
        let program = match value {
            ProductValue::NativeProgram(program) => program,
            value => panic!("native root product produced unexpected value {value:?}"),
        };
        Ok(program)
    })
}

pub(crate) fn with_reconciled_root_request<'a, T, R>(
    world: &mut World,
    tel: &'a T,
    sessions: &mut ProductSessions,
    root: RootId,
    timeout: Option<std::time::Duration>,
    run: impl FnOnce(&mut World, &'a T, &mut ProductSessions, &mut ProductDriver<'a, T>) -> Result<R, String>,
) -> Result<R, String>
where
    T: crate::telemetry::RawSpanTelemetry,
{
    with_retained_root_request(world, tel, sessions, root, |world, tel, sessions, driver, retained| {
        reconcile_request(world, tel, sessions, root, timeout, retained)?;
        let result = run(world, tel, sessions, driver)?;
        world.unpark_root_artifact_jobs(root);
        let mut context = ExecutionContext::with_product_sessions(world, tel, sessions);
        drain_request_context(&mut context, root, timeout)?;
        Ok(result)
    })
}

pub(crate) fn with_retained_root_request<'a, T, E, R>(
    world: &mut World,
    tel: &'a T,
    sessions: &mut ProductSessions,
    root: RootId,
    run: impl FnOnce(&mut World, &'a T, &mut ProductSessions, &mut ProductDriver<'a, T>, bool) -> Result<R, E>,
) -> Result<R, E>
where
    T: crate::telemetry::RawSpanTelemetry,
{
    let (session, retained) = sessions.take(root, world.work_start_tally());
    let mut driver = ProductDriver::with_session(tel, session);
    let result = run(world, tel, sessions, &mut driver, retained);
    world.unpark_root_artifact_jobs(root);
    sessions.finish_activation(root, driver.session_mut(), world.work_start_tally());
    let session = driver.into_session();
    sessions.restore(session);
    result
}

pub(crate) fn drive_active_root_backend_product<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    sessions: &mut ProductSessions,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
) -> Result<(Rc<BackendProgram>, Option<ProductProjection>), E> {
    let program = drive_root_backend_product_with_driver(
        world,
        tel,
        root,
        driver,
        Some(sessions),
        PRODUCT_DRIVE_BUDGET,
        PRODUCT_DRIVE_BUDGET,
    )?;
    let projection = driver.projection(&ProductKey::RootBackendProduct(root));
    Ok((program, projection))
}

fn drive_root_backend_product_with_driver<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
    sessions: Option<&mut ProductSessions>,
    product_stack_budget: u64,
    fact_wait_budget: u64,
) -> Result<Rc<BackendProgram>, E> {
    let root_key = ProductKey::RootBackendProduct(root);
    let (value, _) = drive_root_product_with_driver(
        world,
        tel,
        root,
        root_key,
        driver,
        sessions,
        product_stack_budget,
        fact_wait_budget,
    )?;
    match value {
        ProductValue::RootBackendProduct(answer) => Ok(Rc::clone(&answer.program)),
        value => panic!("backend root product produced unexpected value {value:?}"),
    }
}

fn drive_root_product_with_driver<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    root_key: ProductKey,
    driver: &mut ProductDriver<'_, T>,
    sessions: Option<&mut ProductSessions>,
    product_stack_budget: u64,
    fact_wait_budget: u64,
) -> Result<(ProductValue, Option<ProductProjection>), E> {
    drive_root_product_with(
        world,
        tel,
        root,
        root_key,
        driver,
        sessions,
        product_stack_budget,
        fact_wait_budget,
        |world, driver, current| {
            let mut producers = WorldProductProducers::new(world, tel);
            driver.pull(&mut producers, current)
        },
    )
}

#[cfg(test)]
pub(super) fn drive_root_product_with_producers<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    root_key: ProductKey,
    driver: &mut ProductDriver<'_, T>,
    sessions: Option<&mut ProductSessions>,
    producers: &mut impl super::pull::ProductProducers,
) -> Result<(ProductValue, Option<ProductProjection>), E> {
    drive_root_product_with(
        world,
        tel,
        root,
        root_key,
        driver,
        sessions,
        PRODUCT_DRIVE_BUDGET,
        PRODUCT_DRIVE_BUDGET,
        |_, driver, current| driver.pull(producers, current),
    )
}

fn drive_root_product_with<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    root_key: ProductKey,
    driver: &mut ProductDriver<'_, T>,
    mut sessions: Option<&mut ProductSessions>,
    product_stack_budget: u64,
    fact_wait_budget: u64,
    mut pull: impl FnMut(&mut World, &mut ProductDriver<'_, T>, ProductKey) -> PullOutcome,
) -> Result<(ProductValue, Option<ProductProjection>), E> {
    // `Vec::new` is allocation-free: a retained root hit returns before the
    // first wait pushes anything onto the expansion stack.
    let mut stack = Vec::new();
    let mut current = root_key.clone();
    let mut last_wait = None;
    let mut backend_projection = None;
    for _ in 0..product_stack_budget {
        if let Some(sessions) = sessions.as_deref_mut() {
            sessions.drain_active_movements(root, driver.session_mut());
        }
        let outcome = pull(world, driver, current.clone());
        if let Some(sessions) = sessions.as_deref_mut() {
            sessions.sync_subscriptions(root, driver.session_mut());
        }
        match outcome {
            PullOutcome::Produced(value) => {
                let requested = current == root_key;
                if let (ProductKey::RootBackendProduct(backend_root), ProductValue::RootBackendProduct(answer)) =
                    (&current, &value)
                {
                    let projection = driver.projection(&current);
                    if requested {
                        backend_projection = projection;
                    } else if let Some(sessions) = sessions.as_deref_mut() {
                        super::jobs::backend::publish_backend_product_projection(
                            world,
                            tel,
                            sessions,
                            *backend_root,
                            Rc::clone(&answer.program),
                            projection,
                        );
                    }
                }
                if requested {
                    ExecutionContext::new(world, tel).flush_reported_warnings();
                    return Ok((value, backend_projection));
                }
                current = stack.pop().unwrap_or_else(|| root_key.clone());
            }
            PullOutcome::Waiting(mut waits) => {
                // A pull that reports more than one wait built the list from
                // a `HashSet<PullWait>` upstream (the standing idiom for
                // wait-accumulator parameters throughout `jobs::runtime_demand`
                // and `jobs::artifact`), so its arrival order here is a
                // per-process `RandomState` artifact, not a property of the
                // program. Product dependencies still expand in order, and
                // fact producers are still driven in order, so that order
                // decides which producer job actually runs first and can flip
                // a keep-first merge downstream. The settled fact questions
                // from this ONE evaluation cross the drain arbiter together.
                // `PullWait`'s
                // constituents span too many identity types across the
                // compiler to give it a cheap structural `Ord`, but its
                // Product keys retain their existing data ordering. Fact uses
                // can carry activation arrows, whose raw `Ty` ids are mint
                // history, so they share the World's faithful semantic key
                // with terminal diagnostics and other fact-wait boundaries.
                sort_product_waits(world.types(), &mut waits);
                waits.dedup();
                last_wait = Some((current.clone(), waits.clone()));
                stack.push(current);
                let mut facts = Vec::new();
                for wait in waits.into_iter().rev() {
                    match wait {
                        PullWait::Product(product) => stack.push(product),
                        PullWait::Fact(fact) => facts.push(fact),
                    }
                }
                let producer_pokes = drive_product_fact_waits_with_sessions::<T, E>(
                    world,
                    tel,
                    root,
                    driver,
                    sessions.as_deref_mut(),
                    &facts,
                    fact_wait_budget,
                )?;
                driver.session_mut().record_producer_pokes(producer_pokes);
                current = stack.pop().expect("a waiting product leaves itself on the pull stack");
            }
            PullOutcome::Failed(failure) => return Err(E::product_failed(world, tel, root, &current, failure)),
        }
    }
    Err(E::did_not_settle(world, tel, root, last_wait))
}

/// Orders a product producer's unordered wait set before the stack consumes
/// it. Fact waits use the World's semantic type key because they can contain
/// activation arrows whose raw handles and display strings are not identities.
pub(super) fn sort_product_waits(types: &super::types::Types, waits: &mut [PullWait]) {
    waits.sort_by(|left, right| match (left, right) {
        (PullWait::Fact(left), PullWait::Fact(right)) => left.semantic_cmp(right, types),
        (PullWait::Product(left), PullWait::Product(right)) => left.semantic_cmp(right, types),
        (PullWait::Fact(_), PullWait::Product(_)) => std::cmp::Ordering::Less,
        (PullWait::Product(_), PullWait::Fact(_)) => std::cmp::Ordering::Greater,
    });
}

/// The single-fact test seam over the exact prerequisite-set loop below.
/// Production passes every fact named by one product evaluation together.
#[cfg(test)]
pub(super) fn drive_product_fact_wait<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
    fact: FactUse<FactKey>,
    fact_wait_budget: u64,
) -> Result<u64, E> {
    drive_product_fact_waits_with_sessions(world, tel, root, driver, None, &[fact], fact_wait_budget)
}

#[cfg(test)]
pub(super) fn drive_product_fact_waits<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
    facts: &[FactUse<FactKey>],
    fact_wait_budget: u64,
) -> Result<u64, E> {
    drive_product_fact_waits_with_sessions(world, tel, root, driver, None, facts, fact_wait_budget)
}

fn drive_product_fact_waits_with_sessions<T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
    mut sessions: Option<&mut ProductSessions>,
    facts: &[FactUse<FactKey>],
    fact_wait_budget: u64,
) -> Result<u64, E> {
    let mut producer_pokes = 0_u64;
    let settled_facts = facts
        .iter()
        .filter(|fact| fact.readiness() == super::facts::FactReadiness::Settled)
        .map(|fact| fact.fact().clone())
        .collect::<Vec<_>>();
    for fact in facts {
        let mut jobs_ran = 0_u64;
        while !product_fact_wait_is_satisfied(world, fact) {
            let job = match world.next_ready_job(sessions.as_ref().map(|_| root)) {
                Some(job) => {
                    apply_quiescence(world, tel, driver, sessions.as_deref_mut());
                    job
                }
                None => {
                    // One producer evaluation owns one exact prerequisite set.
                    // At a drain, arbitrate all of its settled questions in one
                    // scheduler step so their typed movements stay atomic.
                    world.settle_quiescent(&settled_facts);
                    if apply_quiescence(world, tel, driver, sessions.as_deref_mut()) {
                        continue;
                    }
                    producer_pokes += world.demand_fact_producer(fact.fact(), WorkStartReason::BlockedWaiterExpansion);
                    let job = if sessions.is_some() {
                        world.pop_root_request_job(root)
                    } else {
                        world.work_graph.pop()
                    };
                    let Some(job) = job else {
                        return Err(E::no_ready_producer(world, tel, root, fact));
                    };
                    job
                }
            };
            let job_span = super::drive::start_job_span(tel, &job);
            let result = super::jobs::run(
                &mut super::drive::ExecutionContext::with_optional_product_sessions(
                    world,
                    tel,
                    sessions.as_deref_mut(),
                ),
                &job,
            );
            match result {
                Ok(effects) => {
                    jobs_ran += 1;
                    let completion = super::drive::ExecutionContext::with_optional_product_sessions(
                        world,
                        tel,
                        sessions.as_deref_mut(),
                    )
                    .complete_job(job, effects);
                    if sessions.is_none() {
                        driver.apply_fact_movements(&completion.step.movements);
                    }
                    super::drive::stop_job_span(job_span);
                }
                Err(err) => {
                    job_span.exception();
                    return Err(E::job_failed(world, tel, root, fact, &job, err));
                }
            }
            if jobs_ran > fact_wait_budget {
                return Err(E::fact_wait_budget_exceeded(world, tel, root, fact));
            }
        }
    }
    Ok(producer_pokes)
}

/// Emits the drain arbiter's readiness steps and feeds their movements to the
/// product memo, exactly as a job completion's movements are fed. Returns
/// whether the arbiter moved anything — a moved fact is a reason to re-ask the
/// wait, whether or not the movement also woke a job.
fn apply_quiescence<T: crate::telemetry::RawSpanTelemetry>(
    world: &mut World,
    tel: &T,
    driver: &mut ProductDriver<'_, T>,
    sessions: Option<&mut ProductSessions>,
) -> bool {
    let steps = super::drive::flush_quiescence(world, tel);
    if let Some(sessions) = sessions {
        for step in &steps {
            sessions.publish(&step.movements);
        }
    } else {
        for step in &steps {
            driver.apply_fact_movements(&step.movements);
        }
    }
    !steps.is_empty()
}

fn product_fact_wait_is_satisfied(world: &World, fact: &FactUse<FactKey>) -> bool {
    match fact.readiness() {
        FactReadiness::Current => world.fact_revision(fact.fact()).is_some(),
        FactReadiness::Settled => world.fact_is_settled(fact.fact()),
    }
}

fn reconcile_request<T: crate::telemetry::RawSpanTelemetry>(
    world: &mut World,
    telemetry: &T,
    sessions: &mut ProductSessions,
    root: RootId,
    timeout: Option<std::time::Duration>,
    retained: bool,
) -> Result<(), String> {
    if timeout == Some(std::time::Duration::ZERO) {
        let outcome =
            ExecutionContext::with_product_sessions(world, telemetry, sessions).drain_pending_for_root(root, timeout);
        if let DriveOutcome::TimedOut { jobs_ran, pending_jobs } = outcome {
            return Err(format!(
                "compiler2 root {} exceeded 0 ms drive limit after {} jobs with {} pending",
                root.as_u32(),
                jobs_ran,
                pending_jobs,
            ));
        }
    }
    if world.work_graph.runnable_jobs() == 0 || !retained && !world.work_graph.pending(&Job::BuildBackendProduct(root))
    {
        return Ok(());
    }
    let outcome =
        ExecutionContext::with_product_sessions(world, telemetry, sessions).drain_pending_for_root(root, timeout);
    interpret_request_drain(root, outcome)
}

fn drain_request_context<T: crate::telemetry::RawSpanTelemetry>(
    context: &mut ExecutionContext<'_, T>,
    root: RootId,
    timeout: Option<std::time::Duration>,
) -> Result<(), String> {
    if context.world.work_graph.runnable_jobs() == 0 {
        return Ok(());
    }
    let outcome = context.drain_pending_for(timeout);
    interpret_request_drain(root, outcome)
}

fn interpret_request_drain(root: RootId, outcome: DriveOutcome<Job, FactKey>) -> Result<(), String> {
    match outcome {
        DriveOutcome::Resolved => Ok(()),
        DriveOutcome::Fatal { job } => Err(format!(
            "compiler2 root {} failed while applying queued work at {job:?}",
            root.as_u32()
        )),
        DriveOutcome::TimedOut { jobs_ran, pending_jobs } => Err(format!(
            "compiler2 root {} exceeded its drive limit after {} jobs with {} pending",
            root.as_u32(),
            jobs_ran,
            pending_jobs
        )),
        DriveOutcome::Unresolved { waits } => Err(format!(
            "compiler2 root {} could not apply queued work; unresolved={waits:?}",
            root.as_u32()
        )),
    }
}
