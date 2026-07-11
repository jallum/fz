//! Shared pull-drive runner for the `RootBackendProduct` product boundary.
//!
//! Both the interp front door (`compiler::Compiler2::drive_root_backend_product`)
//! and the backend product job (`jobs::backend::build_backend_product`) drive
//! the exact same stack-based product pull to the exact same fixed point: pop
//! a product key, pull it, and expand any `PullWait::Product`/`PullWait::Fact`
//! the pull reports until `RootBackendProduct` settles or the budget runs out.
//! Only what happens with a settled result — and how each site *reports*
//! failure — differs: the front door returns an in-memory `BackendProgram`
//! behind a `String` error and leaves `finish_session` to its caller (it also
//! reads the driver's session afterward for the activation/executable
//! inventory); the backend job publishes the `BackendProgram` fact behind a
//! `FatalError` and finishes the session itself. `ProductDriveError`
//! parameterizes exactly that seam so the loop body lives once.
use crate::telemetry::{TelemetryExt as _, opaque_debug};
use crate::{measurements, metadata};

use super::drive::{ExecutionContext, FactKey};
use super::facts::{FactReadiness, FactUse};
use super::identity::RootId;
use super::pull::{ProductDriver, ProductKey, ProductValue, PullOutcome, PullWait, WorldProductProducers};
use super::scheduler::{FatalError, WorkStartReason};
use super::world::World;
use super::{BackendProgram, Job};

/// A retry-budgeted stack expansion of this size backs both the outer product
/// pull and the inner fact-wait job drive, matching the pre-unification
/// budgets in both call sites.
pub(super) const PRODUCT_DRIVE_BUDGET: u64 = 50_000;

/// Reports one of the four ways a `RootBackendProduct` pull-drive can fail.
///
/// Each method receives the settled `World` so an implementation can read
/// context (e.g. `work_graph.unresolved()`) or emit a diagnostic; the loop
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
    /// The outer product-pull stack exhausted its budget before
    /// `RootBackendProduct` settled. `last_wait` is the last product key and
    /// waits observed, when any wait was ever recorded.
    fn did_not_settle<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        last_wait: Option<(ProductKey, Vec<PullWait>)>,
    ) -> Self;
}

/// Drives `root`'s `RootBackendProduct` to a settled `BackendProgram` through
/// the guarded product boundary, returning the program together with the
/// finished-but-not-yet-emitted driver so a caller can read the accumulated
/// session (e.g. the materialized executable inventory) before calling
/// `ProductDriver::finish_session`.
pub(crate) fn drive_root_backend_product<'a, T: crate::telemetry::Telemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &'a T,
    root: RootId,
) -> Result<(BackendProgram, ProductDriver<'a, T>), E> {
    drive_root_backend_product_with_budgets(world, tel, root, PRODUCT_DRIVE_BUDGET, PRODUCT_DRIVE_BUDGET)
}

/// The loop `drive_root_backend_product` runs, parameterized on the outer
/// product-stack budget and the inner per-fact-wait job budget. This is a
/// test-only seam: `drive_root_backend_product` always passes
/// `PRODUCT_DRIVE_BUDGET` for both, so production behavior is byte-identical
/// to before the split. Tests pass a small budget to force
/// `did_not_settle`/`fact_wait_budget_exceeded` on a genuine drive without
/// spending the real 50,000-job budget doing it.
pub(super) fn drive_root_backend_product_with_budgets<'a, T: crate::telemetry::Telemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &'a T,
    root: RootId,
    product_stack_budget: u64,
    fact_wait_budget: u64,
) -> Result<(BackendProgram, ProductDriver<'a, T>), E> {
    let root_key = ProductKey::RootBackendProduct(root);
    let mut driver = ProductDriver::new(tel, root);
    let mut stack = vec![root_key.clone()];
    let mut last_wait = None;
    for _ in 0..product_stack_budget {
        let Some(current) = stack.pop() else {
            stack.push(root_key.clone());
            continue;
        };
        let outcome = {
            let mut producers = WorldProductProducers::new(world, tel);
            driver.pull(&mut producers, current.clone())
        };
        match outcome {
            PullOutcome::Produced(ProductValue::RootBackendProduct(program)) if current == root_key => {
                driver.session_mut().record_work_starts(world.work_start_tally());
                ExecutionContext::new(world, tel).flush_reported_warnings();
                return Ok((*program, driver));
            }
            PullOutcome::Produced(_) => {}
            PullOutcome::Waiting(mut waits) => {
                // A pull that reports more than one wait built the list from
                // a `HashSet<PullWait>` upstream (the standing idiom for
                // wait-accumulator parameters throughout `jobs::runtime_demand`
                // and `jobs::artifact`), so its arrival order here is a
                // per-process `RandomState` artifact, not a property of the
                // program. This loop processes each wait to completion in
                // order — one poke-and-drain per iteration — so that order
                // decides which fact's producer job actually runs first,
                // which can flip a keep-first merge downstream. `PullWait`'s
                // constituents span too many identity types across the
                // compiler to give it a cheap structural `Ord`, but its
                // `Debug` rendering is pure data (ids and enum tags, no
                // addresses or hashes), so sorting by it is a valid,
                // deterministic total order — it only pins iteration order,
                // it does not change which wait is processed to completion.
                waits.sort_by_cached_key(|wait| format!("{wait:?}"));
                last_wait = Some((current.clone(), waits.clone()));
                stack.push(current);
                for wait in waits.into_iter().rev() {
                    match wait {
                        PullWait::Product(product) => stack.push(product),
                        PullWait::Fact(fact) => {
                            let producer_pokes =
                                drive_product_fact_wait::<T, E>(world, tel, root, fact, fact_wait_budget)?;
                            driver.session_mut().record_producer_pokes(producer_pokes);
                        }
                    }
                }
            }
        }
    }
    Err(E::did_not_settle(world, tel, root, last_wait))
}

/// The inner per-fact-wait job loop run while expanding a `PullWait::Fact`.
/// `pub(super)` so test scaffolding driving a `ProductKey` this module has no
/// dedicated runner for can still share this loop instead of forking it.
pub(super) fn drive_product_fact_wait<T: crate::telemetry::Telemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    fact: FactUse<FactKey>,
    fact_wait_budget: u64,
) -> Result<u64, E> {
    let mut jobs_ran = 0_u64;
    let mut producer_pokes = 0_u64;
    while !product_fact_wait_is_satisfied(world, &fact) {
        let job = match world.next_ready_job() {
            Some(job) => job,
            None => {
                producer_pokes += world.demand_fact_producer(fact.fact(), WorkStartReason::BlockedWaiterExpansion);
                let Some(job) = world.work_graph.pop() else {
                    return Err(E::no_ready_producer(world, tel, root, &fact));
                };
                job
            }
        };
        let job_span = tel.span_lazy(&["fz", "compiler2", "job"], || {
            metadata! {
                job: opaque_debug(&job),
            }
        });
        match super::jobs::run(&mut super::drive::ExecutionContext::new(world, tel), &job) {
            Ok(effects) => {
                jobs_ran += 1;
                job_span.stop_with_lazy(|| {
                    (
                        measurements! {},
                        metadata! {
                            effects: opaque_debug(&effects),
                        },
                    )
                });
                super::drive::ExecutionContext::new(world, tel).complete_job(job, effects);
            }
            Err(err) => {
                job_span.stop_with_lazy(|| (measurements! {}, metadata! {}));
                return Err(E::job_failed(world, tel, root, &fact, &job, err));
            }
        }
        if jobs_ran > fact_wait_budget {
            return Err(E::fact_wait_budget_exceeded(world, tel, root, &fact));
        }
    }
    Ok(producer_pokes)
}

fn product_fact_wait_is_satisfied(world: &World, fact: &FactUse<FactKey>) -> bool {
    match fact.readiness() {
        FactReadiness::Current => world.fact_revision(fact.fact()).is_some(),
        FactReadiness::Settled => world.fact_is_settled(fact.fact()),
    }
}
