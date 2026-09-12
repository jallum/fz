//! Shared retained root-product request and pull-drive boundary.
//!
//! Backend and native front doors use one session lifecycle and one stack-based
//! pull to the same fixed point: pop a product key, pull it, and expand its
//! exact product/fact waits until the requested root product settles or the
//! budget runs out. A native pull retains the backend product it discovers
//! before lowering continues. The test-only bounded runner returns its fresh
//! driver so failure-contract tests can inspect it. `ProductDriveError` keeps
//! the production `String` and scheduler `FatalError` surfaces distinct without
//! duplicating the loop.
use std::rc::Rc;

use super::drive::{ExecutionContext, FactKey, ProductAddress};
use super::facts::{FactReadiness, FactUse};
use super::identity::RootId;
use super::ordered_worklist::OrderedWorklist;
use super::pull::{
    ProductDriver, ProductFailure, ProductKey, ProductRequestId, ProductSessions, ProductValidation, ProductValue,
    PullOutcome, PullWait, WorldProductProducers,
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

pub(crate) fn drive_retained_product<T: crate::telemetry::RawSpanTelemetry>(
    world: &mut World,
    tel: &T,
    sessions: &mut ProductSessions,
    address: ProductAddress,
) -> Result<ProductValue, FatalError> {
    with_retained_root_request(world, tel, sessions, address.root, |world, tel, sessions, driver, _| {
        drive_root_product_with_driver(
            world,
            tel,
            address.root,
            address.key,
            driver,
            Some(sessions),
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
        )
    })
}

impl<T: crate::telemetry::RawSpanTelemetry> ExecutionContext<'_, T> {
    pub(crate) fn drive_product_requests(&mut self) -> Result<bool, (ProductAddress, FatalError)> {
        let Some(sessions) = self.product_sessions.as_deref_mut() else {
            return Ok(false);
        };
        let mut drove = false;
        while let Some(address) = sessions.next_request() {
            if let Err(error) = drive_retained_product(self.world, self.telemetry, sessions, address.clone()) {
                sessions.retry_request(address.clone());
                return Err((address, error));
            }
            drove = true;
        }
        Ok(drove)
    }
}

fn delivered_facts(
    movements: &[super::facts::FactMovement<super::drive::DependencyKey>],
) -> Vec<super::facts::FactMovement<FactKey>> {
    movements
        .iter()
        .filter_map(|movement| {
            movement.key.fact().map(|fact| super::facts::FactMovement {
                key: fact.clone(),
                state: movement.state,
            })
        })
        .collect()
}

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
        last_wait: Option<(&ProductKey, &[PullWait])>,
    ) -> Self;
    fn product_failed<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        root: RootId,
        product: &ProductKey,
        failure: ProductFailure,
    ) -> Self;
    fn dependency_failed<T: crate::telemetry::Telemetry>(
        world: &World,
        tel: &T,
        address: ProductAddress,
        source: FatalError,
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
    let mut sessions = ProductSessions::default();
    let (session, _) = sessions.take(root, world.work_start_tally());
    let mut driver = ProductDriver::with_shared_session(tel, Rc::clone(&session));
    let result = drive_root_backend_product_with_driver(
        world,
        tel,
        root,
        &mut driver,
        Some(&mut sessions),
        product_stack_budget,
        fact_wait_budget,
    );
    sessions.finish_activation(root, &mut driver.session_mut(), world.work_start_tally());
    sessions.restore(session);
    let program = result?;
    Ok((program, driver))
}

pub(crate) fn drive_retained_root_backend_product<T: crate::telemetry::RawSpanTelemetry>(
    world: &mut World,
    tel: &T,
    sessions: &mut ProductSessions,
    root: RootId,
    timeout: Option<std::time::Duration>,
) -> Result<Rc<BackendProgram>, String> {
    with_reconciled_root_request(world, tel, sessions, root, timeout, |world, tel, sessions, driver| {
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
        let value = drive_root_product_with_driver::<T, String>(
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
    let mut driver = ProductDriver::with_shared_session(tel, session);
    let result = run(world, tel, sessions, &mut driver, retained);
    sessions.finish_activation(root, &mut driver.session_mut(), world.work_start_tally());
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
) -> Result<Rc<BackendProgram>, E> {
    let program = drive_root_backend_product_with_driver(
        world,
        tel,
        root,
        driver,
        Some(sessions),
        PRODUCT_DRIVE_BUDGET,
        PRODUCT_DRIVE_BUDGET,
    )?;
    Ok(program)
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
    let value = drive_root_product_with_driver(
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
        ProductValue::RootBackendProduct(answer) => Ok(Rc::clone(&answer)),
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
) -> Result<ProductValue, E> {
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
) -> Result<ProductValue, E> {
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

/// One observed wait owns its original keys. Frames and the budget diagnostic
/// share it; selection borrows an indexed key rather than copying its input.
struct ProductWaitBatch {
    owner: ProductKey,
    waits: Vec<PullWait>,
}

impl ProductWaitBatch {
    fn product(&self, index: usize) -> &ProductKey {
        let PullWait::Product(product) = &self.waits[index] else {
            unreachable!("product suffix")
        };
        product
    }
}

enum SelectedProduct {
    Owned(ProductKey),
    Wait { batch: Rc<ProductWaitBatch>, index: usize },
    Owner(Rc<ProductWaitBatch>),
}

impl SelectedProduct {
    fn key(&self) -> &ProductKey {
        match self {
            Self::Owned(key) => key,
            Self::Wait { batch, index } => batch.product(*index),
            Self::Owner(batch) => &batch.owner,
        }
    }

    fn into_owner(self) -> ProductKey {
        match self {
            Self::Owned(key) => key,
            // A child that also waits owns an independent batch, never a
            // parent handle that would retain completed ancestor batches.
            Self::Wait { batch, index } => batch.product(index).clone(),
            Self::Owner(batch) => {
                Rc::try_unwrap(batch)
                    .ok()
                    .expect("a completed batch releases its diagnostic before owner transfer")
                    .owner
            }
        }
    }
}

enum FrameProduct {
    Observed(usize),
    Admitted(ProductKey),
}

impl FrameProduct {
    fn key<'a>(&'a self, batch: &'a ProductWaitBatch) -> &'a ProductKey {
        match self {
            Self::Observed(index) => batch.product(*index),
            Self::Admitted(key) => key,
        }
    }

    fn select(self, batch: &Rc<ProductWaitBatch>) -> SelectedProduct {
        match self {
            Self::Observed(index) => SelectedProduct::Wait {
                batch: Rc::clone(batch),
                index,
            },
            Self::Admitted(key) => SelectedProduct::Owned(key),
        }
    }
}

struct ProductWaitFrame {
    batch: Rc<ProductWaitBatch>,
    request: Option<ProductRequestId>,
    products: OrderedWorklist<FrameProduct>,
}

impl ProductWaitFrame {
    fn take_selection(
        current: &mut Option<SelectedProduct>,
        request: Option<ProductRequestId>,
        waits: Vec<PullWait>,
        fact_count: usize,
    ) -> Self {
        let owner = current
            .take()
            .expect("waiting selection transfers to its frame")
            .into_owner();
        let products = OrderedWorklist::from_sorted((fact_count..waits.len()).map(FrameProduct::Observed).collect());
        Self {
            batch: Rc::new(ProductWaitBatch { owner, waits }),
            request,
            products,
        }
    }
}

fn discard_wait_frames<T: crate::telemetry::Telemetry>(
    stack: &mut Vec<ProductWaitFrame>,
    driver: &mut ProductDriver<'_, T>,
    from: usize,
    current: Option<&ProductKey>,
    work: &mut ProductValidation,
) -> Option<SelectedProduct> {
    if let Some(current) = current {
        release_selected(stack, driver, current, work);
    }
    let mut boundary = None;
    while stack.len() > from {
        let position = stack.len() - 1;
        let frame = stack.pop().expect("discarded wait frame");
        if let Some(request) = frame.request {
            for wait in frame.products.into_values() {
                driver.release_wait_frame_product(&frame.batch.owner, request, wait.key(&frame.batch));
            }
            driver.collect_wait_frame_work(&frame.batch.owner, work);
            driver.unregister_wait_frame(&frame.batch.owner, request, position);
        }
        if stack.len() > from {
            release_selected(stack, driver, &frame.batch.owner, work);
        }
        boundary = Some(SelectedProduct::Owner(frame.batch));
    }
    boundary
}

fn release_selected<T: crate::telemetry::Telemetry>(
    stack: &[ProductWaitFrame],
    driver: &mut ProductDriver<'_, T>,
    current: &ProductKey,
    work: &mut ProductValidation,
) {
    if let Some(frame) = stack.last()
        && let Some(request) = frame.request
    {
        driver.release_wait_frame_product(&frame.batch.owner, request, current);
        driver.collect_wait_frame_work(&frame.batch.owner, work);
    }
}

fn reconcile_wait_frames<T: crate::telemetry::Telemetry>(
    stack: &mut Vec<ProductWaitFrame>,
    driver: &mut ProductDriver<'_, T>,
    types: &super::types::Types,
    current: Option<&ProductKey>,
    work: &mut ProductValidation,
) -> Option<SelectedProduct> {
    let (position, request) = driver.reconcile_wait_frames(types)?;
    let frame = stack
        .get(position)
        .expect("a canceled observation still has its registered frame");
    assert_eq!(
        frame.request,
        Some(request),
        "cancellation identifies the actual waiting attempt"
    );
    discard_wait_frames(stack, driver, position, current, work)
}

fn next_waiting_product<T: crate::telemetry::Telemetry>(
    stack: &mut Vec<ProductWaitFrame>,
    driver: &mut ProductDriver<'_, T>,
    types: &super::types::Types,
    work: &mut ProductValidation,
) -> Option<SelectedProduct> {
    while let Some((position, request, product)) = driver.next_wait_frame_admission(work) {
        let frame = stack
            .get_mut(position)
            .expect("a live admission names its registered frame");
        assert_eq!(frame.request, Some(request));
        frame.products.push(FrameProduct::Admitted(product), |left, right| {
            work.ordering_comparisons += 1;
            left.key(&frame.batch).semantic_cmp(right.key(&frame.batch), types)
        });
    }
    let frame = stack.last_mut()?;
    while let Some(wait) = frame.products.pop(|left, right| {
        work.ordering_comparisons += 1;
        left.key(&frame.batch).semantic_cmp(right.key(&frame.batch), types)
    }) {
        let product = wait.key(&frame.batch);
        if driver.product_is_current(product) {
            if let Some(request) = frame.request {
                driver.release_wait_frame_product(&frame.batch.owner, request, product);
                driver.collect_wait_frame_work(&frame.batch.owner, work);
            }
            continue;
        }
        return Some(wait.select(&frame.batch));
    }
    let position = stack.len() - 1;
    let frame = stack.pop().expect("completed wait frame");
    if let Some(request) = frame.request {
        driver.unregister_wait_frame(&frame.batch.owner, request, position);
    }
    Some(SelectedProduct::Owner(frame.batch))
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
    mut pull: impl FnMut(&mut World, &mut ProductDriver<'_, T>, &ProductKey) -> PullOutcome,
) -> Result<ProductValue, E> {
    // `Vec::new` is allocation-free: a retained root hit returns before the
    // first wait pushes anything onto the expansion stack.
    let mut stack = Vec::new();
    let mut current = Some(SelectedProduct::Owned(root_key.clone()));
    let mut last_wait = None;
    let mut work = ProductValidation::default();
    let result = (|| {
        for _ in 0..product_stack_budget {
            if let Some(sessions) = sessions.as_deref_mut() {
                sessions.drain_active_movements(root, &mut driver.session_mut());
            }
            if let Some(owner) = reconcile_wait_frames(
                &mut stack,
                driver,
                world.types(),
                current.as_ref().map(SelectedProduct::key),
                &mut work,
            ) {
                current = Some(owner);
            }
            let outcome = pull(world, driver, current.as_ref().expect("selected product").key());
            if let Some(sessions) = sessions.as_deref_mut() {
                sessions.sync_subscriptions(root, &mut driver.session_mut());
                let changes = sessions.take_product_changes(root, world.types());
                ExecutionContext::with_product_sessions(world, tel, sessions).apply_product_changes(changes);
            }
            if let Some(owner) = reconcile_wait_frames(
                &mut stack,
                driver,
                world.types(),
                current.as_ref().map(SelectedProduct::key),
                &mut work,
            ) {
                current = Some(owner);
                continue;
            }
            match outcome {
                PullOutcome::Produced(value) => {
                    if current.as_ref().map(SelectedProduct::key) == Some(&root_key) {
                        ExecutionContext::new(world, tel).flush_reported_warnings();
                        return Ok(value);
                    }
                    release_selected(
                        &stack,
                        driver,
                        current.as_ref().expect("produced selection").key(),
                        &mut work,
                    );
                    current = Some(
                        next_waiting_product(&mut stack, driver, world.types(), &mut work)
                            .unwrap_or_else(|| SelectedProduct::Owned(root_key.clone())),
                    );
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
                    let owner = current.as_ref().expect("waiting selection").key();
                    let fact_count = waits
                        .iter()
                        .take_while(|wait| matches!(wait, PullWait::Fact(_)))
                        .count();
                    let request = driver.register_wait_frame(owner, stack.len());
                    if let Some(request) = request {
                        for wait in &waits[fact_count..] {
                            let PullWait::Product(product) = wait else {
                                unreachable!("product suffix")
                            };
                            driver.admit_wait_frame_product(owner, request, product);
                        }
                        driver.collect_wait_frame_work(owner, &mut work);
                    }
                    last_wait = None;
                    let frame = ProductWaitFrame::take_selection(&mut current, request, waits, fact_count);
                    let batch = Rc::clone(&frame.batch);
                    last_wait = Some(Rc::clone(&batch));
                    stack.push(frame);
                    let facts = batch.waits[..fact_count].iter().rev().map(|wait| {
                        let PullWait::Fact(fact) = wait else {
                            unreachable!("sorted fact prefix")
                        };
                        fact
                    });
                    let producer_pokes = drive_product_fact_waits_with_sessions::<T, E>(
                        world,
                        tel,
                        root,
                        driver,
                        sessions.as_deref_mut(),
                        facts,
                        fact_wait_budget,
                    )?;
                    driver.session_mut().record_producer_pokes(producer_pokes);
                    current = Some(
                        reconcile_wait_frames(
                            &mut stack,
                            driver,
                            world.types(),
                            current.as_ref().map(SelectedProduct::key),
                            &mut work,
                        )
                        .or_else(|| next_waiting_product(&mut stack, driver, world.types(), &mut work))
                        .expect("a waiting product leaves its owner on the pull stack"),
                    );
                }
                PullOutcome::Failed(failure) => {
                    return Err(E::product_failed(
                        world,
                        tel,
                        root,
                        current.as_ref().expect("failed selection").key(),
                        failure,
                    ));
                }
            }
        }
        Err(E::did_not_settle(
            world,
            tel,
            root,
            last_wait.as_ref().map(|batch| (&batch.owner, batch.waits.as_slice())),
        ))
    })();
    // A failed fact pump can leave a retirement notification. Consume it while
    // its positions still name this drive, then unregister only our own frames.
    let _ = driver.reconcile_wait_frames(world.types());
    let _ = discard_wait_frames(
        &mut stack,
        driver,
        0,
        current.as_ref().map(SelectedProduct::key),
        &mut work,
    );
    driver.finish_wait_frames();
    work.report(tel, &root_key);
    result
}

/// Orders a product producer's unordered wait set before the stack consumes
/// it. Fact waits use the World's semantic type key because they can contain
/// activation arrows whose raw handles and display strings are not identities.
pub(super) fn sort_product_waits(types: &super::types::Types, waits: &mut [PullWait]) {
    waits.sort_by(|left, right| compare_product_waits(types, left, right));
}

fn compare_product_waits(types: &super::types::Types, left: &PullWait, right: &PullWait) -> std::cmp::Ordering {
    match (left, right) {
        (PullWait::Fact(left), PullWait::Fact(right)) => left.semantic_cmp(right, types),
        (PullWait::Product(left), PullWait::Product(right)) => left.semantic_cmp(right, types),
        (PullWait::Fact(_), PullWait::Product(_)) => std::cmp::Ordering::Less,
        (PullWait::Product(_), PullWait::Fact(_)) => std::cmp::Ordering::Greater,
    }
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
    drive_product_fact_waits_with_sessions(world, tel, root, driver, None, std::iter::once(&fact), fact_wait_budget)
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
    drive_product_fact_waits_with_sessions(world, tel, root, driver, None, facts.iter(), fact_wait_budget)
}

fn drive_product_fact_waits_with_sessions<'facts, T: crate::telemetry::RawSpanTelemetry, E: ProductDriveError>(
    world: &mut World,
    tel: &T,
    root: RootId,
    driver: &mut ProductDriver<'_, T>,
    mut sessions: Option<&mut ProductSessions>,
    facts: impl Iterator<Item = &'facts FactUse<FactKey>> + Clone,
    fact_wait_budget: u64,
) -> Result<u64, E> {
    let mut producer_pokes = 0_u64;
    let settled_facts = facts
        .clone()
        .filter(|fact| fact.readiness() == super::facts::FactReadiness::Settled)
        .map(|fact| fact.fact().clone())
        .collect::<Vec<_>>();
    for fact in facts {
        let mut jobs_ran = 0_u64;
        loop {
            if let Some(sessions) = sessions.as_deref_mut() {
                sessions.drain_active_movements(root, &mut driver.session_mut());
            }
            if driver.wait_frames_canceled(world.types()) {
                return Ok(producer_pokes);
            }
            if product_fact_wait_is_satisfied(world, fact) {
                break;
            }
            if world.work_graph.pending_jobs() == 0
                && let Some(sessions) = sessions.as_deref_mut()
            {
                let mut context = ExecutionContext::with_product_sessions(world, tel, sessions);
                if context
                    .drive_product_requests()
                    .map_err(|(address, source)| E::dependency_failed(context.world, tel, address, source))?
                {
                    continue;
                }
            }
            let job = match world.next_ready_job(sessions.as_deref()) {
                Some(job) => {
                    apply_quiescence(world, tel, driver, sessions.as_deref_mut());
                    job
                }
                None => {
                    // One producer evaluation owns one exact prerequisite set.
                    // At a drain, arbitrate all of its settled questions in one
                    // scheduler step so their typed movements stay atomic.
                    world.settle_quiescent_with_sessions(&settled_facts, sessions.as_deref());
                    if apply_quiescence(world, tel, driver, sessions.as_deref_mut()) {
                        continue;
                    }
                    producer_pokes += world.demand_fact_producer(fact.fact(), WorkStartReason::BlockedWaiterExpansion);
                    let job = world.work_graph.pop();
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
                        driver.apply_fact_movements(&delivered_facts(&completion.step.movements));
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
            ExecutionContext::with_product_sessions(world, tel, sessions).publish_dependency_movements(&step.movements);
        }
    } else {
        for step in &steps {
            driver.apply_fact_movements(&delivered_facts(&step.movements));
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
        let outcome = ExecutionContext::with_product_sessions(world, telemetry, sessions).drain_pending_for(timeout);
        if let DriveOutcome::TimedOut { jobs_ran, pending_jobs } = outcome {
            return Err(format!(
                "compiler2 root {} exceeded 0 ms drive limit after {} jobs with {} pending",
                root.as_u32(),
                jobs_ran,
                pending_jobs,
            ));
        }
    }
    if world.work_graph.pending_jobs() == 0 || !retained {
        return Ok(());
    }
    let outcome = ExecutionContext::with_product_sessions(world, telemetry, sessions).drain_pending_for(timeout);
    interpret_request_drain(root, outcome)
}

fn drain_request_context<T: crate::telemetry::RawSpanTelemetry>(
    context: &mut ExecutionContext<'_, T>,
    root: RootId,
    timeout: Option<std::time::Duration>,
) -> Result<(), String> {
    if context.world.work_graph.pending_jobs() == 0 {
        return Ok(());
    }
    let outcome = context.drain_pending_for(timeout);
    interpret_request_drain(root, outcome)
}

fn interpret_request_drain(
    root: RootId,
    outcome: DriveOutcome<Job, super::drive::DependencyKey>,
) -> Result<(), String> {
    match outcome {
        DriveOutcome::Resolved => Ok(()),
        DriveOutcome::DependencyFailed { dependency } => Err(format!(
            "compiler2 root {} failed while producing {dependency:?}",
            root.as_u32()
        )),
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

#[cfg(test)]
mod wait_frame_tests {
    use super::*;
    use crate::compiler2::pull::{ProductProducers, ProductReadContext};
    use crate::telemetry::ConfiguredTelemetry;

    #[derive(Debug)]
    struct WaitStorage {
        buffer: *const PullWait,
        inputs: Vec<*const crate::compiler2::Ty>,
        message: String,
    }

    impl ProductDriveError for WaitStorage {
        fn job_failed<T: crate::telemetry::Telemetry>(
            _: &World,
            _: &T,
            _: RootId,
            _: &FactUse<FactKey>,
            _: &Job,
            _: FatalError,
        ) -> Self {
            panic!("unexpected job failure")
        }
        fn no_ready_producer<T: crate::telemetry::Telemetry>(
            _: &World,
            _: &T,
            _: RootId,
            _: &FactUse<FactKey>,
        ) -> Self {
            panic!("unexpected missing producer")
        }
        fn fact_wait_budget_exceeded<T: crate::telemetry::Telemetry>(
            _: &World,
            _: &T,
            _: RootId,
            _: &FactUse<FactKey>,
        ) -> Self {
            panic!("unexpected fact budget failure")
        }
        fn product_failed<T: crate::telemetry::Telemetry>(
            _: &World,
            _: &T,
            _: RootId,
            _: &ProductKey,
            _: ProductFailure,
        ) -> Self {
            panic!("unexpected product failure")
        }
        fn dependency_failed<T: crate::telemetry::Telemetry>(
            _: &World,
            _: &T,
            _: ProductAddress,
            _: FatalError,
        ) -> Self {
            panic!("unexpected dependency failure")
        }
        fn did_not_settle<T: crate::telemetry::Telemetry>(
            world: &World,
            tel: &T,
            root: RootId,
            last_wait: Option<(&ProductKey, &[PullWait])>,
        ) -> Self {
            let (_, waits) = last_wait.as_ref().expect("the drive observed a wait");
            Self {
                buffer: waits.as_ptr(),
                inputs: waits
                    .iter()
                    .filter_map(|wait| {
                        let PullWait::Product(key) = wait else { return None };
                        Some(positioned_input(key))
                    })
                    .collect(),
                message: String::did_not_settle(world, tel, root, last_wait),
            }
        }
    }

    fn positioned_key(arrow: crate::compiler2::Ty, id: u32) -> ProductKey {
        use crate::compiler2::transport::{ActivationSymbol, ExecutableSymbol, TransportPosition};
        ProductKey::TransportShape(TransportPosition::ExecutableReturn {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function: crate::compiler2::FunctionId::for_test(id),
                    arrow,
                    input: vec![arrow; 32].into_boxed_slice(),
                },
                need: crate::compiler2::identity::ExecutableNeed::Value,
            },
        })
    }

    fn positioned_input(key: &ProductKey) -> *const crate::compiler2::Ty {
        let ProductKey::TransportShape(position) = key else {
            panic!("expected a positioned product")
        };
        position.executable().activation.input.as_ptr()
    }

    #[test]
    fn budget_diagnostics_retain_the_original_wait_batch_even_after_its_frame_drains() {
        for (product_count, budget) in [(0, 1), (3, 1), (3, 4)] {
            let tel = ConfiguredTelemetry::new();
            let mut world = World::new();
            let root = RootId::for_test(91);
            let root_key = ProductKey::RootBackendProduct(root);
            let arrow = world.types_mut().any();
            let mut waits = (100..100 + product_count)
                .map(|id| PullWait::Product(positioned_key(arrow, id)))
                .collect::<Vec<_>>();
            sort_product_waits(world.types(), &mut waits);
            let buffer = waits.as_ptr();
            let inputs = waits
                .iter()
                .map(|wait| {
                    let PullWait::Product(key) = wait else { unreachable!() };
                    positioned_input(key)
                })
                .collect::<Vec<_>>();
            let expected_message = format!(
                "compiler2 root {} product backend did not settle; last wait: {:?}",
                root.as_u32(),
                Some((&root_key, &waits)),
            );
            let mut waits = Some(waits);
            let mut driver = ProductDriver::new(&tel, root);
            let error = drive_root_product_with::<_, WaitStorage>(
                &mut world,
                &tel,
                root,
                root_key.clone(),
                &mut driver,
                None,
                budget,
                PRODUCT_DRIVE_BUDGET,
                |_, _, key| {
                    if key == &root_key {
                        PullOutcome::Waiting(waits.take().expect("the budget ends before root retry"))
                    } else {
                        PullOutcome::Produced(ProductValue::Unit)
                    }
                },
            )
            .unwrap_err();
            assert_eq!(
                error.message, expected_message,
                "the full historic diagnostic survives frame consumption"
            );
            assert_eq!(
                error.buffer, buffer,
                "remembering a wait moves its vector rather than cloning it"
            );
            assert_eq!(
                error.inputs, inputs,
                "positioned input backing is shared, not duplicated for diagnostics"
            );
        }
    }

    #[test]
    fn the_latest_nested_mixed_wait_keeps_its_full_original_snapshot_after_completion() {
        for budget in [2, 4, 5] {
            let tel = ConfiguredTelemetry::new();
            let mut world = World::new();
            let code = world.submit_code(None, "def indexed_only() do\n 1\nend\n".to_owned());
            let root = RootId::for_test(95);
            let root_key = ProductKey::RootBackendProduct(root);
            let arrow = world.types_mut().any();
            let child = positioned_key(arrow, 100);
            let mut waits = vec![
                PullWait::Product(positioned_key(arrow, 102)),
                PullWait::Fact(FactUse::current(FactKey::CodeIndexed(code))),
                PullWait::Product(positioned_key(arrow, 101)),
            ];
            sort_product_waits(world.types(), &mut waits);
            let buffer = waits.as_ptr();
            let inputs = waits
                .iter()
                .filter_map(|wait| {
                    let PullWait::Product(key) = wait else { return None };
                    Some(positioned_input(key))
                })
                .collect::<Vec<_>>();
            let expected = format!(
                "compiler2 root {} product backend did not settle; last wait: {:?}",
                root.as_u32(),
                Some((&child, &waits)),
            );
            let mut waits = Some(waits);
            let mut selected_inputs = Vec::new();
            let mut driver = ProductDriver::new(&tel, root);
            let error = drive_root_product_with::<_, WaitStorage>(
                &mut world,
                &tel,
                root,
                root_key.clone(),
                &mut driver,
                None,
                budget,
                PRODUCT_DRIVE_BUDGET,
                |_, _, key| {
                    if key == &root_key {
                        PullOutcome::Waiting(vec![PullWait::Product(child.clone())])
                    } else if key == &child {
                        waits
                            .take()
                            .map_or(PullOutcome::Produced(ProductValue::Unit), PullOutcome::Waiting)
                    } else {
                        selected_inputs.push(positioned_input(key));
                        PullOutcome::Produced(ProductValue::Unit)
                    }
                },
            )
            .unwrap_err();
            assert!(
                world.fact_revision(&FactKey::CodeIndexed(code)).is_some(),
                "the mixed prefix drove its real fact producer"
            );
            assert_eq!(
                error.message, expected,
                "last_wait names the child, not the completed parent frame"
            );
            assert_eq!(error.buffer, buffer);
            assert_eq!(error.inputs, inputs);
            if budget >= 4 {
                assert_eq!(
                    selected_inputs, inputs,
                    "fact-prefix indices select each original product exactly once"
                );
            }
        }
    }

    #[test]
    fn product_index_storage_is_sized_once_for_the_exact_suffix() {
        for fact_count in [0, 2] {
            for product_count in [0, 1, 64, 1024] {
                let owner = ProductKey::RootBackendProduct(RootId::for_test(96));
                let mut waits = (0..fact_count)
                    .map(|id| PullWait::Fact(FactUse::current(FactKey::RootEntry(RootId::for_test(id as u32)))))
                    .collect::<Vec<_>>();
                waits.extend(
                    (0..product_count)
                        .map(|id| PullWait::Product(ProductKey::RootBackendProduct(RootId::for_test(id as u32)))),
                );
                let storage = waits.as_ptr();
                let frame =
                    ProductWaitFrame::take_selection(&mut Some(SelectedProduct::Owned(owner)), None, waits, fact_count);
                assert_eq!(frame.batch.waits.as_ptr(), storage);
                let indices = frame.products.into_values();
                assert_eq!(indices.len(), product_count);
                assert_eq!(
                    indices.capacity(),
                    product_count,
                    "the exact-size suffix does not grow an initially undersized heap"
                );
                assert!(indices.iter().enumerate().all(|(index, product)| matches!(product, FrameProduct::Observed(actual) if *actual == fact_count + index)));
            }
        }
    }

    #[test]
    fn a_failed_selected_product_cleans_up_before_the_same_driver_retries() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = RootId::for_test(97);
        let root_key = ProductKey::RootBackendProduct(root);
        let child = positioned_key(world.types_mut().any(), 100);
        let input = positioned_input(&child);
        let mut waits = Some(vec![PullWait::Product(child)]);
        let mut driver = ProductDriver::new(&tel, root);
        let error = drive_root_product_with::<_, String>(
            &mut world,
            &tel,
            root,
            root_key.clone(),
            &mut driver,
            None,
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
            |_, _, key| {
                if key == &root_key {
                    PullOutcome::Waiting(waits.take().unwrap())
                } else {
                    assert_eq!(
                        positioned_input(key),
                        input,
                        "a failed selection still borrows its original input"
                    );
                    PullOutcome::Failed(ProductFailure::NativeLowering)
                }
            },
        )
        .unwrap_err();
        assert!(
            error.contains("failed"),
            "the selected product owns its failure: {error}"
        );
        let mut pulls = 0;
        let result = drive_root_product_with::<_, String>(
            &mut world,
            &tel,
            root,
            root_key.clone(),
            &mut driver,
            None,
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
            |_, _, key| {
                pulls += 1;
                assert_eq!(key, &root_key, "no discarded child is requested on retry");
                PullOutcome::Produced(ProductValue::Unit)
            },
        );
        assert_eq!(result, Ok(ProductValue::Unit));
        assert_eq!(pulls, 1);
    }

    #[test]
    fn healthy_wait_selection_borrows_the_original_positioned_input() {
        struct Producers<'a> {
            world: &'a World,
            root: &'a ProductKey,
            waits: &'a mut Option<Vec<PullWait>>,
            input: *const crate::compiler2::Ty,
            child_pulls: &'a mut usize,
        }
        impl ProductProducers for Producers<'_> {
            fn product_types(&self) -> &crate::compiler2::Types {
                self.world.types()
            }
            fn produce(&mut self, _: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
                if key == self.root {
                    self.waits
                        .take()
                        .map_or(PullOutcome::Produced(ProductValue::Unit), PullOutcome::Waiting)
                } else {
                    *self.child_pulls += 1;
                    assert_eq!(
                        positioned_input(key),
                        self.input,
                        "selection and ProductDriver both borrow the original key"
                    );
                    PullOutcome::Produced(ProductValue::Unit)
                }
            }
        }
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let root = RootId::for_test(92);
        let root_key = ProductKey::RootBackendProduct(root);
        let child = positioned_key(world.types_mut().any(), 101);
        let input = positioned_input(&child);
        let mut waits = Some(vec![PullWait::Product(child)]);
        let mut driver = ProductDriver::new(&tel, root);
        let mut child_pulls = 0;
        let result = drive_root_product_with::<_, String>(
            &mut world,
            &tel,
            root,
            root_key.clone(),
            &mut driver,
            None,
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
            |world, driver, key| {
                driver.pull(
                    &mut Producers {
                        world,
                        root: &root_key,
                        waits: &mut waits,
                        input,
                        child_pulls: &mut child_pulls,
                    },
                    key,
                )
            },
        );
        assert_eq!(result, Ok(ProductValue::Unit));
        assert_eq!(child_pulls, 1);
    }

    #[test]
    fn canceling_nested_frames_releases_batches_without_copying_the_resumed_owner() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let arrow = world.types_mut().any();
        let root = RootId::for_test(93);
        let owner = positioned_key(arrow, 100);
        let owner_input = positioned_input(&owner);
        let child = positioned_key(arrow, 101);
        let child_input = positioned_input(&child);
        let mut current = Some(SelectedProduct::Owned(owner));
        let first = ProductWaitFrame::take_selection(&mut current, None, vec![PullWait::Product(child)], 0);
        let first_lifetime = Rc::downgrade(&first.batch);
        let mut stack = vec![first];
        let mut driver = ProductDriver::new(&tel, root);
        let mut work = ProductValidation::default();
        current = next_waiting_product(&mut stack, &mut driver, world.types(), &mut work);
        assert_eq!(positioned_input(current.as_ref().unwrap().key()), child_input);
        let second = ProductWaitFrame::take_selection(&mut current, None, Vec::new(), 0);
        let second_lifetime = Rc::downgrade(&second.batch);
        assert_ne!(
            positioned_input(&second.batch.owner),
            child_input,
            "only a child that waits needs one independent owner copy"
        );
        let last_wait = Rc::clone(&second.batch);
        stack.push(second);
        let boundary = discard_wait_frames(&mut stack, &mut driver, 0, None, &mut work).unwrap();
        assert!(stack.is_empty());
        assert_eq!(
            positioned_input(boundary.key()),
            owner_input,
            "canceling intermediate frames only moves handles"
        );
        drop(boundary);
        assert!(
            first_lifetime.upgrade().is_none(),
            "the latest diagnostic cannot retain its parent batch"
        );
        assert!(
            second_lifetime.upgrade().is_some(),
            "the last diagnostic alone retains its complete observation"
        );
        drop(last_wait);
        assert!(
            second_lifetime.upgrade().is_none(),
            "dropping the last diagnostic releases its observation"
        );
    }

    #[test]
    fn completed_owner_retry_moves_its_input_and_allocates_no_product_inventory_for_fact_only_waits() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let arrow = world.types_mut().any();
        let root = RootId::for_test(94);
        for waits in [
            Vec::new(),
            vec![PullWait::Fact(FactUse::current(FactKey::RootEntry(root)))],
        ] {
            let owner = positioned_key(arrow, 100);
            let input = positioned_input(&owner);
            let mut current = Some(SelectedProduct::Owned(owner));
            let fact_count = waits.len();
            let frame = ProductWaitFrame::take_selection(&mut current, None, waits, fact_count);
            assert_eq!(
                Rc::strong_count(&frame.batch),
                1,
                "the frame owns one shared batch allocation"
            );
            let old_batch = Rc::downgrade(&frame.batch);
            let mut last_wait = Some(Rc::clone(&frame.batch));
            assert_eq!(
                Rc::strong_count(&frame.batch),
                2,
                "the diagnostic shares that allocation"
            );
            let ProductWaitFrame {
                batch,
                request,
                products,
            } = frame;
            let products = products.into_values();
            assert_eq!(
                products.capacity(),
                0,
                "empty and fact-only batches need no product-index allocation"
            );
            let mut stack = vec![ProductWaitFrame {
                batch,
                request,
                products: OrderedWorklist::from_sorted(products),
            }];
            let mut driver = ProductDriver::new(&tel, root);
            current = next_waiting_product(
                &mut stack,
                &mut driver,
                world.types(),
                &mut ProductValidation::default(),
            );
            assert!(stack.is_empty());
            assert_eq!(positioned_input(current.as_ref().unwrap().key()), input);
            drop(last_wait.take());
            let replacement = ProductWaitFrame::take_selection(&mut current, None, Vec::new(), 0);
            assert_eq!(
                positioned_input(&replacement.batch.owner),
                input,
                "a drained owner moves into its next observation"
            );
            assert!(old_batch.upgrade().is_none());
        }
    }

    #[test]
    fn a_waiting_frame_takes_the_selected_positioned_key_without_copying_its_input() {
        use crate::compiler2::transport::{ActivationSymbol, ExecutableSymbol, TransportPosition};
        let arrow = crate::compiler2::Types::new().any();
        let input = vec![arrow; 32].into_boxed_slice();
        let storage = input.as_ptr();
        let mut selected = Some(SelectedProduct::Owned(ProductKey::TransportShape(
            TransportPosition::ExecutableReturn {
                executable: ExecutableSymbol {
                    activation: ActivationSymbol {
                        function: crate::compiler2::FunctionId::for_test(91),
                        arrow,
                        input,
                    },
                    need: crate::compiler2::identity::ExecutableNeed::Value,
                },
            },
        )));
        let frame = ProductWaitFrame::take_selection(&mut selected, None, Vec::new(), 0);
        assert!(
            selected.is_none(),
            "the suspended owner has exactly one current location"
        );
        let ProductKey::TransportShape(position) = &frame.batch.owner else {
            unreachable!()
        };
        assert_eq!(
            position.executable().activation.input.as_ptr(),
            storage,
            "suspending a selected key moves its boxed input rather than allocating a duplicate"
        );
    }

    #[test]
    fn a_product_wait_batch_drives_facts_in_descending_semantic_order() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let roots = ["missing_first", "missing_second"].map(|name| {
            world.submit_root(
                None,
                name.to_owned(),
                0,
                crate::compiler2::identity::ExecutableNeed::Value,
            )
        });
        let mut facts = roots.map(|root| FactUse::settled(FactKey::RootEntry(root)));
        facts.sort_by(|left, right| left.semantic_cmp(right, world.types()));
        let root = roots[0];
        let expected_fact = facts[1].clone();
        let waits = facts.into_iter().map(PullWait::Fact).collect::<Vec<_>>();
        let mut driver = ProductDriver::new(&tel, root);
        let result = drive_root_product_with::<_, String>(
            &mut world,
            &tel,
            root,
            ProductKey::RootBackendProduct(root),
            &mut driver,
            None,
            PRODUCT_DRIVE_BUDGET,
            PRODUCT_DRIVE_BUDGET,
            |_, _, _| PullOutcome::Waiting(waits.clone()),
        );
        let expected = <String as ProductDriveError>::no_ready_producer(&world, &tel, root, &expected_fact);
        assert_eq!(
            result,
            Err(expected),
            "the actual pump must begin with the last semantically sorted fact"
        );
    }

    #[test]
    fn a_fact_pump_rechecks_retired_demand_before_reporting_an_obsolete_missing_producer() {
        struct Producers<'a> {
            world: &'a World,
            tel: &'a ConfiguredTelemetry,
            indexed: FactKey,
            missing: FactKey,
            remove_after_index: bool,
            keys: [ProductKey; 4],
        }
        impl ProductProducers for Producers<'_> {
            fn product_types(&self) -> &crate::compiler2::Types {
                self.world.types()
            }
            fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
                let [owner, old_seed, empty_seed, child] = &self.keys;
                if key == owner {
                    let indexed = context.read_fact(self.world, FactUse::current(self.indexed.clone()));
                    let seed = if indexed && self.remove_after_index {
                        empty_seed
                    } else {
                        old_seed
                    };
                    return match context.read_rooted_products(self.tel, key.clone(), seed.clone(), self.world.types()) {
                        Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                        Err(waits) => PullOutcome::Waiting(waits),
                    };
                }
                if key == old_seed {
                    context.include_product(child.clone());
                }
                if key == child {
                    let fact = FactUse::settled(self.missing.clone());
                    if !context.read_fact(self.world, fact.clone()) {
                        return PullOutcome::wait_on_fact(fact);
                    }
                }
                PullOutcome::Produced(ProductValue::Unit)
            }
        }
        for remove_after_index in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let mut world = World::new();
            let code = world.submit_code(None, "def indexed_only() do\n 1\nend\n".to_owned());
            let root = world.submit_root(
                None,
                "undefined_wait_entry".to_owned(),
                0,
                crate::compiler2::identity::ExecutableNeed::Value,
            );
            let keys = [100, 101, 102, 103].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
            let mut driver = ProductDriver::new(&tel, root);
            let result = drive_root_product_with::<_, String>(
                &mut world,
                &tel,
                root,
                keys[0].clone(),
                &mut driver,
                None,
                PRODUCT_DRIVE_BUDGET,
                PRODUCT_DRIVE_BUDGET,
                |world, driver, current| {
                    driver.pull(
                        &mut Producers {
                            world,
                            tel: &tel,
                            indexed: FactKey::CodeIndexed(code),
                            missing: FactKey::RootEntry(root),
                            remove_after_index,
                            keys: keys.clone(),
                        },
                        current,
                    )
                },
            );
            if remove_after_index {
                assert_eq!(
                    result,
                    Ok(ProductValue::Unit),
                    "IndexCode retires the observation that owned the undefined-root wait"
                );
            } else {
                let error = result.unwrap_err();
                assert!(
                    error.contains("no ready producer"),
                    "a still-required undefined root remains an error: {error}"
                );
            }
        }
    }
}
