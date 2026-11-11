use super::*;
use crate::any_value::{
    AnyValue, ClosureDenotationId, EMPTY_LIST, closure_addr_from_tagged, closure_capture_set, closure_capture_value,
    list_addr_from_tagged,
};
use crate::heap::{Heap, SchemaRegistry};
use crate::process::{Collection, GcBoundary, ProcessState};
use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// A scheduler whose only behaviour is to record what the shared loop asks of
/// it. It keeps a state word per pid so the core has something to transition.
struct Recording {
    core: SchedulingCore,
    states: HashMap<PidId, ProcessState>,
    wakes_process: bool,
    woken: Vec<(PidId, TimerId)>,
    slept: Vec<Duration>,
    collections: Vec<Collection>,
    /// The pid and `dtors_dispatched` of each process at the moment its exit
    /// was observed.
    exits: Vec<(PidId, u64)>,
    destructors: Vec<(u64, u64)>,
}

impl Recording {
    fn new() -> Self {
        Self {
            core: SchedulingCore::new(),
            states: HashMap::new(),
            wakes_process: true,
            woken: Vec::new(),
            slept: Vec::new(),
            collections: Vec::new(),
            exits: Vec::new(),
            destructors: Vec::new(),
        }
    }

    /// Ask the core to make `pid` runnable from whatever state it last had; a
    /// pid never seen before starts out New.
    fn make_runnable(&mut self, pid: PidId) -> bool {
        let state = self.states.entry(pid).or_insert(ProcessState::New);
        self.core.make_runnable(pid, state)
    }

    fn state(&self, pid: PidId) -> ProcessState {
        self.states[&pid]
    }
}

impl Scheduler for Recording {
    fn core(&mut self) -> &mut SchedulingCore {
        &mut self.core
    }

    fn wake_expired(&mut self, pid: PidId, timer: TimerId) {
        self.woken.push((pid, timer));
        if self.wakes_process {
            self.make_runnable(pid);
        }
    }

    fn observe(&mut self, event: RuntimeEvent<'_>) {
        match event {
            RuntimeEvent::SchedulerSlept(wait) => self.slept.push(wait),
            RuntimeEvent::Gc(collection) => self.collections.push(*collection),
            RuntimeEvent::ProcessExited(process) => self.exits.push((process.pid, process.dtors_dispatched)),
            RuntimeEvent::ExecutionReady | RuntimeEvent::SendProbe(_) | RuntimeEvent::RunEnded(_) => {}
        }
    }

    fn run_destructor(&mut self, _process: &mut Process, closure: u64, payload: u64) {
        self.destructors.push((closure, payload));
    }
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

fn queued(s: &Recording) -> Vec<PidId> {
    s.core.queued().iter().copied().collect()
}

#[test]
fn a_blocked_process_woken_once_is_queued_once_and_marked_ready() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);

    assert!(s.make_runnable(7), "this wake is the one that made it runnable");
    assert_eq!(s.state(7), ProcessState::Ready);
    assert_eq!(queued(&s), vec![7]);
}

#[test]
fn a_second_wake_of_a_ready_process_does_not_queue_it_again() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    assert!(s.make_runnable(7));

    assert!(!s.make_runnable(7), "already queued: nothing newly runnable");
    assert_eq!(queued(&s), vec![7]);
    assert_eq!(next_runnable(&mut s), Some(7));
    assert_eq!(next_runnable(&mut s), None, "two wakes, one run");
}

#[test]
fn repeated_wakes_leave_the_queue_order_unchanged() {
    let mut s = Recording::new();
    for pid in [3, 1, 2] {
        s.states.insert(pid, ProcessState::Blocked);
    }

    s.make_runnable(3);
    s.make_runnable(1);
    s.make_runnable(3);
    s.make_runnable(2);
    s.make_runnable(1);

    assert_eq!(queued(&s), vec![3, 1, 2]);
}

#[test]
fn a_new_process_is_queued_by_its_first_wake() {
    let mut s = Recording::new();
    s.states.insert(4, ProcessState::New);

    assert!(s.make_runnable(4));
    assert_eq!(s.state(4), ProcessState::Ready);
    assert_eq!(queued(&s), vec![4]);
}

#[test]
fn a_running_process_that_yields_is_queued_behind_the_others() {
    let mut s = Recording::new();
    s.states.insert(1, ProcessState::Running);
    s.states.insert(2, ProcessState::Blocked);
    s.make_runnable(2);

    assert!(s.make_runnable(1));
    assert_eq!(s.state(1), ProcessState::Ready);
    assert_eq!(queued(&s), vec![2, 1]);
}

#[test]
fn an_exited_process_is_never_queued() {
    let mut s = Recording::new();
    s.states.insert(9, ProcessState::Exited);

    assert!(!s.make_runnable(9));
    assert_eq!(s.state(9), ProcessState::Exited);
    assert!(queued(&s).is_empty());
}

#[test]
fn an_empty_core_is_idle_without_sleeping() {
    let mut s = Recording::new();
    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty());
}

#[test]
fn runnable_processes_come_out_in_queue_order_and_then_idle() {
    let mut s = Recording::new();
    s.make_runnable(3);
    s.make_runnable(1);
    s.make_runnable(2);
    assert_eq!(next_runnable(&mut s), Some(3));
    assert_eq!(next_runnable(&mut s), Some(1));
    assert_eq!(next_runnable(&mut s), Some(2));
    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty(), "a runnable queue never sleeps");
}

#[test]
fn a_pending_timer_keeps_the_core_from_idling_until_it_fires() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    let timer = s.core.schedule_timer(7, ms(20));
    let started = Instant::now();

    assert_eq!(
        next_runnable(&mut s),
        Some(7),
        "the timer's process runs once it expires"
    );

    assert!(started.elapsed() >= ms(20), "the core slept out the whole deadline");
    assert_eq!(s.woken, vec![(7, timer)]);
    assert_eq!(s.state(7), ProcessState::Ready, "the wake went through the core");
    assert_eq!(s.slept.len(), 1, "one sleep is reported for one timer wait");
    assert!(s.slept[0] <= ms(20) && s.slept[0] > Duration::ZERO);
    assert_eq!(next_runnable(&mut s), None, "idle once the timer is spent");
}

#[test]
fn a_timer_firing_for_a_process_a_message_already_queued_does_not_queue_it_twice() {
    let mut s = Recording::new();
    s.states.insert(7, ProcessState::Blocked);
    s.core.schedule_timer(7, ms(5));
    s.make_runnable(7);

    assert_eq!(next_runnable(&mut s), Some(7), "the message's wake runs first");
    assert!(s.slept.is_empty(), "no sleep while something can run");
    assert_eq!(
        next_runnable(&mut s),
        None,
        "the late timer finds it Ready and queues nothing"
    );
    assert_eq!(s.woken.len(), 1, "the timer still expired and was offered");
}

#[test]
fn a_cancelled_timer_does_not_hold_the_core_open() {
    let mut s = Recording::new();
    let timer = s.core.schedule_timer(7, ms(10_000));
    s.core.cancel_timer(timer);

    assert_eq!(next_runnable(&mut s), None);
    assert!(s.slept.is_empty());
    assert!(s.woken.is_empty());
}

#[test]
fn a_timer_whose_process_is_already_awake_is_not_queued() {
    let mut s = Recording::new();
    s.wakes_process = false;
    s.core.schedule_timer(7, ms(5));

    assert_eq!(next_runnable(&mut s), None);
    assert_eq!(s.woken.len(), 1);
    assert_eq!(s.slept.len(), 1, "the stale timer was still waited for, then dropped");
}

#[test]
fn runnable_work_runs_before_a_pending_timer_is_waited_for() {
    let mut s = Recording::new();
    s.core.schedule_timer(9, ms(15));
    s.make_runnable(1);

    assert_eq!(next_runnable(&mut s), Some(1));
    assert!(s.slept.is_empty(), "no sleep while something can run");
    assert_eq!(next_runnable(&mut s), Some(9));
    assert_eq!(s.slept.len(), 1);
}

#[test]
fn staggered_timers_wake_in_deadline_order() {
    let mut s = Recording::new();
    s.core.schedule_timer(1, ms(40));
    s.core.schedule_timer(2, ms(10));

    assert_eq!(next_runnable(&mut s), Some(2));
    assert_eq!(next_runnable(&mut s), Some(1));
    assert_eq!(next_runnable(&mut s), None);
    assert_eq!(s.slept.len(), 2);
}

#[test]
fn the_timer_hooks_schedule_and_cancel_through_the_scheduler_handle() {
    let mut s = Recording::new();
    let handle = &mut s as *mut Recording as *mut ();

    let id = timer_schedule_hook::<Recording>()(handle, 4, 10_000);
    assert!(s.core.next_deadline().is_some());
    timer_cancel_hook::<Recording>()(handle, id);
    assert!(s.core.next_deadline().is_none());
    timer_cancel_hook::<Recording>()(std::ptr::null_mut(), id);
}

// ===== end_quantum ==========================================================

fn new_process() -> Process {
    Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))
}

fn int_list(heap: &mut Heap, head: i64) -> AnyValueRef {
    let bits = heap.alloc_list_cons_slot(AnyValue::int(head), EMPTY_LIST);
    AnyValueRef::from_heap_object(ValueKind::LIST, list_addr_from_tagged(bits).expect("list addr")).expect("list ref")
}

/// A closure capturing `value`, as a destructor or a continuation does.
fn closure_ref_capturing(process: &mut Process, value: AnyValue) -> AnyValueRef {
    let bits = process.heap.alloc_closure_slots(ClosureDenotationId::user(0), 0, 1, 0);
    let closure = closure_addr_from_tagged(bits).expect("closure addr");
    unsafe { closure_capture_set(closure, 0, value) };
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure).expect("closure ref")
}

fn closure_capturing(process: &mut Process, value: AnyValue) -> AnyValue {
    AnyValue::HeapRef(closure_ref_capturing(process, value))
}

/// Make a resource whose destructor closure captures a one-cell list headed by
/// `tag`, and return the stub's value so a caller can keep it reachable.
fn make_resource(process: &mut Process, payload: u64, tag: i64) -> AnyValue {
    let list = int_list(&mut process.heap, tag);
    let closure = closure_capturing(process, AnyValue::HeapRef(list));
    let stub = alloc_resource(
        &mut process.heap,
        ResourceHandle::new(payload, fz_resource_destructor_noop),
        closure,
    );
    AnyValue::heap_ptr(stub.as_raw(), ValueKind::RESOURCE)
}

fn make_yielding(process: &mut Process) {
    let runnable = closure_ref_capturing(process, AnyValue::int(0));
    process.set_runnable_closure(runnable);
    process.state = ProcessState::Running;
}

fn allocate_until_due(process: &mut Process) {
    while !process.needs_boundary_gc() {
        int_list(&mut process.heap, 0);
    }
}

/// The list head a dispatched destructor's closure captured, read back from
/// the closure word the scheduler handed to the driver.
fn captured_tag(closure: u64) -> i64 {
    let closure = AnyValueRef::from_raw_word(closure)
        .expect("closure ref")
        .closure_addr()
        .expect("closure");
    match unsafe { closure_capture_value(closure, 0) } {
        AnyValue::HeapRef(list) => {
            unsafe { (*(list.list_addr().expect("list addr") as *const crate::any_value::ListCons)).head_value() }.raw()
                as i64
        }
        other => panic!("the destructor closure captured a list: {other:?}"),
    }
}

fn payload_of(payload_ref: u64) -> i64 {
    let value = AnyValueRef::from_raw_word(payload_ref).expect("payload ref");
    assert_eq!(value.tag(), ValueKind::INT);
    value.storage_raw().expect("scalar slot") as i64
}

/// A resource whose last reference died in the heap a collection just moved
/// still has its destructor run: the closure and what it captured survive the
/// collection, and the dispatch happens at the same boundary.
#[test]
fn a_resource_freed_by_a_collection_has_its_destructor_dispatched_at_the_boundary() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    make_yielding(&mut process);
    make_resource(&mut process, 77, 4242);
    allocate_until_due(&mut process);

    let disposition = end_quantum(&mut scheduler, &mut process);

    assert_eq!(disposition, Disposition::Requeue);
    let [collection] = scheduler.collections[..] else {
        panic!(
            "a heap past its threshold is collected once: {:?}",
            scheduler.collections
        );
    };
    assert_eq!(collection.boundary, GcBoundary::Yield);
    assert_eq!(scheduler.destructors.len(), 1, "one dead resource, one dispatch");
    let (closure, payload) = scheduler.destructors[0];
    assert_eq!(
        captured_tag(closure),
        4242,
        "the closure's captures outlive the from-space"
    );
    assert_eq!(payload_of(payload), 77);
    assert_eq!(process.dtors_dispatched, 1);
    assert!(process.heap.pending_dtors.is_empty());
    assert_eq!(process.heap.mso_head, 0, "the dead stub left the chain");
}

/// A resource the process still holds is not dead: the collection keeps its
/// stub on the chain and no destructor runs.
#[test]
fn a_resource_the_process_still_holds_survives_the_collection_undisturbed() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    let stub = make_resource(&mut process, 5, 1);
    let runnable = closure_ref_capturing(&mut process, stub);
    process.set_runnable_closure(runnable);
    process.state = ProcessState::Running;
    allocate_until_due(&mut process);

    end_quantum(&mut scheduler, &mut process);

    assert_eq!(scheduler.collections.len(), 1);
    assert!(scheduler.destructors.is_empty());
    assert_ne!(process.heap.mso_head, 0, "the live stub stays on the chain");
    assert_eq!(process.dtors_dispatched, 0);
}

/// Exit is the same decision with nothing live: a halted process whose heap is
/// not due for a collection still has every resource's destructor dispatched,
/// and it is marked Exited.
#[test]
fn a_halted_process_dispatches_the_destructor_of_every_resource_it_held() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    process.state = ProcessState::Running;
    make_resource(&mut process, 10, 1);
    make_resource(&mut process, 20, 2);
    assert!(!process.needs_boundary_gc());

    let disposition = end_quantum(&mut scheduler, &mut process);

    assert_eq!(disposition, Disposition::Exited);
    assert!(
        scheduler.collections.is_empty(),
        "exit sweeps the chain without a to-space"
    );
    assert_eq!(process.state, ProcessState::Exited);
    let dispatched: Vec<(i64, i64)> = scheduler
        .destructors
        .iter()
        .map(|&(closure, payload)| (captured_tag(closure), payload_of(payload)))
        .collect();
    assert_eq!(
        dispatched,
        vec![(2, 20), (1, 10)],
        "newest resource first, as the chain runs"
    );
    assert_eq!(process.dtors_dispatched, 2);
}

/// The exit is observed once the process's destructors have run, so the
/// record the observer reads counts the ones the exit itself dispatched.
#[test]
fn an_exit_is_observed_after_its_destructors_have_run() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    process.state = ProcessState::Running;
    process.pid = 6;
    make_resource(&mut process, 10, 1);
    make_resource(&mut process, 20, 2);

    end_quantum(&mut scheduler, &mut process);

    assert_eq!(scheduler.exits, vec![(6, 2)]);
}

/// A halted process whose heap is due is collected like any other, and the
/// resources that collection freed are dispatched exactly once: the exit sweep
/// that follows finds nothing left.
#[test]
fn a_halted_process_that_is_due_dispatches_each_destructor_once() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    process.state = ProcessState::Running;
    make_resource(&mut process, 9, 3);
    allocate_until_due(&mut process);

    let disposition = end_quantum(&mut scheduler, &mut process);

    assert_eq!(disposition, Disposition::Exited);
    assert_eq!(scheduler.collections.len(), 1);
    assert_eq!(scheduler.collections[0].boundary, GcBoundary::Exit);
    assert_eq!(scheduler.destructors.len(), 1);
    assert_eq!(process.dtors_dispatched, 1);
}

/// A process parked on a receive is trimmed and kept: the destructor of a
/// resource it dropped runs, the process itself is left for a wake-up.
#[test]
fn a_parked_process_runs_destructors_but_is_not_exited() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    process.state = ProcessState::Blocked;
    make_resource(&mut process, 3, 8);
    allocate_until_due(&mut process);

    let disposition = end_quantum(&mut scheduler, &mut process);

    assert_eq!(disposition, Disposition::Parked);
    assert_eq!(scheduler.collections.len(), 1);
    assert_eq!(scheduler.collections[0].boundary, GcBoundary::Park);
    assert!(scheduler.exits.is_empty(), "a park is not an exit");
    assert_eq!(scheduler.destructors.len(), 1);
    assert_eq!(process.state, ProcessState::Blocked);
}

/// A resource whose cleanup an owner claimed has no destructor to run.
#[test]
fn a_claimed_resource_dispatches_no_destructor() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    process.state = ProcessState::Running;
    let stub = make_resource(&mut process, 1, 1);
    let stub = unsafe { crate::resource::ResourceStub::from_raw(stub.heap_addr().expect("stub addr")) };
    assert!(stub.claim());

    end_quantum(&mut scheduler, &mut process);

    assert!(scheduler.destructors.is_empty());
    assert_eq!(process.dtors_dispatched, 0);
}

/// A destructor that yields would overwrite the process's own continuation, so
/// the core faults instead of continuing.
#[test]
#[should_panic(expected = "a destructor must finish within one quantum")]
fn a_destructor_that_yields_is_a_fault() {
    struct Yielding(Recording);
    impl Scheduler for Yielding {
        fn core(&mut self) -> &mut SchedulingCore {
            self.0.core()
        }
        fn wake_expired(&mut self, pid: PidId, timer: TimerId) {
            self.0.wake_expired(pid, timer);
        }
        fn observe(&mut self, event: RuntimeEvent<'_>) {
            self.0.observe(event);
        }
        fn run_destructor(&mut self, process: &mut Process, _closure: u64, _payload: u64) {
            let continuation = closure_ref_capturing(process, AnyValue::int(1));
            process.set_runnable_closure(continuation);
        }
    }
    let mut process = new_process();
    process.state = ProcessState::Running;
    make_resource(&mut process, 1, 1);

    end_quantum(&mut Yielding(Recording::new()), &mut process);
}

/// A claimed resource that a collection finds dead is released without a
/// destructor, and the collection does not need its closure.
#[test]
fn a_claimed_resource_freed_by_a_collection_dispatches_no_destructor() {
    let mut scheduler = Recording::new();
    let mut process = new_process();
    make_yielding(&mut process);
    let stub = make_resource(&mut process, 1, 1);
    let stub = unsafe { crate::resource::ResourceStub::from_raw(stub.heap_addr().expect("stub addr")) };
    assert!(stub.claim());
    allocate_until_due(&mut process);

    end_quantum(&mut scheduler, &mut process);

    assert_eq!(scheduler.collections.len(), 1);
    assert!(scheduler.destructors.is_empty());
    assert_eq!(process.heap.mso_head, 0);
}
