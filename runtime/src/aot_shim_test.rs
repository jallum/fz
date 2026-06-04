use super::*;

/// A bare scheduler for unit tests. The caller pushes tasks into
/// `tasks` and passes `sched_handle(&mut sched)` as the erased scheduler
/// handle the hooks re-narrow — the same handle `ExecCtx.scheduler`
/// carries in production.
fn test_scheduler() -> AotScheduler {
    AotScheduler {
        next_pid: 2,
        tasks: HashMap::new(),
        entry_thunk: null(),
        halt_cont_bodies: [null(); 4],
        run_queue: VecDeque::new(),
        drain_dtor_entry: null(),
        resume_addr: null(),
        timers: TimerWheel::new(),
        ctx: ExecCtx::empty(),
    }
}

fn sched_handle(sched: &mut AotScheduler) -> *mut () {
    sched as *mut AotScheduler as *mut ()
}

#[test]
fn parse_atom_blob_walks_until_double_nul() {
    let blob = b"ok\0err\0\0";
    let names = parse_atom_blob(blob.as_ptr());
    assert_eq!(names, vec!["ok".to_string(), "err".to_string()]);
}

#[test]
fn parse_atom_blob_null_pointer_returns_empty() {
    let names = parse_atom_blob(null());
    assert!(names.is_empty());
}

#[test]
fn aot_send_deep_copies_message_into_receiver_heap() {
    let mut sched = test_scheduler();

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut sender = Box::new(Process::new(schemas.clone()));
    sender.pid = 1;
    let msg = sender
        .heap
        .alloc_list_cons_int(42, AnyValueRef::empty_list())
        .expect("sender list ref");
    let sender_addr = msg.list_addr().expect("sender list addr");

    let mut receiver = Box::new(Process::new(schemas));
    receiver.pid = 2;
    receiver.state = ProcessState::Blocked;

    sched.tasks.insert(1, sender);
    sched.tasks.insert(2, receiver);
    let sender_ptr = sched
        .tasks
        .get_mut(&1)
        .map(|p| p.as_mut() as *mut Process)
        .expect("sender task");

    aot_send_hook(sender_ptr, sched_handle(&mut sched), 2, msg.raw_word());

    let sender = sched.tasks.get(&1).expect("sender");
    let receiver = sched.tasks.get(&2).expect("receiver");
    let copied = receiver.mailbox.front().expect("receiver mailbox");
    let copied_addr = copied.list_addr().expect("copied list addr");
    assert_ne!(copied_addr, sender_addr);
    assert!(sender.heap.contains_heap_addr(sender_addr));
    assert!(receiver.heap.contains_heap_addr(copied_addr));
}

/// fz-xx8.3 — schedule→drain→wake flow on the AOT timer wheel.
/// Mirrors `src/runtime.rs::drain_expired_timers_wakes_after_cont`. We
/// can't drive aot_run_queue_loop directly (it would call into
/// codegen'd shim pointers we don't have), but we exercise every
/// pre-dispatch ingredient: schedule → expiry → mutate the task's
/// wait into a runnable_closure → run-queue enqueue. The
/// dispatch-via-resume-shim step is covered by the end-to-end fixture
/// run on a built binary.
#[test]
fn timer_drain_wakes_after_cont() {
    use crate::park::ParkRecord;

    let mut sched = test_scheduler();

    // Stand up a single task with a wait that has an
    // after_timer_id. matcher_fn is unused on the drain path.
    extern "C" fn never_match(
        _process: *mut Process,
        _msg: u64,
        _pinned: *const AnyValueRef,
        _out: *mut AnyValueRef,
    ) -> u32 {
        0
    }
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut p = Box::new(Process::new(schemas));
    p.pid = 7;
    let timer_id = aot_timer_schedule_hook(sched_handle(&mut sched), p.pid, 1);
    let after_cont_addr: usize = 0xCAFE_BABE;
    p.wait = Some(Box::new(ParkRecord {
        matcher_fn: never_match,
        pinned: vec![],
        clause_bodies: vec![],
        clause_bound_counts: vec![],
        bound_arity: 0,
        after_deadline_ms: Some(1),
        after_cont: after_cont_addr as *mut u8,
        after_timer_id: Some(timer_id),
    }));
    p.state = ProcessState::Blocked;
    sched.tasks.insert(7, p);

    // Wait past the deadline, then run the same drain logic
    // aot_run_queue_loop runs at the top of each iteration.
    sleep(Duration::from_millis(5));
    let expired = sched.timers.drain_expired(Instant::now());
    assert_eq!(expired.len(), 1);
    for entry in expired {
        {
            let task = sched.tasks.get_mut(&entry.pid).unwrap();
            let park = task.wait.as_ref().unwrap();
            assert_eq!(park.after_timer_id, Some(entry.id));
            let after_cont = park.after_cont;
            task.wait = None;
            task.set_runnable_closure(after_cont);
            task.state = ProcessState::Ready;
        }
        sched.run_queue.push_back(entry.pid);
    }

    let task = sched.tasks.get(&7).unwrap();
    assert_eq!(task.state, ProcessState::Ready);
    assert!(task.wait.is_none());
    assert_eq!(task.runnable_ptr() as usize, after_cont_addr);
    assert!(sched.run_queue.iter().any(|p| *p == 7));
}

/// fz-xx8.3 — `aot_timer_cancel_hook` retires a previously scheduled
/// timer so a sender-probe / initial-scan hit can prevent the after
/// from firing.
#[test]
fn timer_cancel_removes_pending_entry() {
    let mut sched = test_scheduler();

    let id = aot_timer_schedule_hook(sched_handle(&mut sched), 99, 10_000);
    assert!(sched.timers.next_deadline().is_some());
    aot_timer_cancel_hook(sched_handle(&mut sched), id);
    assert!(sched.timers.next_deadline().is_none());
}

/// fz-xx8.1 — `fz_aot_set_resume_addr` records the shim address on the
/// scheduler reached through `proc.ctx.scheduler`. We can't drive a full
/// setup→run→teardown cycle from a unit test (it needs a real codegen'd
/// shim), so we wire one process at the scheduler and assert the setter
/// lands the address on it.
#[test]
fn set_resume_addr_records_on_scheduler() {
    let mut sched = test_scheduler();
    let sched_ptr: *mut AotScheduler = &mut sched;
    sched.ctx.scheduler = sched_ptr as *mut ();

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut p = Box::new(Process::new(schemas));
    p.pid = 1;
    p.ctx = &mut sched.ctx;

    let fake = 0xDEAD_BEEFusize as *const u8;
    unsafe { fz_aot_set_resume_addr(p.as_mut(), fake) };
    assert_eq!(sched.resume_addr, fake);
}
