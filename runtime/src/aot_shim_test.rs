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
        core: SchedulingCore::new(),
        drain_dtor_entry: null(),
        resume_addr: null(),
        argv: Argv::default(),
        ctx: ExecCtx::empty(),
    }
}

fn sched_handle(sched: &mut AotScheduler) -> *mut () {
    sched as *mut AotScheduler as *mut ()
}

#[test]
fn parse_atom_blob_reads_every_name_the_length_covers() {
    let blob = b"ok\0err\0\0";
    let names = parse_atom_blob(blob.as_ptr(), blob.len() as u32);
    assert_eq!(names, vec!["ok".to_string(), "err".to_string()]);
}

/// An EMPTY atom name is a name, not the end of the blob.
///
/// Terminating on a zero-length name instead made `:""` truncate the table:
/// every atom interned after it vanished, so `dbg(:hello)` printed `:atom_4`
/// on the AOT door alone and `Atom.to_string` of it aborted the process. The
/// length is what bounds the scan.
#[test]
fn parse_atom_blob_keeps_names_after_an_empty_one() {
    let blob = b"\0hello\0world\0\0";
    let names = parse_atom_blob(blob.as_ptr(), blob.len() as u32);
    assert_eq!(
        names,
        vec![String::new(), "hello".to_string(), "world".to_string()],
        "an empty name must not end the table",
    );

    let only_empty = b"\0\0";
    assert_eq!(
        parse_atom_blob(only_empty.as_ptr(), only_empty.len() as u32),
        vec![String::new()]
    );

    let trailing_empty = b"a\0\0\0";
    assert_eq!(
        parse_atom_blob(trailing_empty.as_ptr(), trailing_empty.len() as u32),
        vec!["a".to_string(), String::new()],
    );
}

#[test]
fn parse_atom_blob_null_pointer_returns_empty() {
    let names = parse_atom_blob(null(), 0);
    assert!(names.is_empty());
}

#[test]
fn empty_closure_denotation_registration_has_no_work() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    fz_aot_register_closure_denotations(&mut process, null(), 0);
}

#[test]
fn named_schema_blob_preserves_module_segment_boundaries() {
    let mut blob = Vec::new();
    blob.extend(2u32.to_ne_bytes());
    for segments in [&["A.B"][..], &["A", "B"][..]] {
        blob.extend((segments.len() as u32).to_ne_bytes());
        for segment in segments {
            blob.extend((segment.len() as u32).to_ne_bytes());
            blob.extend(segment.as_bytes());
        }
        blob.extend(0u32.to_ne_bytes());
    }
    let schemas = parse_named_schema_blob(blob.as_ptr(), blob.len() as u32);
    assert_eq!(schemas[0].0.segments(), &["A.B"]);
    assert_eq!(schemas[1].0.segments(), &["A", "B"]);
    let mut registry = SchemaRegistry::new();
    let left = registry.register(Schema::named_struct(schemas[0].0.clone(), vec![]));
    let right = registry.register(Schema::named_struct(schemas[1].0.clone(), vec![]));
    assert_ne!(left, right, "transport must not merge distinct source module paths");
}

#[test]
fn aot_send_gifts_the_message_and_the_receiver_grafts_it_at_its_next_dispatch() {
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

    let receiver_bytes = sched.tasks[&2].heap.bytes_used();
    aot_send_hook(sender_ptr, sched_handle(&mut sched), 2, msg.raw_word());

    let receiver = sched.tasks.get_mut(&2).expect("receiver");
    assert_eq!(receiver.in_queue.len(), 1, "the gift waits for the receiver's dispatch");
    assert!(receiver.mailbox.is_empty());
    assert_eq!(
        receiver.heap.bytes_used(),
        receiver_bytes,
        "the sender never writes the receiver's heap"
    );
    deliver_in_queue(receiver);
    let sender = sched.tasks.get(&1).expect("sender");
    let receiver = sched.tasks.get(&2).expect("receiver");
    let copied = receiver.mailbox.front().expect("receiver mailbox");
    let copied_addr = copied.list_addr().expect("copied list addr");
    assert_ne!(copied_addr, sender_addr);
    assert!(sender.heap.contains_heap_addr(sender_addr));
    assert!(receiver.heap.contains_heap_addr(copied_addr));
}

#[test]
fn aot_send_to_exited_or_unknown_pid_does_not_copy_or_schedule() {
    let mut sched = test_scheduler();

    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut sender = Box::new(Process::new(schemas.clone()));
    sender.pid = 1;
    let msg = sender
        .heap
        .alloc_list_cons_int(42, AnyValueRef::empty_list())
        .expect("sender list ref");
    let mut receiver = Box::new(Process::new(schemas));
    receiver.pid = 2;
    receiver.state = ProcessState::Exited;
    sched.tasks.insert(1, sender);
    sched.tasks.insert(2, receiver);
    let sender_ptr = sched
        .tasks
        .get_mut(&1)
        .map(|p| p.as_mut() as *mut Process)
        .expect("sender task");
    let before_heap = sched.tasks[&2].heap.alloc_stats_snapshot();
    let before_mailbox = sched.tasks[&2].mailbox.clone();
    let before_queue = sched.core.queued().clone();

    aot_send_hook(sender_ptr, sched_handle(&mut sched), 2, msg.raw_word());
    aot_send_hook(sender_ptr, sched_handle(&mut sched), u32::MAX, msg.raw_word());

    assert_eq!(sched.tasks[&2].heap.alloc_stats_snapshot(), before_heap);
    assert_eq!(sched.tasks[&2].mailbox, before_mailbox);
    assert_eq!(sched.tasks[&2].state, ProcessState::Exited);
    assert_eq!(sched.core.queued(), &before_queue);
}

/// fz-xx8.3 — schedule→expire→wake flow on the AOT scheduler. We can't
/// drive aot_run_queue_loop directly (it would call into codegen'd shim
/// pointers we don't have), but `next_runnable` is the loop's whole
/// pre-dispatch step: schedule → expiry → the task's wait becomes a
/// runnable_closure → its pid comes back runnable. The
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
    let timer_id = timer_schedule_hook::<AotScheduler>()(sched_handle(&mut sched), p.pid, 1);
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

    // The scheduling core waits out the deadline, wakes the task through
    // `fire_after_timer`, and hands its pid back as runnable.
    assert_eq!(next_runnable(&mut sched), Some(7));

    let task = sched.tasks.get(&7).unwrap();
    assert_eq!(task.state, ProcessState::Ready);
    assert!(task.wait.is_none());
    assert_eq!(task.runnable_ptr() as usize, after_cont_addr);
    assert_eq!(next_runnable(&mut sched), None, "nothing else runs or waits");
}

/// fz-xx8.3 — the AOT timer cancel hook retires a previously scheduled
/// timer so a sender-probe hit can prevent the after
/// from firing.
#[test]
fn timer_cancel_removes_pending_entry() {
    let mut sched = test_scheduler();

    let id = timer_schedule_hook::<AotScheduler>()(sched_handle(&mut sched), 99, 10_000);
    assert!(sched.core.next_deadline().is_some());
    timer_cancel_hook::<AotScheduler>()(sched_handle(&mut sched), id);
    assert!(sched.core.next_deadline().is_none());
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

/// The built binary's C `main(argc, argv)` hands the program its command line:
/// everything after the program name, as the exact bytes the OS passed.
#[test]
fn aot_setup_gives_the_program_every_argument_after_the_program_name() {
    use std::ffi::CString;
    let words = ["./prog", "--", "", "-x"].map(|w| CString::new(w).unwrap());
    let pointers: Vec<*const std::ffi::c_char> = words.iter().map(|w| w.as_ptr()).collect();
    let process = fz_aot_setup(
        null(),
        0,
        null(),
        null(),
        null(),
        null(),
        null(),
        pointers.len() as i32,
        pointers.as_ptr(),
    );
    let ctx = unsafe { &*(*process).ctx };
    assert_eq!(ctx.argv(), [b"--".to_vec(), Vec::new(), b"-x".to_vec()]);
}

#[test]
fn aot_setup_with_only_the_program_name_gives_the_empty_command_line() {
    use std::ffi::CString;
    let name = CString::new("./prog").unwrap();
    let pointers = [name.as_ptr()];
    let process = fz_aot_setup(null(), 0, null(), null(), null(), null(), null(), 1, pointers.as_ptr());
    let ctx = unsafe { &*(*process).ctx };
    assert!(ctx.argv().is_empty());
}
