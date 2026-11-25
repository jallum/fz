use super::*;
use crate::any_value::Stored;
use crate::park::park_test::{code_of, frame_of, leaked_site};
use std::time::Duration;

/// A bare scheduler for unit tests. The caller pushes tasks into
/// `tasks` and passes `sched_handle(&mut sched)` as the erased scheduler
/// handle the hooks re-narrow — the same handle `ExecCtx.scheduler`
/// carries in production.
fn test_scheduler() -> AotScheduler {
    AotScheduler {
        pool_outstanding_before_run: 0,
        log: None,
        tasks: ProcTable::new(),
        entry_thunk: null(),
        core: SchedulingCore::new(),
        drain_dtor_entry: null(),
        resume_addr: null(),
        argv: Argv::default(),
        ctx: ExecCtx::empty(),
    }
}

/// A process in the scheduler's table, as a spawn leaves one.
fn spawn_task(sched: &mut AotScheduler) -> &'static mut Process {
    let node = Rc::new(Node::empty());
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let process = sched
        .tasks
        .spawn(node, schemas, DEFAULT_REDUCTIONS_PER_QUANTUM)
        .expect("a test table has room");
    // SAFETY: the table keeps the process at its address until it exits or the table drops.
    unsafe { &mut *process }
}

fn sched_handle(sched: &mut AotScheduler) -> *mut () {
    sched as *mut AotScheduler as *mut ()
}

#[test]
fn parse_atom_blob_reads_every_name_the_length_covers() {
    let blob = b"ok\0err\0\0";
    let names = parse_atom_blob(blob.as_ptr(), blob.len() as u32);
    assert_eq!(names, ["ok", "err"]);
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
    assert_eq!(names, ["", "hello", "world"], "an empty name must not end the table",);

    let only_empty = b"\0\0";
    assert_eq!(parse_atom_blob(only_empty.as_ptr(), only_empty.len() as u32), [""]);

    let trailing_empty = b"a\0\0\0";
    assert_eq!(
        parse_atom_blob(trailing_empty.as_ptr(), trailing_empty.len() as u32),
        ["a", ""],
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

    let sender = spawn_task(&mut sched);
    let msg = sender
        .heap
        .alloc_list_cons_int(42, AnyValueRef::empty_list())
        .expect("sender list ref");
    let sender_addr = msg.list_addr().expect("sender list addr");

    let receiver = spawn_task(&mut sched);
    receiver.state = ProcessState::Blocked;
    let receiver_pid = receiver.pid;

    let receiver_bytes = receiver.heap.bytes_used();
    let sent = Stored::of_ref(msg);
    aot_send_hook(sender, sched_handle(&mut sched), receiver_pid, sent.word, sent.kind);

    let receiver = sched.tasks.get_mut(receiver_pid).expect("receiver");
    assert_eq!(
        receiver.delivery.lock().queued_gifts().count(),
        1,
        "the gift waits for the receiver's dispatch"
    );
    assert!(receiver.mailbox.is_empty());
    assert_eq!(
        receiver.heap.bytes_used(),
        receiver_bytes,
        "the sender never writes the receiver's heap"
    );
    deliver_in_queue(receiver);
    let copied = receiver.mailbox.front().expect("receiver mailbox");
    let copied_addr = copied.heap_ref().list_addr().expect("copied list addr");
    assert!(
        !receiver.heap.contains_heap_addr(copied_addr),
        "the message waits outside the receiver's heap until a receive takes it"
    );
    receiver.mailbox.take(0, &mut receiver.heap);
    assert_ne!(copied_addr, sender_addr);
    assert!(sender.heap.contains_heap_addr(sender_addr));
    assert!(
        receiver.heap.contains_heap_addr(copied_addr),
        "the receive that took the message brought it into the receiver's heap"
    );
}

/// Intent: a send to a pid that never named a process, or whose process has
/// exited, goes nowhere, even when a later process has taken the slot.
#[test]
fn aot_send_to_exited_or_unknown_pid_does_not_copy_or_schedule() {
    let mut sched = test_scheduler();

    let sender = spawn_task(&mut sched);
    let msg = sender
        .heap
        .alloc_list_cons_int(42, AnyValueRef::empty_list())
        .expect("sender list ref");
    let receiver = spawn_task(&mut sched);
    let dead_pid = receiver.pid;
    sched.tasks.retire(dead_pid);
    let successor_pid = loop {
        let successor = spawn_task(&mut sched);
        if crate::proc_table::pid_slot(successor.pid) == crate::proc_table::pid_slot(dead_pid) {
            break successor.pid;
        }
    };
    let before_heap = sched.tasks.get(successor_pid).unwrap().heap.node.alloc_stats();
    let before_queue = sched.core.queued().clone();

    let sent = Stored::of_ref(msg);
    aot_send_hook(sender, sched_handle(&mut sched), dead_pid, sent.word, sent.kind);
    aot_send_hook(sender, sched_handle(&mut sched), u32::MAX, sent.word, sent.kind);

    let successor = sched.tasks.get(successor_pid).unwrap();
    assert_eq!(successor.heap.node.alloc_stats(), before_heap);
    assert!(successor.mailbox.is_empty());
    assert_eq!(successor.delivery.lock().queued_gifts().count(), 0);
    assert_eq!(sched.core.queued(), &before_queue);
}

/// Schedule→expire→wake flow on the AOT scheduler. We can't
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
    extern "C" fn never_match(_process: *mut Process, _word: u64, _kind: u64, _frame: u64, _out: *mut Stored) -> u32 {
        0
    }
    let p = spawn_task(&mut sched);
    let timer_id = timer_schedule_hook::<AotScheduler>()(sched_handle(&mut sched), p.pid, 1);
    let after_code: usize = 0xCAFE_BABE;
    let frame = frame_of(&mut p.heap, &[]);
    p.delivery.lock().install_park(ParkRecord {
        site: leaked_site(never_match, Some((after_code, 0)), 0, &[]),
        frame,
        after_deadline_ms: Some(1),
        after_timer_id: Some(timer_id),
    });
    p.state = ProcessState::Blocked;
    let pid = p.pid;

    // The scheduling core waits out the deadline, wakes the task through
    // `fire_after_timer`, and hands its pid back as runnable.
    assert_eq!(next_runnable(&mut sched), Some(pid));

    let task = sched.tasks.get(pid).unwrap();
    assert_eq!(task.state, ProcessState::Ready);
    assert!(task.delivery.lock().park().is_none());
    assert_eq!(task.runnable_closure().map(code_of), Some(after_code));
    assert_eq!(next_runnable(&mut sched), None, "nothing else runs or waits");
}

/// The AOT timer cancel hook retires a previously scheduled
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

/// `fz_aot_set_resume_addr` records the shim address on the
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
    let process = fz_aot_setup(null(), 0, null(), pointers.len() as i32, pointers.as_ptr());
    let ctx = unsafe { &*(*process).ctx };
    assert_eq!(ctx.argv(), [b"--".to_vec(), Vec::new(), b"-x".to_vec()]);
}

#[test]
fn aot_setup_with_only_the_program_name_gives_the_empty_command_line() {
    use std::ffi::CString;
    let name = CString::new("./prog").unwrap();
    let pointers = [name.as_ptr()];
    let process = fz_aot_setup(null(), 0, null(), 1, pointers.as_ptr());
    let ctx = unsafe { &*(*process).ctx };
    assert!(ctx.argv().is_empty());
}

fn log_into(path: &std::path::Path) -> TelemetryLog {
    let file = OpenOptions::new().create(true).append(true).open(path).unwrap();
    TelemetryLog {
        file,
        epoch: Instant::now(),
        line: String::new(),
    }
}

/// A scheduler with a log appends one whole line per event after what the file
/// already holds, which is how a log the compiler wrote keeps its events first.
#[test]
fn an_observed_event_is_appended_as_one_whole_line() {
    let path = std::env::temp_dir().join(format!("fz_aot_observe_{}.jsonl", std::process::id()));
    std::fs::write(&path, "compile line\n").unwrap();
    let mut sched = test_scheduler();
    sched.log = Some(log_into(&path));

    sched.observe(RuntimeEvent::SchedulerSlept(Duration::from_nanos(7)));
    sched.observe(RuntimeEvent::ExecutionReady);

    let text = std::fs::read_to_string(&path).unwrap();
    std::fs::remove_file(&path).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 3, "{text}");
    assert_eq!(lines[0], "compile line");
    assert!(lines[1].starts_with("{\"name\":[\"fz\",\"runtime\",\"scheduler_slept\"],\"time_ns\":"));
    assert!(lines[1].ends_with("\"span_id\":0,\"parent_span_id\":0,\"measurements\":{},\"metadata\":{\"wait_ns\":7}}"));
    assert!(lines[2].contains("\"execution_ready\""));
    assert!(text.ends_with('\n'));
}

/// Without a log an observed event has nowhere to go and costs nothing.
#[test]
fn an_observed_event_without_a_log_is_dropped() {
    let mut sched = test_scheduler();
    sched.observe(RuntimeEvent::SchedulerSlept(Duration::from_nanos(7)));
    assert!(sched.log.is_none());
}

/// A matcher that takes every message as the receive's one clause, which binds
/// nothing.
extern "C" fn take_anything(_process: *mut Process, _word: u64, _kind: u64, _frame: u64, _out: *mut Stored) -> u32 {
    1
}

/// One process's whole life through the scheduler's hooks: spawned by `parent`,
/// parked in a receive, sent the message that matches, woken, and exited.
fn one_life(
    sched: &mut AotScheduler,
    parent: &mut Process,
    site: &'static crate::park::ReceiveSite,
    closure: AnyValueRef,
    msg: AnyValueRef,
) {
    use crate::park::ParkRecord;
    let pid = aot_spawn_hook(parent, sched_handle(sched), closure.raw_word());
    assert_eq!(next_runnable(sched), Some(pid), "a spawn queues the child");
    // SAFETY: the table keeps the child at its address until it exits.
    let child = unsafe { &mut *sched.tasks.get_ptr(pid).expect("the child") };
    child.state = ProcessState::Running;
    child.take_runnable_closure().expect("a spawned process has an entry");
    child.handlers.push_interpreter();
    child.handlers.pop();
    let frame = frame_of(&mut child.heap, &[]);
    child.delivery.lock().install_park(ParkRecord {
        site,
        frame,
        after_deadline_ms: None,
        after_timer_id: None,
    });
    child.state = ProcessState::Blocked;
    assert_eq!(end_quantum(sched, child), Disposition::Parked);

    let sent = Stored::of_ref(msg);
    aot_send_hook(parent, sched_handle(sched), pid, sent.word, sent.kind);
    assert_eq!(next_runnable(sched), Some(pid), "the matching message wakes the child");
    // SAFETY: as above.
    let child = unsafe { &mut *sched.tasks.get_ptr(pid).expect("the child") };
    child.state = ProcessState::Running;
    deliver_in_queue(child);
    child.take_runnable_closure().expect("a woken receive resumes");
    assert_eq!(end_quantum(sched, child), Disposition::Exited);
    assert!(sched.tasks.get(pid).is_none(), "an exited process leaves the table");
}

/// The allocations a life makes that belong to no shell: a debug build's heap
/// view snapshots the heap's address ranges for its ownership assertion, once
/// for the closure a spawn copies and once for the message a send copies.
const DEBUG_VIEW_RANGES: usize = if cfg!(debug_assertions) { 2 } else { 0 };

/// Intent: after the first process has grown the buffers a process needs, a
/// spawn, park, send, wake and exit allocates only what no shell owns (the
/// debug heap views above): the exited process's shell, with its gift queue,
/// mailbox, handler stack and lock, serves the next. Allocation calls are
/// counted on this thread over the whole cycle, through the scheduler's own
/// hooks.
#[test]
fn a_spawn_park_send_wake_exit_cycle_allocates_nothing_but_debug_views_after_the_first() {
    let mut sched = test_scheduler();
    sched.entry_thunk = 0x1000 as *const u8;
    let parent = spawn_task(&mut sched);
    let closure = frame_of(&mut parent.heap, &[]);
    let msg = closure;
    let site = leaked_site(
        take_anything,
        None,
        0,
        &[crate::park::ReceiveClause {
            code: 0x10,
            projector: None,
            root_count: 0,
            argument_count: 0,
            empty_slots: 0,
        }],
    );

    let ((), first) = crate::alloc_probe::allocations_during(|| one_life(&mut sched, parent, site, closure, msg));
    let rounds: Vec<usize> = (0..4)
        .map(|_| crate::alloc_probe::allocations_during(|| one_life(&mut sched, parent, site, closure, msg)).1)
        .collect();

    assert!(
        first > DEBUG_VIEW_RANGES,
        "the first life builds the shell and grows its buffers"
    );
    assert_eq!(
        rounds, [DEBUG_VIEW_RANGES; 4],
        "a reused shell allocates nothing; the first life made {first}"
    );
}
