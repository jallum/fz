use super::{Disposition, Node, Process, ProcessState, YIELD_REASON_REDUCTIONS};
use crate::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, EMPTY_LIST, ValueKind, closure_addr_from_tagged, closure_capture_set,
    closure_capture_value, list_addr_from_tagged,
};
use crate::heap::{Heap, SchemaRegistry};
use crate::park::ParkRecord;
use std::cell::RefCell;
use std::ptr::null_mut;
use std::rc::Rc;

#[test]
fn node_compares_atoms_by_name_not_intern_id() {
    let node = Node::new(vec!["z".into(), "a".into(), "m".into()]);

    assert_eq!(node.cmp_atom_names(0, 1), std::cmp::Ordering::Greater);
    assert_eq!(node.cmp_atom_names(1, 2), std::cmp::Ordering::Less);
    assert_eq!(node.cmp_atom_names(2, 2), std::cmp::Ordering::Equal);
}

#[test]
fn reduction_budget_resets_and_spends() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 3;
    process.reset_reduction_budget();

    assert_eq!(process.reductions_remaining, 3);
    process.finish_yield_report(-1, YIELD_REASON_REDUCTIONS);
    assert_eq!(process.reductions_remaining, -1);
    assert_eq!(process.reductions_executed, 4);
    assert_eq!(process.reduction_yields, 1);
    assert_eq!(process.yield_reasons & YIELD_REASON_REDUCTIONS, YIELD_REASON_REDUCTIONS);
}

#[test]
fn finish_yield_report_charges_only_reduction_exhaustion() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 10;
    process.reset_reduction_budget();

    process.finish_yield_report(3, YIELD_REASON_REDUCTIONS);

    assert_eq!(process.reductions_remaining, 3);
    assert_eq!(process.reductions_executed, 7);
    assert_eq!(process.reduction_yields, 1);
    assert_eq!(process.yield_reasons, YIELD_REASON_REDUCTIONS);
}

#[test]
fn reset_reduction_budget_clears_yield_reasons() {
    let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    process.reductions_per_quantum = 5;
    process.reductions_remaining = 0;
    process.yield_reasons = YIELD_REASON_REDUCTIONS;

    process.reset_reduction_budget();

    assert_eq!(process.reductions_remaining, 5);
    assert_eq!(process.yield_reasons, 0);
}

fn int_list(heap: &mut Heap, head: i64) -> AnyValueRef {
    let bits = heap.alloc_list_cons_slot(AnyValue::int(head), EMPTY_LIST);
    AnyValueRef::from_heap_object(ValueKind::LIST, list_addr_from_tagged(bits).expect("list addr")).expect("list ref")
}

/// A closure capturing `list`, as a clause body or continuation does.
fn closure_capturing(process: &mut Process, list: AnyValueRef) -> AnyValueRef {
    let bits = process.heap.alloc_closure_slots(ClosureDenotationId::user(0), 0, 1, 0);
    let closure = closure_addr_from_tagged(bits).expect("closure addr");
    unsafe { closure_capture_set(closure, 0, AnyValue::HeapRef(list)) };
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure).expect("closure ref")
}

fn list_head(list: AnyValueRef) -> i64 {
    unsafe { (*(list.list_addr().expect("list addr") as *const crate::any_value::ListCons)).head_value() }.raw() as i64
}

fn captured_list(closure: AnyValueRef) -> AnyValueRef {
    match unsafe { closure_capture_value(closure.closure_addr().expect("closure addr"), 0) } {
        AnyValue::HeapRef(list) => list,
        other => panic!("a captured list stays a heap ref: {other:?}"),
    }
}

/// Matches a message whose list head equals the pinned list's head.
extern "C" fn pinned_head_matcher(
    _process: *mut Process,
    msg: u64,
    pinned: *const AnyValueRef,
    _out: *mut AnyValueRef,
) -> u32 {
    let pinned = unsafe { *pinned };
    let msg = AnyValueRef::from_raw_word(msg).expect("msg ref");
    u32::from(list_head(msg) == list_head(pinned))
}

fn park_on(process: &mut Process, pinned: AnyValueRef, bodies: Vec<AnyValueRef>, after_cont: Option<AnyValueRef>) {
    process.delivery.lock().install_park(ParkRecord {
        matcher_fn: pinned_head_matcher,
        pinned: vec![pinned],
        clause_bound_counts: vec![0; bodies.len()],
        clause_bodies: bodies,
        bound_arity: 0,
        after_deadline_ms: None,
        after_cont,
        after_timer_id: None,
    });
}

/// A collection moves everything the process holds into its heap: the
/// runnable closure, the parked receive's clause bodies, after body and
/// pinned values, the mailbox and the caller's transient values. Each is
/// forwarded and still reads as it did, so the parked receive still matches.
#[test]
fn collect_forwards_every_root_a_parked_process_holds() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let pinned = int_list(&mut process.heap, 1);
    let body_capture = int_list(&mut process.heap, 2);
    let after_capture = int_list(&mut process.heap, 3);
    let runnable_capture = int_list(&mut process.heap, 4);
    let mailbox_message = int_list(&mut process.heap, 5);
    let mut transient = [int_list(&mut process.heap, 6)];
    let body = closure_capturing(&mut process, body_capture);
    let after = closure_capturing(&mut process, after_capture);
    let runnable = closure_capturing(&mut process, runnable_capture);
    park_on(&mut process, pinned, vec![body], Some(after));
    process.set_runnable_closure(runnable);
    process.mailbox.push_back(mailbox_message);
    let before = (
        pinned.list_addr().unwrap(),
        body,
        after,
        runnable,
        mailbox_message.list_addr().unwrap(),
        transient[0].list_addr().unwrap(),
    );

    let stats = process.collect(&mut transient);

    let delivery = process.delivery.lock();
    let park = delivery.park().expect("still parked");
    assert_ne!(park.pinned[0].list_addr().unwrap(), before.0, "pinned value moved");
    assert_ne!(park.clause_bodies[0], before.1, "clause body moved");
    assert_ne!(park.after_cont, Some(before.2), "after body moved");
    assert_ne!(process.runnable_closure(), Some(before.3), "runnable closure moved");
    assert_ne!(
        process.mailbox[0].list_addr().unwrap(),
        before.4,
        "mailbox message moved"
    );
    assert_ne!(transient[0].list_addr().unwrap(), before.5, "transient value moved");
    assert_eq!(list_head(park.pinned[0]), 1);
    assert_eq!(list_head(captured_list(park.clause_bodies[0])), 2);
    assert_eq!(list_head(captured_list(park.after_cont.expect("after body"))), 3);
    assert_eq!(
        list_head(captured_list(process.runnable_closure().expect("runnable"))),
        4
    );
    assert_eq!(list_head(process.mailbox[0]), 5);
    assert_eq!(list_head(transient[0]), 6);
    let probe = int_list(&mut process.heap, 1);
    assert!(
        park.try_match(null_mut(), probe).is_some(),
        "the moved pinned value still matches"
    );
    assert_eq!(stats.root_heap_edges, 6);
}

/// A receive with no `after` has a null after body and a running process has
/// no park record: neither contributes a root.
#[test]
fn collect_roots_only_what_the_process_holds() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let capture = int_list(&mut process.heap, 7);
    let runnable = closure_capturing(&mut process, capture);
    process.set_runnable_closure(runnable);

    let running = process.collect(&mut []);
    assert_eq!(running.root_heap_edges, 1, "the runnable closure is the only root");
    assert_eq!(
        list_head(captured_list(process.runnable_closure().expect("runnable"))),
        7
    );

    let pinned = int_list(&mut process.heap, 8);
    let body_capture = int_list(&mut process.heap, 9);
    let body = closure_capturing(&mut process, body_capture);
    park_on(&mut process, pinned, vec![body], None);
    let parked = process.collect(&mut []);
    assert_eq!(
        parked.root_heap_edges, 3,
        "runnable, clause body, pinned value; no after body"
    );
    assert!(process.delivery.lock().park().unwrap().after_cont.is_none());
}

/// How a quantum ended is read off the process: runnable means it
/// yielded, blocked means it parked, anything else means it halted.
#[test]
fn quantum_end_is_read_off_the_process_state() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let capture = int_list(&mut process.heap, 7);
    let runnable = closure_capturing(&mut process, capture);
    process.set_runnable_closure(runnable);
    process.state = ProcessState::Running;
    assert_eq!(process.quantum_end(), Disposition::Requeue);
    process.state = ProcessState::Blocked;
    assert_eq!(process.quantum_end(), Disposition::Parked);
    process.state = ProcessState::Running;
    process.take_runnable_closure();
    assert_eq!(process.quantum_end(), Disposition::Exited);
}
