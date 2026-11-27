use super::{Disposition, Node, Process, ProcessState, YIELD_REASON_EXPLICIT, YIELD_REASON_REDUCTIONS};
use crate::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, EMPTY_LIST, Stored, ValueKind, closure_addr_from_tagged,
    closure_capture_set, closure_capture_value, list_addr_from_tagged,
};
use crate::handler_stack::Innermost;
use crate::handler_stack::handler_stack_test::push_template;
use crate::heap::{GcStats, Heap, Roots, SchemaRegistry};
use crate::park::park_test::{frame_of, leaked_site};
use crate::park::{ParkRecord, ReceiveClause};
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

/// Intent: two atoms order by name whether or not they are the same atom, so
/// the answer for one id against itself needs no table read.
#[test]
fn node_orders_atom_ids_as_their_names_do() {
    let node = Node::empty();
    let names = ["", "a", "a\0", "a\0b", "eight888a", "eight888b", "é", "true", "zebra"];
    let ids: Vec<u32> = names.iter().rev().map(|name| node.intern_atom(name)).collect();
    let ids: Vec<u32> = ids.into_iter().rev().collect();
    for (i, left) in names.iter().enumerate() {
        for (j, right) in names.iter().enumerate() {
            assert_eq!(
                node.cmp_atom_ids(ids[i], ids[j]),
                left.cmp(right),
                "{left:?} vs {right:?}"
            );
        }
    }
    assert_eq!(
        node.cmp_atom_ids(u32::MAX, u32::MAX),
        std::cmp::Ordering::Equal,
        "one atom is equal to itself without a lookup"
    );
}

#[test]
fn reading_an_atom_name_shares_the_table_entry() {
    let node = Node::new(vec!["alpha".into()]);
    let interned = node.intern_atom("beta");

    let first = node.atom_name(interned).expect("interned atom has a name");
    let second = node.atom_name(interned).expect("interned atom has a name");
    assert_eq!(first, "beta");
    assert!(
        std::sync::Arc::ptr_eq(&first.0, &second.0),
        "two reads share one allocation"
    );

    let seeded = node.atom_name(0).expect("seeded atom has a name");
    assert!(std::sync::Arc::ptr_eq(&seeded.0, &node.atom_name(0).unwrap().0));
    assert_eq!(node.atom_name(99), None);
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
extern "C" fn pinned_head_matcher(_process: *mut Process, word: u64, kind: u64, frame: u64, _out: *mut Stored) -> u32 {
    let pinned = AnyValueRef::from_raw_word(crate::ir_runtime::fz_receive_pinned_ref(frame, 1)).expect("pinned ref");
    let msg = Stored { word, kind }.heap_ref();
    u32::from(list_head(msg) == list_head(pinned))
}

/// Park on a one-clause receive whose frame captures `capture` and pins `pinned`.
fn park_on(process: &mut Process, capture: AnyValueRef, pinned: AnyValueRef) {
    let clause = ReceiveClause {
        code: 0x10,
        projector: None,
        root_count: 0,
        argument_count: 0,
        empty_slots: 0,
    };
    let frame = frame_of(&mut process.heap, &[capture, pinned]);
    process.delivery.borrow_mut().install_park(ParkRecord {
        site: leaked_site(pinned_head_matcher, None, 1, &[clause]),
        frame,
        after_deadline_ms: None,
        after_timer_id: None,
    });
}

/// The list a receive frame captures behind its outer continuation.
fn frame_capture(frame: AnyValueRef) -> AnyValueRef {
    match unsafe { closure_capture_value(frame.closure_addr().expect("frame addr"), 1) } {
        AnyValue::HeapRef(list) => list,
        other => panic!("a captured list stays a heap ref: {other:?}"),
    }
}

/// A collection moves everything the process holds into its heap: the
/// runnable closure, the parked receive's frame with its capture and
/// pinned value and the caller's transient values; the mailbox is no root. Each is
/// forwarded and still reads as it did, so the parked receive still matches.
#[test]
fn collect_forwards_every_root_a_parked_process_holds() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let pinned = int_list(&mut process.heap, 1);
    let body_capture = int_list(&mut process.heap, 2);
    let runnable_capture = int_list(&mut process.heap, 4);
    let mailbox_message = int_list(&mut process.heap, 5);
    let mut transient = [int_list(&mut process.heap, 6)];
    let runnable = closure_capturing(&mut process, runnable_capture);
    park_on(&mut process, body_capture, pinned);
    let frame = process.delivery.borrow().park().expect("parked").frame;
    process.set_runnable_closure(runnable);
    let (segment, mailbox_message) = crate::sched::gift_copy_one(&mut process.heap, Stored::of_ref(mailbox_message));
    process.mailbox.push(mailbox_message, segment);
    let before = (
        pinned.list_addr().unwrap(),
        frame,
        runnable,
        mailbox_message.heap_ref().list_addr().unwrap(),
        transient[0].list_addr().unwrap(),
    );

    let stats = process.collect_stats(&mut transient);

    let delivery = process.delivery.borrow_mut();
    let park = delivery.park().expect("still parked");
    assert_ne!(park.frame, before.1, "frame moved");
    assert_ne!(process.runnable_closure(), Some(before.2), "runnable closure moved");
    assert_eq!(
        process.mailbox.front().unwrap().heap_ref().list_addr().unwrap(),
        before.3,
        "a message waiting in the mailbox is no root and stays where it is"
    );
    assert_ne!(transient[0].list_addr().unwrap(), before.4, "transient value moved");
    assert_ne!(
        frame_capture(park.frame).list_addr().unwrap(),
        before.0,
        "pinned and captured lists moved"
    );
    assert_eq!(list_head(frame_capture(park.frame)), 2);
    assert_eq!(
        list_head(captured_list(process.runnable_closure().expect("runnable"))),
        4
    );
    assert_eq!(list_head(process.mailbox.front().unwrap().heap_ref()), 5);
    assert_eq!(list_head(transient[0]), 6);
    let probe = int_list(&mut process.heap, 1);
    assert!(
        park.try_match(null_mut(), Stored::of_ref(probe), &mut crate::park::Roots::new())
            .is_some(),
        "the moved pinned value still matches"
    );
    assert_eq!(
        stats.copied_objects, 6,
        "each of the three roots moved with what it holds, and the mailbox's message was not copied"
    );
}

#[test]
fn handlers_pop_innermost_first() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let capture = int_list(&mut process.heap, 1);
    let template = closure_capturing(&mut process, capture);
    let outer = push_template(&mut process.handlers, template.closure_addr().unwrap());
    process.push_interpreter_handler();

    assert_eq!(process.handlers.depth(), 2);
    assert_eq!(process.handlers.innermost(), Some(Innermost::Interpreter));
    process.pop_handler();
    assert_eq!(process.handlers.innermost(), Some(Innermost::Compiled(outer)));
    process.pop_handler();
    assert_eq!(process.handlers.innermost(), None);
}

#[test]
#[should_panic(expected = "a try body completes under the handler it pushed")]
fn popping_without_a_handler_is_a_compiler_defect() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    process.pop_handler();
}

/// What a compiled handler captures is a root: a collection while a `try`
/// body runs moves the values its record holds and writes them back into the
/// record, and the interpreter's record holds nothing to move. The record
/// itself lives on the handler stack, so nothing else moves.
#[test]
fn collect_forwards_what_every_compiled_handler_captures() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let capture = int_list(&mut process.heap, 11);
    let template = closure_capturing(&mut process, capture);
    let image = push_template(&mut process.handlers, template.closure_addr().unwrap());
    process.push_interpreter_handler();

    let stats = process.collect_stats(&mut []);

    assert_eq!(process.handlers.depth(), 2, "both records keep their places");
    let moved = AnyValueRef::from_heap_object(ValueKind::CLOSURE, image).unwrap();
    assert_ne!(captured_list(moved), capture, "the captured list moved");
    assert_eq!(list_head(captured_list(moved)), 11);
    assert_eq!(
        stats.copied_objects, 1,
        "the captured list is everything the collection moves"
    );
}

/// A receive with no `after` has a null after body and a running process has
/// no park record: neither contributes a root.
#[test]
fn collect_roots_only_what_the_process_holds() {
    let mut process = Process::new(Rc::new(RefCell::new(SchemaRegistry::new())));
    let capture = int_list(&mut process.heap, 7);
    let runnable = closure_capturing(&mut process, capture);
    process.set_runnable_closure(runnable);

    let running = process.collect_stats(&mut []);
    assert_eq!(
        running.copied_objects, 2,
        "the runnable closure and its capture are everything the collection moves"
    );
    assert_eq!(
        list_head(captured_list(process.runnable_closure().expect("runnable"))),
        7
    );

    let pinned = int_list(&mut process.heap, 8);
    let body_capture = int_list(&mut process.heap, 9);
    park_on(&mut process, body_capture, pinned);
    let parked = process.collect_stats(&mut []);
    assert_eq!(
        parked.copied_objects, 3,
        "the frame, its capture and its pinned value move; the runnable closure is already kept"
    );
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

/// A closure standing in for a scheduler continuation or a handler.
fn a_closure(process: &mut Process) -> AnyValueRef {
    let capture = int_list(&mut process.heap, 1);
    closure_capturing(process, capture)
}

fn a_process() -> Process {
    Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))
}

/// Runs one quantum whose code does `unwind` each time it is entered, and
/// returns the closures it was entered with.
fn entries_of_a_quantum(process: &mut Process, mut unwind: impl FnMut(&mut Process, usize)) -> Vec<AnyValueRef> {
    let first = a_closure(process);
    let mut entered = Vec::new();
    process.run_quantum(first, |process, closure| {
        unwind(process, entered.len());
        entered.push(closure);
    });
    assert_eq!(entered[0], first);
    entered
}

#[test]
fn a_delivered_handler_continues_the_quantum_without_the_scheduler() {
    let mut process = a_process();
    let handler = a_closure(&mut process);
    process.reductions_remaining = 17;

    let entered = entries_of_a_quantum(&mut process, |process, entry| {
        if entry == 0 {
            process.deliver_handler(handler);
        }
    });

    assert_eq!(entered.len(), 2, "the handler ran in the same quantum");
    assert_eq!(entered[1], handler);
    assert!(!process.has_delivered_handler(), "the handler was taken");
    assert!(process.runnable.is_none(), "nothing was queued for the scheduler");
    assert_eq!(process.reductions_remaining, 17, "the budget is not reset");
}

#[test]
fn a_handler_that_yields_hands_the_process_back_to_the_scheduler() {
    let mut process = a_process();
    let handler = a_closure(&mut process);
    let continuation = a_closure(&mut process);

    let entered = entries_of_a_quantum(&mut process, |process, entry| match entry {
        0 => process.deliver_handler(handler),
        _ => {
            process.set_runnable_closure(continuation);
            process.finish_yield_report(0, YIELD_REASON_REDUCTIONS);
        }
    });

    assert_eq!(entered.len(), 2);
    assert_eq!(process.runnable_closure(), Some(continuation));
}

#[test]
fn a_reduction_yield_hands_the_process_back_to_the_scheduler() {
    let mut process = a_process();
    let continuation = a_closure(&mut process);

    let entered = entries_of_a_quantum(&mut process, |process, _| {
        process.set_runnable_closure(continuation);
        process.finish_yield_report(0, YIELD_REASON_REDUCTIONS);
    });

    assert_eq!(entered.len(), 1);
    assert_eq!(process.runnable_closure(), Some(continuation));
    assert_eq!(process.reduction_yields, 1);
}

#[test]
fn an_explicit_yield_hands_the_process_back_to_the_scheduler() {
    let mut process = a_process();
    let continuation = a_closure(&mut process);

    let entered = entries_of_a_quantum(&mut process, |process, _| {
        process.set_runnable_closure(continuation);
        process.finish_yield_report(10, YIELD_REASON_EXPLICIT);
    });

    assert_eq!(entered.len(), 1);
    assert_eq!(process.runnable_closure(), Some(continuation));
}

#[test]
fn a_park_hands_the_process_back_to_the_scheduler() {
    let mut process = a_process();

    let entered = entries_of_a_quantum(&mut process, |process, _| process.state = ProcessState::Blocked);

    assert_eq!(entered.len(), 1);
    assert!(process.runnable.is_none());
    assert_eq!(process.state, ProcessState::Blocked);
}

#[test]
fn a_failure_hands_the_process_back_to_the_scheduler() {
    let mut process = a_process();

    let entered = entries_of_a_quantum(&mut process, |process, _| process.failed = true);

    assert_eq!(entered.len(), 1);
    assert!(process.failed);
}

#[test]
fn collect_forwards_a_delivered_handler() {
    let mut process = a_process();
    let capture = int_list(&mut process.heap, 21);
    let handler = closure_capturing(&mut process, capture);
    process.deliver_handler(handler);

    let stats = process.collect_stats(&mut []);

    let moved = process.delivered.expect("the handler stays delivered").as_ref();
    assert_ne!(moved, handler);
    assert_eq!(list_head(captured_list(moved)), 21);
    assert_eq!(
        stats.copied_objects, 2,
        "the delivered handler and its capture are everything the collection moves"
    );
}

/// A thin callable is one object: asking the node for the same code under the
/// same header twice returns the same word, and a different code word is a
/// different object.
#[test]
fn a_node_keeps_one_static_closure_per_header_and_code_word() {
    let node = Node::empty();
    let denotation = ClosureDenotationId::user(0);

    let first = node.static_closure(denotation, 1, 7);
    assert_eq!(first.raw_word(), node.static_closure(denotation, 1, 7).raw_word());
    assert_ne!(first.raw_word(), node.static_closure(denotation, 1, 8).raw_word());
    assert_ne!(first.raw_word(), node.static_closure(denotation, 2, 7).raw_word());
}

/// The static closure reads exactly as a heap closure with no captures does:
/// kind, arity, zero captures, its code word, 16-aligned, and a literal ref
/// so the collector and deep copy treat it as read-only program data.
#[test]
fn a_static_closure_reads_as_a_literal_closure_with_no_captures() {
    let node = Node::empty();
    let word = node.static_closure(ClosureDenotationId::user(0), 3, 42);

    assert!(word.is_literal());
    assert_eq!(word.tag(), ValueKind::CLOSURE);
    let addr = word.storage_addr();
    assert_eq!(addr as usize % 16, 0);
    unsafe {
        assert_eq!(crate::any_value::closure_arity(addr), 3);
        assert_eq!(crate::any_value::closure_captured_count(addr), 0);
        assert_eq!(crate::any_value::closure_fn_ptr(addr), 42);
    }
}

/// A static bitstring reads exactly as a heap bitstring does, and is one
/// 16-aligned literal object per distinct value: the same bytes at another bit
/// length are another value.
#[test]
fn a_node_keeps_one_static_bitstring_per_value_and_it_reads_as_a_literal_bitstring() {
    let node = Node::empty();

    let word = node.static_bitstring(b"hello", 40);

    assert!(word.is_literal());
    assert_eq!(word.tag(), ValueKind::BITSTRING);
    assert_eq!(word.storage_addr() as usize % 16, 0);
    let addr = word.storage_addr();
    unsafe {
        assert_eq!(crate::any_value::bitstring_bit_len(addr), 40);
        let bytes = std::slice::from_raw_parts(crate::any_value::bitstring_bytes_ptr(addr), 6);
        assert_eq!(bytes, b"hello\0", "the bytes, then the NUL a C string reader stops at");
    }
    assert_eq!(word.raw_word(), node.static_bitstring(b"hello", 40).raw_word());
    assert_ne!(word.raw_word(), node.static_bitstring(b"hello", 39).raw_word());
    assert_ne!(word.raw_word(), node.static_bitstring(b"world", 40).raw_word());
}

/// A collection leaves a literal closure where it is, and a deep copy shares
/// it instead of copying: every holder sees the one object.
#[test]
fn a_collection_leaves_a_static_closure_in_place_and_a_deep_copy_shares_it() {
    let node = Rc::new(Node::empty());
    let word = node.static_closure(ClosureDenotationId::user(0), 0, 9);
    let mut process = Process::with_node(Rc::clone(&node), Rc::new(RefCell::new(SchemaRegistry::new())), 1, 1000);

    let mut roots = [word];
    process.heap.collect_stats(&mut roots);
    assert_eq!(roots[0].raw_word(), word.raw_word(), "a collection does not move it");

    let mut receiver = Process::with_node(node, Rc::new(RefCell::new(SchemaRegistry::new())), 2, 1000);
    let view = process.heap.view();
    let copied = crate::heap::deep_copy_any_value_ref(word, &view, &mut receiver.heap);
    assert_eq!(copied.raw_word(), word.raw_word(), "a send shares it");
}

/// Intent: atoms order by name, byte for byte, whether the first eight bytes
/// settle it or the names agree that far.
#[test]
fn atoms_order_by_name_within_and_beyond_their_first_eight_bytes() {
    let node = Node::empty();
    let names = [
        "",
        "a",
        "ab",
        "b",
        "eight888",
        "eight888a",
        "eight888b",
        "eight889",
        "é",
        "zebra",
    ];
    let ids: Vec<u32> = names.iter().rev().map(|name| node.intern_atom(name)).collect();
    let ids: Vec<u32> = ids.into_iter().rev().collect();
    for (i, left) in names.iter().enumerate() {
        for (j, right) in names.iter().enumerate() {
            assert_eq!(
                node.cmp_atom_names(ids[i], ids[j]),
                left.cmp(right),
                "{left} vs {right}"
            );
        }
    }
}

impl Process {
    /// Collect and keep what the collection measured, releasing its from-space.
    pub(crate) fn collect_stats(&mut self, transient: &mut (impl Roots + ?Sized)) -> GcStats {
        let collected = self.collect(transient);
        *collected.stats()
    }
}
