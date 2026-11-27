use super::*;
use crate::any_value::AnyValue;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, ValueKind, closure_capture_raw_kind, closure_capture_set_raw_kind,
    closure_header_word, closure_header_write, closure_size_for_count,
};
use crate::heap::{Generation, Heap, SIZE_TABLE};
use crate::process::Process;

/// Push a compiled record the way compiled code does: a closure image of
/// `captures`, then the trailer naming the record's size.
fn push_compiled(stack: &mut HandlerStack, code: u64, captures: &[(u64, ValueKind)]) -> *mut u8 {
    let image_bytes = closure_size_for_count(captures.len());
    let image = stack.reserve(image_bytes + WORD);
    // SAFETY: `reserve` handed back `image_bytes + WORD` bytes for this record alone.
    unsafe {
        closure_header_write(
            image,
            closure_header_word(ClosureDenotationId::INTERNAL, captures.len() as u16, 0, 3),
        );
        (image.add(8) as *mut u64).write(code);
        for (idx, (raw, kind)) in captures.iter().enumerate() {
            closure_capture_set_raw_kind(image, idx, *raw, *kind);
        }
        (image.add(image_bytes) as *mut u64).write((image_bytes + WORD) as u64);
    }
    image
}

fn code_of(record: Innermost) -> u64 {
    match record {
        // SAFETY: a compiled record is a closure image whose second word is its code.
        Innermost::Compiled(image) => unsafe { (image.add(8) as *const u64).read() },
        Innermost::Interpreter => panic!("expected a compiled record"),
    }
}

#[test]
fn a_raise_reaches_the_innermost_handler_whichever_kind_pushed_it() {
    let mut stack = HandlerStack::default();
    assert_eq!(stack.innermost(), None, "a process outside every try has no handler");

    push_compiled(&mut stack, 0x100, &[(7, ValueKind::INT)]);
    stack.push_interpreter();
    push_compiled(&mut stack, 0x300, &[(1, ValueKind::INT), (2, ValueKind::INT)]);
    assert_eq!(stack.depth(), 3);

    assert_eq!(code_of(stack.innermost().unwrap()), 0x300);
    stack.pop();
    assert_eq!(stack.innermost(), Some(Innermost::Interpreter));
    stack.pop();
    assert_eq!(code_of(stack.innermost().unwrap()), 0x100);
    stack.pop();
    assert_eq!(stack.innermost(), None);
    assert_eq!(stack.depth(), 0);
}

#[test]
fn growing_the_stack_keeps_every_record_intact() {
    let mut stack = HandlerStack::default();
    for code in 0..500u64 {
        push_compiled(&mut stack, code, &[(code * 10, ValueKind::INT)]);
    }
    assert_eq!(stack.depth(), 500);
    for code in (0..500u64).rev() {
        let Some(Innermost::Compiled(image)) = stack.innermost() else {
            panic!("expected a compiled record");
        };
        assert_eq!(code_of(Innermost::Compiled(image)), code);
        // SAFETY: the record is a closure image with one capture.
        assert_eq!(
            unsafe { closure_capture_raw_kind(image, 0) },
            (code * 10, ValueKind::INT)
        );
        stack.pop();
    }
}

#[test]
fn every_capture_is_handed_to_the_collector_with_its_kind_innermost_first() {
    let mut heap = Heap::new(SIZE_TABLE[0], crate::bits::bits_test::fresh_registry());
    let list = |heap: &mut Heap, n| heap.alloc_list_cons_int(n, AnyValueRef::empty_list()).unwrap();
    let outer = list(&mut heap, 1);
    let inner = list(&mut heap, 2);
    let mut stack = HandlerStack::default();
    push_compiled(&mut stack, 0x1, &[(outer.raw_word(), outer.tag()), (5, ValueKind::INT)]);
    stack.push_interpreter();
    push_compiled(&mut stack, 0x2, &[(inner.raw_word(), inner.tag())]);

    let mut handed = Vec::new();
    stack.for_each_capture(|slot, kind| handed.push((unsafe { *slot }, kind)));
    assert_eq!(
        handed,
        vec![
            (inner.raw_word(), inner.tag()),
            (outer.raw_word(), outer.tag()),
            (5, ValueKind::INT)
        ],
        "innermost first, each with its kind, and the interpreter's record holds none"
    );

    stack.for_each_capture(|slot, _| unsafe { *slot += 16 });
    let mut held = Vec::new();
    stack.for_each_capture(|slot, _| held.push(unsafe { *slot }));
    assert_eq!(held, vec![inner.raw_word() + 16, outer.raw_word() + 16, 21]);
}

/// Push a compiled record copied from the heap closure `template`: the record
/// compiled code writes for a handler whose image is that closure.
pub(crate) fn push_template(stack: &mut HandlerStack, template: *const u8) -> *mut u8 {
    // SAFETY: `template` is a live closure.
    let image_bytes = closure_size_for_count(unsafe { closure_captured_count(template) });
    let image = stack.reserve(image_bytes + WORD);
    // SAFETY: `reserve` handed back `image_bytes + WORD` bytes, and `template` spans `image_bytes`.
    unsafe {
        std::ptr::copy_nonoverlapping(template, image, image_bytes);
        (image.add(image_bytes) as *mut u64).write((image_bytes + WORD) as u64);
    }
    image
}

/// The destination a record's first capture holds now.
fn destination_held(stack: &HandlerStack) -> crate::heap::FieldDestination {
    let Some(Innermost::Compiled(image)) = stack.innermost() else {
        panic!("a compiled record is innermost");
    };
    let (word, kind) = unsafe { closure_capture_raw_kind(image, 0) };
    assert_eq!(kind, ValueKind::DESTINATION);
    crate::heap::FieldDestination::from_word(word)
}

fn heads_from(cell: *mut u8) -> Vec<i64> {
    let mut heads = Vec::new();
    let mut cell = cell as *const crate::any_value::ListCons;
    while !cell.is_null() {
        let cons = unsafe { &*cell };
        let AnyValue::Int(head) = cons.head_value() else {
            panic!("an int head");
        };
        heads.push(head);
        cell = cons.tail_cell_addr() as *const crate::any_value::ListCons;
    }
    heads
}

/// A builder that yields inside a `try` holds its destination in the record's
/// closure image, which only the handler stack's walk reaches. The walk must
/// move the cell and rebase the destination as it does for any closure's
/// captures, and the collection must write its open hole down.
#[test]
fn a_destination_captured_by_a_try_record_follows_its_cell_through_a_minor_and_a_major() {
    let mut process = Process::new(crate::bits::bits_test::fresh_registry());
    let (_, dest) = process.heap.alloc_open_list_cell(AnyValue::int(7));
    push_compiled(&mut process.handlers, 0x1, &[(dest.word(), ValueKind::DESTINATION)]);
    let mut ballast = AnyValueRef::empty_list();
    for n in 0..200 {
        ballast = process.heap.alloc_list_cons_int(n, ballast).unwrap();
    }
    let mut roots = [ballast];

    let minor = {
        drop(process.collect(&mut roots));
        process.gc_stats
    };
    assert_eq!(minor.generation, Generation::Minor);
    assert_eq!(
        minor.open_holes, 1,
        "the record's destination was met and its hole written down"
    );
    let moved = destination_held(&process.handlers);
    assert_ne!(
        moved.cell_addr(),
        dest.cell_addr(),
        "the cell moved and the destination followed"
    );
    assert!(process.heap.destination_is_open(moved));

    drop(process.collect(&mut roots));
    assert_eq!(process.gc_stats.generation, Generation::Major);
    assert_eq!(process.gc_stats.open_holes, 1);
    let rebased = destination_held(&process.handlers);
    assert!(process.heap.destination_is_open(rebased));

    let list = process.heap.alloc_list_cons_int(41, AnyValueRef::empty_list()).unwrap();
    let list = process.heap.alloc_list_cons_int(40, list).unwrap();
    process
        .heap
        .fill_destination(rebased, AnyValue::heap_ptr(list.list_addr().unwrap(), ValueKind::LIST));
    drop(process.collect(&mut roots));
    assert_eq!(process.gc_stats.generation, Generation::Minor);
    assert_eq!(process.gc_stats.open_holes, 0);
    assert_eq!(heads_from(destination_held(&process.handlers).cell_addr()), [7, 40, 41]);
}
