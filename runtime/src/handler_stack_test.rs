use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, ValueKind, closure_capture_raw_kind, closure_capture_set_raw_kind,
    closure_header_word, closure_header_write, closure_size_for_count,
};
use crate::heap::{Heap, SIZE_TABLE};

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
fn only_heap_captures_are_handed_to_the_collector_and_hold_what_it_leaves_in_order() {
    let mut heap = Heap::new(SIZE_TABLE[0], crate::bits::bits_test::fresh_registry());
    let list = |heap: &mut Heap, n| heap.alloc_list_cons_int(n, AnyValueRef::empty_list()).unwrap();
    let outer = list(&mut heap, 1);
    let inner = list(&mut heap, 2);
    let mut stack = HandlerStack::default();
    push_compiled(&mut stack, 0x1, &[(outer.raw_word(), outer.tag()), (5, ValueKind::INT)]);
    stack.push_interpreter();
    push_compiled(&mut stack, 0x2, &[(inner.raw_word(), inner.tag())]);

    let mut handed = Vec::new();
    stack.forward_captures(|capture| handed.push(*capture));
    assert_eq!(
        handed,
        vec![inner, outer],
        "innermost first, and the raw int is no root"
    );

    let moved_inner = list(&mut heap, 20);
    let moved_outer = list(&mut heap, 10);
    let mut leaves = [moved_inner, moved_outer].into_iter();
    stack.forward_captures(|capture| *capture = leaves.next().unwrap());
    let mut held = Vec::new();
    stack.forward_captures(|capture| held.push(*capture));
    assert_eq!(held, vec![moved_inner, moved_outer]);
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
