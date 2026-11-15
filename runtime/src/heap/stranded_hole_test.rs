//! A continuation frame that resumes under a newer object cannot be popped.
//! Compiled code records its bytes as the heap's single hole, and the next
//! runtime allocation that fits places its object there instead of at the tip.
//! These tests write the hole the way compiled code does and observe where
//! `Heap::alloc` puts what it allocates.

use super::*;
use crate::any_value::{AnyValue, AnyValueRef, EMPTY_LIST, list_addr_from_tagged};
use std::cell::RefCell;
use std::rc::Rc;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

/// A heap whose tip holds a stranded frame of `frame` bytes under one newer
/// 16-byte object, and that frame's address.
fn heap_with_stranded_frame(frame: usize) -> (Heap, *mut u8) {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let start = heap.alloc(frame);
    heap.alloc(16);
    heap.hole = Hole { start, size: frame };
    (heap, start)
}

#[test]
fn an_allocation_that_fits_the_hole_is_placed_in_it_and_the_hole_shrinks_by_what_it_took() {
    let (mut heap, start) = heap_with_stranded_frame(64);
    let tip = heap.bump_top;

    let first = heap.alloc(32);
    let second = heap.alloc(16);
    let third = heap.alloc(16);
    let fourth = heap.alloc(16);

    assert_eq!(first, start, "the first object takes the hole's first bytes");
    assert_eq!(second, unsafe { start.add(32) }, "the hole's remainder serves the next");
    assert_eq!(third, unsafe { start.add(48) }, "down to its last slot");
    assert_eq!(fourth, tip, "an exhausted hole leaves allocation at the tip");
    assert_eq!(heap.hole.size, 0);
}

#[test]
fn an_allocation_that_does_not_fit_the_hole_goes_to_the_tip_and_leaves_the_hole_whole() {
    let (mut heap, start) = heap_with_stranded_frame(64);
    let tip = heap.bump_top;

    assert_eq!(heap.alloc(80), tip, "80 bytes do not fit a 64-byte hole");
    assert_eq!(heap.alloc(64), start, "the hole still serves what fits it");
}

#[test]
fn a_hole_in_the_old_generation_is_refused_and_forgotten() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let kept = heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST);
    let mut roots = [AnyValueRef::from_raw_word(kept).expect("list root")];
    heap.collect(&mut roots);
    let old = roots[0].heap_object_word().expect("forwarded list");
    let old_address = list_addr_from_tagged(old).expect("list address");
    assert!(
        !ref_io::ptr_in_ranges(old_address, heap.young_ranges()),
        "the survivor lives in an old block"
    );
    heap.hole = Hole {
        start: old_address,
        size: 32,
    };
    let tip = heap.bump_top;

    assert_eq!(
        heap.alloc(16),
        tip,
        "a stranded frame an earlier collection kept is not reused"
    );
    assert_eq!(
        heap.hole.size, 0,
        "an old hole can never become young, so it is dropped"
    );
}

#[test]
fn a_hole_is_not_taken_while_a_gift_window_is_open_and_serves_again_after_it_closes() {
    let (mut heap, start) = heap_with_stranded_frame(64);

    heap.begin_gift(32);
    let in_gift = heap.alloc(32);
    assert_eq!(
        in_gift, heap.block_start,
        "a gift's copy lands in its own block, measured exactly"
    );
    let segment = heap.end_gift();
    assert_eq!(segment.fill_bytes(), 32);

    assert_eq!(heap.alloc(64), start, "the hole survives the window");
}

#[test]
fn a_collection_forgets_the_hole() {
    let (mut heap, _) = heap_with_stranded_frame(64);

    heap.collect(&mut []);

    assert_eq!(heap.hole.size, 0, "the hole's block was released");
    let tip = heap.bump_top;
    assert_eq!(heap.alloc(16), tip);
}
