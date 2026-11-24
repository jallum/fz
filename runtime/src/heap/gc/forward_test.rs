//! `Tracer::forward` returns a word unchanged unless it names an object the
//! collection moves.

use super::*;
use crate::any_value::AnyValueRefPacking;
use crate::heap::{Generation, SIZE_TABLE};
use std::cell::RefCell;
use std::rc::Rc;

fn with_tracer(check: impl FnOnce(&mut Tracer)) {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut heap = Heap::new(SIZE_TABLE[0], schemas.clone());
    let from_space = FromSpace::of(&heap, Generation::Major);
    let schemas = schemas.borrow();
    check(&mut Tracer::new(from_space, &mut heap, &schemas, GcStats::default()));
}

#[test]
fn a_word_whose_kind_is_not_a_heap_kind_is_returned_unchanged() {
    with_tracer(|tracer| {
        assert_eq!(tracer.forward(0x1234_5670, ValueKind::INT), 0x1234_5670);
        assert_eq!(tracer.forward(7, ValueKind::ATOM), 7);
    });
}

#[test]
fn the_empty_list_is_returned_unchanged() {
    with_tracer(|tracer| assert_eq!(tracer.forward(0, ValueKind::LIST), 0));
}

#[test]
fn a_literal_object_stays_where_it_is_and_the_collection_copies_nothing() {
    let literal_cell = Box::leak(Box::new([0u64; 2])) as *mut _ as u64 | AnyValueRefPacking::current().literal_bit();
    with_tracer(|tracer| {
        assert_eq!(tracer.forward(literal_cell, ValueKind::LIST), literal_cell);
        assert_eq!(tracer.stats.copied_objects, 0);
        assert!(tracer.worklist.is_empty());
    });
}

#[test]
fn a_slot_whose_kind_is_not_a_heap_kind_is_not_written() {
    with_tracer(|tracer| {
        let mut slot = 0x1234_5670u64;
        unsafe { tracer.forward_slot(&raw mut slot, ValueKind::INT) };
        assert_eq!(slot, 0x1234_5670);
    });
}
