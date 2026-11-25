//! What a collection takes as from-space is read off the age table, and it
//! agrees with the blocks the heap holds young.

use super::*;
use crate::any_value::AnyValueRef;
use crate::any_value::{AnyValue, EMPTY_LIST, heap_kind_from_tagged};
use crate::heap::ref_io::ptr_in_ranges;
use crate::heap::{GiftSegment, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;

fn registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

fn list_of(heap: &mut Heap, len: i64) -> u64 {
    (0..len).fold(EMPTY_LIST, |tail, head| {
        heap.alloc_list_cons_slot(AnyValue::int(head), tail)
    })
}

fn root_of(bits: u64) -> AnyValueRef {
    let kind = heap_kind_from_tagged(bits).expect("tagged heap root");
    AnyValueRef::from_raw_word(bits)
        .inspect(|root| assert_eq!(root.tag(), kind))
        .expect("heap root ref")
}

fn gift(sender: &mut Heap, len: i64) -> GiftSegment {
    let source = list_of(sender, len);
    crate::sched::gift_copy(sender, &[root_of(source)]).0
}

/// A heap holding old blocks, many grafted young blocks, a climbed tip and a
/// huge object's block.
fn heap_with_old_and_many_young_blocks() -> Heap {
    let reg = registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut heap = Heap::new(SIZE_TABLE[0], reg);
    let kept = list_of(&mut heap, 600);
    let mut roots = [root_of(kept)];
    heap.collect_stats(&mut roots);
    for len in 1..=40 {
        heap.graft(gift(&mut sender, len));
    }
    list_of(&mut heap, 3000);
    heap.alloc_list_cons_slot(AnyValue::int(0), EMPTY_LIST);
    heap
}

#[test]
fn the_age_table_calls_young_exactly_the_addresses_the_young_blocks_cover() {
    let heap = heap_with_old_and_many_young_blocks();
    let young: Vec<_> = heap.young_ranges().collect();
    assert!(young.len() > 40, "the grafts and the climbed tip are separate blocks");
    let mut slots = 0;
    for (start, end) in heap.block_ranges() {
        let mut p = start;
        while p < end {
            assert_eq!(
                range().is_young(p),
                ptr_in_ranges(p, young.iter().copied()),
                "{p:p} is young by the table and by the ranges alike"
            );
            p = unsafe { p.add(16) };
            slots += 1;
        }
    }
    assert!(slots > 0);
}

#[test]
fn a_minor_collection_leaves_every_old_address_and_a_major_one_moves_it() {
    let heap = heap_with_old_and_many_young_blocks();
    let minor = FromSpace::of(Generation::Minor);
    let major = FromSpace::of(Generation::Major);
    let mut old_slots = 0;
    for block in &heap.old_blocks {
        let mut p = block.start;
        while p < block.end() {
            assert!(
                !minor.moves(&heap, p, false),
                "{p:p} is old: a minor collection leaves it"
            );
            assert!(
                major.moves(&heap, p, false),
                "{p:p}: a major collection takes every block"
            );
            p = unsafe { p.add(16) };
            old_slots += 1;
        }
    }
    assert!(old_slots > 0);
}

#[test]
fn a_literal_moves_in_no_collection() {
    let heap = heap_with_old_and_many_young_blocks();
    let literal = Box::new([0u64; 2]);
    let p = literal.as_ptr() as *mut u8;
    assert!(!FromSpace::of(Generation::Minor).moves(&heap, p, true));
    assert!(!FromSpace::of(Generation::Major).moves(&heap, p, true));
}
