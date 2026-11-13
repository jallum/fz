use super::*;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

thread_local! {
    static ALLOCATIONS: Cell<u64> = const { Cell::new(0) };
}

/// Counts the allocation calls made by the thread that asks, so a test can
/// say that a stretch of work allocated nothing.
struct CountingAllocator;

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.with(|count| count.set(count.get() + 1));
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOCATIONS.with(|count| count.set(count.get() + 1));
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn allocations_during(work: impl FnOnce()) -> u64 {
    let before = ALLOCATIONS.with(Cell::get);
    work();
    ALLOCATIONS.with(Cell::get) - before
}

fn id(n: u32) -> ValueId {
    ValueId::from_u32(n)
}

fn set_of(count: usize, numbers: &[u32]) -> ValueSet {
    let mut set = ValueSet::for_values(count);
    set.extend(numbers.iter().map(|n| id(*n)));
    set
}

fn numbers(set: &ValueSet) -> Vec<u32> {
    set.iter().map(|value| value.as_u32()).collect()
}

/// The set is one bit per value inside a three-word handle: the words are one
/// contiguous run, inline for the common body size and on the heap beyond it.
#[test]
fn a_set_is_a_small_handle_over_one_run_of_words() {
    assert_eq!(std::mem::size_of::<ValueSet>(), 24);
}

/// A walk over a body of ordinary size makes, marks, tests and unmarks its
/// visiting set without asking the allocator for anything.
#[test]
fn a_set_over_an_ordinary_body_allocates_nothing() {
    let allocations = allocations_during(|| {
        let mut visiting = ValueSet::for_values(128);
        for number in 0..128 {
            assert!(visiting.mark(id(number)));
        }
        assert!(visiting.contains(id(100)));
        assert!(visiting.unmark(id(100)));
        assert_eq!(visiting.iter().count(), 127);
    });
    assert_eq!(allocations, 0);
}

/// A body larger than the inline words gets its one allocation up front and
/// never grows: marking every value afterwards allocates nothing.
#[test]
fn a_set_over_a_large_body_allocates_once() {
    let mut set = ValueSet::for_values(480);
    let allocations = allocations_during(|| {
        for number in 0..480 {
            set.mark(id(number));
        }
    });
    assert_eq!(allocations, 0);
    assert_eq!(set.iter().count(), 480);
}

/// Marks across the inline and heap sizes iterate in number order, and a
/// value past the end of the set is simply not a member.
#[test]
fn a_set_keeps_every_mark_and_iterates_in_number_order() {
    let mut set = set_of(480, &[479, 3, 128, 127]);
    assert_eq!(numbers(&set), vec![3, 127, 128, 479]);
    assert!(!set.contains(id(480)));
    assert!(!set.contains(id(100_000)));
    assert!(set.unmark(id(479)));
    assert!(!set.unmark(id(479)));
    assert!(!set.unmark(id(100_000)));
    assert_eq!(numbers(&set), vec![3, 127, 128]);
}

/// A set marks a value once and reports whether the mark was new.
#[test]
fn a_set_reports_whether_a_mark_is_new() {
    let mut set = ValueSet::for_values(8);
    assert!(set.mark(id(7)));
    assert!(!set.mark(id(7)));
    assert!(set.contains(id(7)));
    assert!(set.unmark(id(7)));
    assert!(!set.unmark(id(7)));
    assert_eq!(set.iter().count(), 0);
}

/// A value the set was not made for is a bug in the caller, and says so.
#[test]
#[should_panic(expected = "within the count its set was made for")]
fn marking_past_the_count_is_loud() {
    ValueSet::for_values(64).mark(id(64));
}

/// Subtracting unmarks what the other set marks, whichever set is longer.
#[test]
fn subtracting_unmarks_the_other_sets_values() {
    let small = set_of(128, &[1, 5, 70]);
    let large = set_of(301, &[5, 70, 71, 300]);

    let mut large_minus_small = large.clone();
    large_minus_small.subtract(&small);
    assert_eq!(numbers(&large_minus_small), vec![71, 300]);

    let mut small_minus_large = small.clone();
    small_minus_large.subtract(&large);
    assert_eq!(numbers(&small_minus_large), vec![1]);
}
