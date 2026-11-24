use super::*;
use crate::heap::arena::{GRANULE, is_young, young_mark_bytes};

fn start() -> Footprint {
    pool_drain_for_test();
    pool_footprint()
}

#[test]
fn a_block_handed_out_adds_its_capacity_to_the_bytes_in_use() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2], Age::Young);
    assert_eq!(pool_footprint().in_use_bytes, before.in_use_bytes + SIZE_TABLE[2]);
    pool_free(p, SIZE_TABLE[2]);
    pool_drain_for_test();
}

#[test]
fn freeing_a_pooled_block_moves_its_bytes_from_in_use_to_idle() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2], Age::Young);
    pool_free(p, SIZE_TABLE[2]);
    let after = pool_footprint();
    assert_eq!(after.in_use_bytes, before.in_use_bytes);
    assert_eq!(after.idle_bytes, before.idle_bytes + SIZE_TABLE[2]);
    pool_drain_for_test();
}

#[test]
fn taking_a_recycled_block_moves_its_bytes_from_idle_back_to_in_use() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2], Age::Young);
    pool_free(p, SIZE_TABLE[2]);
    let p = pool_alloc(SIZE_TABLE[2], Age::Young);
    let held = pool_footprint();
    assert_eq!(held.idle_bytes, before.idle_bytes);
    assert_eq!(held.in_use_bytes, before.in_use_bytes + SIZE_TABLE[2]);
    pool_free(p, SIZE_TABLE[2]);
    pool_drain_for_test();
}

#[test]
fn a_block_above_the_table_counts_while_held_and_leaves_no_idle_bytes_when_freed() {
    let before = start();
    let above_table = round_up_16(SIZE_TABLE[SIZE_TABLE.len() - 1] + 1);
    let big = pool_alloc(above_table, Age::Young);
    assert_eq!(
        pool_footprint().in_use_bytes,
        before.in_use_bytes + above_table,
        "a block off the table is in use like any other"
    );
    pool_free(big, above_table);
    let after = pool_footprint();
    assert_eq!(after.in_use_bytes, before.in_use_bytes);
    assert_eq!(after.idle_bytes, before.idle_bytes, "the system allocator took it back");
}

#[test]
fn a_small_block_is_pooled_at_its_exact_size() {
    let before = start();
    let p = pool_alloc(64, Age::Young);
    assert_eq!(pool_footprint().in_use_bytes, before.in_use_bytes + 64);
    pool_free(p, 64);
    let idle = pool_footprint();
    assert_eq!(idle.in_use_bytes, before.in_use_bytes);
    assert_eq!(
        idle.idle_bytes,
        before.idle_bytes + 64,
        "the freed block rests in the pool"
    );
    let again = pool_alloc(64, Age::Young);
    assert_eq!(again, p, "the same size reuses the freed block");
    assert_eq!(pool_footprint().idle_bytes, before.idle_bytes);
    let other = pool_alloc(80, Age::Young);
    assert_ne!(other, p, "a different size is a different class");
    pool_free(again, 64);
    pool_free(other, 80);
    pool_drain_for_test();
}

#[test]
fn every_pooled_capacity_has_its_own_class_and_names_its_capacity_back() {
    let capacities: Vec<usize> = (16..SIZE_TABLE[0]).step_by(16).chain(SIZE_TABLE).collect();
    for (expected, capacity) in capacities.iter().enumerate() {
        let class = pooled_class(*capacity).expect("pooled");
        assert_eq!(class, expected);
        assert_eq!(class_capacity(class), *capacity);
    }
    assert_eq!(capacities.len(), CLASSES);
    assert_eq!(pooled_class(SIZE_TABLE[0] + 16), None, "between table entries");
}

#[test]
fn the_peak_records_the_highest_in_use_between_two_readings() {
    let before = start();
    let a = pool_alloc(SIZE_TABLE[3], Age::Young);
    let b = pool_alloc(SIZE_TABLE[3], Age::Young);
    pool_free(a, SIZE_TABLE[3]);
    pool_free(b, SIZE_TABLE[3]);
    let after = pool_footprint();
    assert_eq!(after.in_use_bytes, before.in_use_bytes);
    assert!(
        after.peak_in_use_bytes >= before.in_use_bytes + 2 * SIZE_TABLE[3],
        "the two blocks were in use together even though neither is now"
    );
    pool_drain_for_test();
}

#[test]
fn a_binary_buffers_bytes_are_in_use_until_it_is_freed() {
    let before = start();
    binary_buffer_allocated(100);
    let held = pool_footprint();
    assert_eq!(held.in_use_bytes, before.in_use_bytes + 100);
    assert!(held.peak_in_use_bytes >= held.in_use_bytes);
    binary_buffer_freed(100);
    assert_eq!(pool_footprint().in_use_bytes, before.in_use_bytes);
}

#[test]
fn a_buffer_freed_on_another_thread_leaves_the_allocating_threads_bytes_in_use() {
    let before = start();
    binary_buffer_allocated(100);
    std::thread::spawn(|| binary_buffer_freed(100)).join().unwrap();
    assert_eq!(
        pool_footprint().in_use_bytes,
        before.in_use_bytes + 100,
        "a free is counted where it happens"
    );
    binary_buffer_freed(100);
}

#[cfg(debug_assertions)]
#[test]
fn a_block_handed_out_reads_as_unwritten_in_debug_builds() {
    start();
    let p = pool_alloc(SIZE_TABLE[2], Age::Young);
    unsafe { p.write_bytes(0, SIZE_TABLE[2]) };
    pool_free(p, SIZE_TABLE[2]);
    let recycled = pool_alloc(SIZE_TABLE[2], Age::Young);
    let bytes = unsafe { std::slice::from_raw_parts(recycled, SIZE_TABLE[2]) };
    assert!(
        bytes.iter().all(|&b| b == UNWRITTEN_BYTE),
        "recycled block keeps old contents"
    );
    pool_free(recycled, SIZE_TABLE[2]);
    let exact = pool_alloc(SIZE_TABLE[0] - 16, Age::Young);
    let bytes = unsafe { std::slice::from_raw_parts(exact, SIZE_TABLE[0] - 16) };
    assert!(
        bytes.iter().all(|&b| b == UNWRITTEN_BYTE),
        "fresh block is not poisoned"
    );
    pool_free(exact, SIZE_TABLE[0] - 16);
    pool_drain_for_test();
}

fn every_granule_is_young(p: *mut u8, capacity: usize) -> bool {
    (0..span_len(capacity))
        .step_by(GRANULE)
        .all(|offset| is_young(unsafe { p.add(offset) }))
}

fn no_granule_is_young(p: *mut u8, capacity: usize) -> bool {
    (0..span_len(capacity))
        .step_by(GRANULE)
        .all(|offset| !is_young(unsafe { p.add(offset) }))
}

#[test]
fn a_young_block_reads_young_and_an_old_block_never_does() {
    start();
    let capacities = [
        16,
        48,
        1008,
        SIZE_TABLE[2],
        round_up_16(SIZE_TABLE[SIZE_TABLE.len() - 1] + 1),
    ];
    for capacity in capacities {
        let young = pool_alloc(capacity, Age::Young);
        assert!(every_granule_is_young(young, capacity), "a {capacity}-byte young block");
        assert!(is_young(unsafe { young.add(capacity - 1) }), "the block's last byte");
        pool_free(young, capacity);
        if !is_pooled_capacity(capacity) {
            assert!(
                no_granule_is_young(young, capacity),
                "a released {capacity}-byte exact block is cleared, for the span list may cut it up"
            );
        }

        let old = pool_alloc(capacity, Age::Old);
        assert!(no_granule_is_young(old, capacity), "a {capacity}-byte old block");
        pool_free(old, capacity);
    }
    pool_drain_for_test();
}

#[test]
fn a_block_reused_after_a_young_blocks_release_reads_not_young_unless_made_young() {
    start();
    let pooled = SIZE_TABLE[1];
    let exact = round_up_16(SIZE_TABLE[SIZE_TABLE.len() - 1] * 3);
    for capacity in [pooled, exact] {
        let young = pool_alloc(capacity, Age::Young);
        pool_free(young, capacity);
        let old = pool_alloc(capacity, Age::Old);
        if is_pooled_capacity(capacity) {
            assert_eq!(old, young, "the {capacity}-byte block was reused");
        }
        assert!(no_granule_is_young(old, capacity), "made old, it is not young");
        pool_free(old, capacity);

        let again = pool_alloc(capacity, Age::Young);
        assert!(every_granule_is_young(again, capacity), "made young, it is young");
        pool_free(again, capacity);
    }
    pool_drain_for_test();
}

#[test]
fn a_pooled_block_reused_at_the_same_age_writes_no_table_bytes() {
    start();
    let capacity = SIZE_TABLE[2];
    let span = span_len(capacity) / GRANULE;

    let first = pool_alloc(capacity, Age::Young);
    pool_free(first, capacity);
    let before = young_mark_bytes();
    let second = pool_alloc(capacity, Age::Young);
    assert_eq!(second, first, "the freed block came back");
    assert_eq!(
        young_mark_bytes(),
        before,
        "young over its own young mark: nothing to write"
    );
    assert!(every_granule_is_young(second, capacity));
    pool_free(second, capacity);

    let before = young_mark_bytes();
    let old = pool_alloc(capacity, Age::Old);
    assert_eq!(old, first);
    assert_eq!(
        young_mark_bytes() - before,
        span,
        "old over a young leftover clears the span once"
    );
    pool_free(old, capacity);
    let before = young_mark_bytes();
    let old = pool_alloc(capacity, Age::Old);
    assert_eq!(young_mark_bytes(), before, "old over old writes nothing");
    pool_free(old, capacity);
    pool_drain_for_test();
}

#[test]
fn a_pooled_span_is_one_mark_through_every_reuse_and_age() {
    start();
    // Every pooled capacity is a span of its own for good: reused at any age,
    // its table bytes stay equal, which a debug build asserts at every make.
    for class in 0..CLASSES {
        let capacity = class_capacity(class);
        if capacity > SIZE_TABLE[14] {
            continue;
        }
        let ages = [Age::Young, Age::Old, Age::Old, Age::Young, Age::Young, Age::Old];
        let mut first = None;
        for age in ages {
            let p = pool_alloc(capacity, age);
            assert_eq!(
                *first.get_or_insert(p),
                p,
                "a freed block of class {class} is the one reused"
            );
            match age {
                Age::Young => assert!(every_granule_is_young(p, capacity)),
                Age::Old => assert!(no_granule_is_young(p, capacity)),
            }
            pool_free(p, capacity);
        }
    }
    pool_drain_for_test();
}

#[test]
fn a_block_off_the_table_lives_in_the_range_like_any_other() {
    start();
    let above_table = round_up_16(SIZE_TABLE[SIZE_TABLE.len() - 1] * 3);
    let big = pool_alloc(above_table, Age::Young);
    assert!(range().contains(big));
    assert!(is_young(big));
    pool_free(big, above_table);
}

#[test]
fn a_block_released_with_no_pool_to_take_it_is_found_again_and_takes_the_age_it_is_made() {
    let (p, class_capacity) = std::thread::spawn(|| {
        // A class no other test uses, so no pool draws the block off the spill list first.
        let capacity = SIZE_TABLE[16];
        let p = pool_alloc(capacity, Age::Young);
        pool_free(p, capacity);
        // The thread's pool is torn down with the block resting in it.
        (p as usize, capacity)
    })
    .join()
    .unwrap();
    let p = p as *mut u8;
    start();
    let mut taken = Vec::new();
    loop {
        let q = pool_alloc(class_capacity, Age::Old);
        taken.push(q);
        if q == p || taken.len() > 64 {
            break;
        }
    }
    assert!(
        taken.contains(&p),
        "the exited thread's block is on the spill list, and any pool takes it"
    );
    assert!(
        no_granule_is_young(p, class_capacity),
        "made old over the young mark its last life left, it is not young"
    );
    for q in taken {
        pool_free(q, class_capacity);
    }
    pool_drain_for_test();
}

#[test]
fn every_block_a_thread_exits_with_is_handed_over_whole_and_found_again() {
    // A class no other test uses, so no other test's pool draws these off the spill list.
    let capacity = 992;
    let mut made: Vec<usize> = std::thread::spawn(move || {
        let blocks: Vec<*mut u8> = (0..40).map(|_| pool_alloc(capacity, Age::Young)).collect();
        for &p in &blocks {
            pool_free(p, capacity);
        }
        blocks.into_iter().map(|p| p as usize).collect()
    })
    .join()
    .unwrap();
    start();
    let mut taken: Vec<usize> = (0..made.len())
        .map(|_| pool_alloc(capacity, Age::Old) as usize)
        .collect();
    made.sort_unstable();
    taken.sort_unstable();
    assert_eq!(
        taken, made,
        "the exited thread's whole free list comes back, block for block"
    );
    for p in taken {
        pool_free(p as *mut u8, capacity);
    }
    pool_drain_for_test();
}

#[test]
fn the_footprint_counts_logical_capacities_through_a_scripted_sequence() {
    let before = start();
    let small = 80;
    let table = SIZE_TABLE[2];
    let exact = round_up_16(SIZE_TABLE[SIZE_TABLE.len() - 1] + 100);
    let outstanding = pool_outstanding_blocks();

    let a = pool_alloc(small, Age::Young);
    let b = pool_alloc(table, Age::Young);
    let c = pool_alloc(exact, Age::Old);
    let held = pool_footprint();
    assert_eq!(held.in_use_bytes, before.in_use_bytes + small + table + exact);
    assert_eq!(held.idle_bytes, before.idle_bytes);
    assert_eq!(
        pool_outstanding_blocks(),
        outstanding + 2,
        "an exact block is not outstanding"
    );

    pool_free(c, exact);
    pool_free(a, small);
    let after = pool_footprint();
    assert_eq!(after.in_use_bytes, before.in_use_bytes + table);
    assert_eq!(
        after.idle_bytes,
        before.idle_bytes + small,
        "an exact block leaves no idle bytes"
    );
    assert_eq!(after.peak_in_use_bytes, held.in_use_bytes.max(before.peak_in_use_bytes));
    assert_eq!(pool_outstanding_blocks(), outstanding + 1);

    let a = pool_alloc(small, Age::Young);
    assert_eq!(
        pool_footprint().idle_bytes,
        before.idle_bytes,
        "the small block was recycled"
    );
    pool_free(a, small);
    pool_free(b, table);
    assert_eq!(pool_outstanding_blocks(), outstanding);
    pool_drain_for_test();
}

/// A capacity of a trimmed class, and a small one whose allocations drive the
/// epochs without being trimmed themselves.
const TRIMMED: usize = SIZE_TABLE[10];
const DRIVER: usize = SIZE_TABLE[0];

/// Allocations and frees of the driver capacity until `epochs` epochs of at
/// least `EPOCH_FLOOR` bytes have passed.
fn pass_epochs(epochs: usize) {
    for _ in 0..epochs * (EPOCH_FLOOR / DRIVER + 2) {
        let p = pool_alloc(DRIVER, Age::Old);
        pool_free(p, DRIVER);
    }
}

fn cold_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().cold.iter().sum())
}

/// The whole pages inside the block, which are the ones a trim gives back.
fn inner_pages(p: *mut u8, capacity: usize) -> &'static [u8] {
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let start = (p as usize).next_multiple_of(page);
    let end = (p as usize + capacity) & !(page - 1);
    assert!(end > start, "a trimmed block holds a whole page");
    unsafe { std::slice::from_raw_parts(start as *const u8, end - start) }
}

fn is_zeroed(p: *mut u8, capacity: usize) -> bool {
    inner_pages(p, capacity).iter().all(|&b| b == 0)
}

#[test]
fn an_idle_block_nobody_wanted_for_a_whole_epoch_gives_its_pages_back_and_is_still_handed_out() {
    start();
    const { assert!(TRIMMED >= TRIM_FROM_CAPACITY) };
    let blocks: Vec<*mut u8> = (0..4).map(|_| pool_alloc(TRIMMED, Age::Old)).collect();
    for &p in &blocks {
        unsafe { p.write_bytes(0xAB, TRIMMED) };
    }
    for &p in &blocks {
        pool_free(p, TRIMMED);
    }
    let cold_before = cold_blocks();

    pass_epochs(1);
    assert_eq!(
        cold_blocks(),
        cold_before,
        "an epoch that began with them idle has not yet shown them unwanted"
    );
    pass_epochs(1);
    assert_eq!(
        cold_blocks(),
        cold_before + 4,
        "unwanted for the whole of an epoch, all four are cold"
    );
    for &p in &blocks {
        assert!(
            is_zeroed(p, TRIMMED),
            "a cold block's pages went back and read as zeros"
        );
    }
    assert_eq!(
        pool_footprint().idle_bytes,
        start_idle() + 4 * TRIMMED,
        "cold blocks are still idle blocks of the pool"
    );

    let again = pool_alloc(TRIMMED, Age::Young);
    assert!(blocks.contains(&again), "a cold block is handed out like any other");
    unsafe { again.write_bytes(0xCD, TRIMMED) };
    assert_eq!(cold_blocks(), cold_before + 3, "and is no longer cold");
    pool_free(again, TRIMMED);
    pool_drain_for_test();
}

fn start_idle() -> usize {
    pool_footprint().idle_bytes - BLOCK_POOL.with(|pool| pool.borrow().free_lists[SMALL_CLASSES + 10].len()) * TRIMMED
}

#[test]
fn a_block_wanted_every_epoch_stays_warm_and_only_the_spare_beneath_it_goes_cold() {
    start();
    let blocks: Vec<*mut u8> = (0..2).map(|_| pool_alloc(TRIMMED, Age::Old)).collect();
    for &p in &blocks {
        unsafe { p.write_bytes(0xAB, TRIMMED) };
        pool_free(p, TRIMMED);
    }
    let hot = blocks[1];
    for _ in 0..3 {
        let p = pool_alloc(TRIMMED, Age::Old);
        assert_eq!(p, hot, "the most recently freed block is the one wanted");
        pool_free(p, TRIMMED);
        pass_epochs(1);
    }
    assert!(!is_zeroed(hot, TRIMMED), "the block in use every epoch keeps its pages");
    assert!(is_zeroed(blocks[0], TRIMMED), "the spare beneath it went cold");
    assert_eq!(cold_blocks(), 1);
    pool_drain_for_test();
}

#[test]
fn a_small_idle_block_is_never_trimmed() {
    start();
    let capacity = SIZE_TABLE[2];
    assert!(capacity < TRIM_FROM_CAPACITY);
    let p = pool_alloc(capacity, Age::Old);
    unsafe { p.write_bytes(0xAB, capacity) };
    pool_free(p, capacity);
    pass_epochs(3);
    assert_eq!(cold_blocks(), 0);
    assert!(
        unsafe { std::slice::from_raw_parts(p, capacity) }
            .iter()
            .all(|&b| b == 0xAB)
    );
    pool_drain_for_test();
}
