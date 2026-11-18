use super::*;

fn start() -> Footprint {
    pool_drain_for_test();
    pool_footprint()
}

#[test]
fn a_block_handed_out_adds_its_capacity_to_the_bytes_in_use() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2]);
    assert_eq!(pool_footprint().in_use_bytes, before.in_use_bytes + SIZE_TABLE[2]);
    pool_free(p, SIZE_TABLE[2]);
    pool_drain_for_test();
}

#[test]
fn freeing_a_pooled_block_moves_its_bytes_from_in_use_to_idle() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2]);
    pool_free(p, SIZE_TABLE[2]);
    let after = pool_footprint();
    assert_eq!(after.in_use_bytes, before.in_use_bytes);
    assert_eq!(after.idle_bytes, before.idle_bytes + SIZE_TABLE[2]);
    pool_drain_for_test();
}

#[test]
fn taking_a_recycled_block_moves_its_bytes_from_idle_back_to_in_use() {
    let before = start();
    let p = pool_alloc(SIZE_TABLE[2]);
    pool_free(p, SIZE_TABLE[2]);
    let p = pool_alloc(SIZE_TABLE[2]);
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
    let big = pool_alloc(above_table);
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
    let p = pool_alloc(64);
    assert_eq!(pool_footprint().in_use_bytes, before.in_use_bytes + 64);
    pool_free(p, 64);
    let idle = pool_footprint();
    assert_eq!(idle.in_use_bytes, before.in_use_bytes);
    assert_eq!(
        idle.idle_bytes,
        before.idle_bytes + 64,
        "the freed block rests in the pool"
    );
    let again = pool_alloc(64);
    assert_eq!(again, p, "the same size reuses the freed block");
    assert_eq!(pool_footprint().idle_bytes, before.idle_bytes);
    let other = pool_alloc(80);
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
    let a = pool_alloc(SIZE_TABLE[3]);
    let b = pool_alloc(SIZE_TABLE[3]);
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
    let p = pool_alloc(SIZE_TABLE[2]);
    unsafe { p.write_bytes(0, SIZE_TABLE[2]) };
    pool_free(p, SIZE_TABLE[2]);
    let recycled = pool_alloc(SIZE_TABLE[2]);
    let bytes = unsafe { std::slice::from_raw_parts(recycled, SIZE_TABLE[2]) };
    assert!(
        bytes.iter().all(|&b| b == UNWRITTEN_BYTE),
        "recycled block keeps old contents"
    );
    pool_free(recycled, SIZE_TABLE[2]);
    let exact = pool_alloc(SIZE_TABLE[0] - 16);
    let bytes = unsafe { std::slice::from_raw_parts(exact, SIZE_TABLE[0] - 16) };
    assert!(
        bytes.iter().all(|&b| b == UNWRITTEN_BYTE),
        "fresh block is not poisoned"
    );
    pool_free(exact, SIZE_TABLE[0] - 16);
    pool_drain_for_test();
}
