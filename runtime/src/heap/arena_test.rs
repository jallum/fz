use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

/// A small range of its own, so a test owns every span it sees. Each gets
/// hints of its own, so the space above one is free for it to grow into.
fn small_range() -> Reservation {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, Ordering::Relaxed);
    Reservation::reserve(COMMIT_CHUNK, 0x1000_0000_0000 + (n << 34), 0x5000_0000_0000 + (n << 30))
        .expect("a small range can be reserved")
}

fn granule_index(range: &Reservation, p: *mut u8) -> usize {
    (p as usize - range.base) >> GRANULE_SHIFT
}

#[test]
fn a_span_is_whole_granules_and_a_fresh_one_reads_not_young() {
    let range = small_range();
    let span = span_len(1);
    assert_eq!(span, GRANULE, "even a one-byte block takes a granule to itself");
    let p = range.claim(span);
    assert!((p as usize - range.base).is_multiple_of(GRANULE));
    assert!(!range.is_young(p));
    #[cfg(debug_assertions)]
    assert!(!range.in_block(p));
}

#[test]
fn a_young_block_marks_every_granule_of_its_span_and_nothing_beyond() {
    let range = small_range();
    let span = span_len(10 * GRANULE + 1);
    let before = range.claim(GRANULE);
    let p = range.claim(span);
    let after = range.claim(GRANULE);

    range.made_pooled(p, span, Age::Young);
    for granule in 0..span / GRANULE {
        assert!(range.is_young(unsafe { p.add(granule * GRANULE) }));
    }
    assert!(range.is_young(unsafe { p.add(span - 1) }), "the last byte of the span");
    assert!(!range.is_young(before), "the span before is not touched");
    assert!(!range.is_young(after), "the span after is not touched");
}

#[test]
fn a_pooled_block_made_again_at_the_age_its_span_already_has_writes_nothing() {
    let range = small_range();
    let span = span_len(4 * GRANULE);
    let p = range.claim(span);

    let start = young_mark_bytes();
    range.made_pooled(p, span, Age::Young);
    assert_eq!(
        young_mark_bytes() - start,
        span / GRANULE,
        "a fresh span is marked once"
    );

    let marked = young_mark_bytes();
    range.made_pooled(p, span, Age::Young);
    assert_eq!(
        young_mark_bytes(),
        marked,
        "a block reused young over a young span writes nothing"
    );
    assert!(range.is_young(p));
}

#[test]
fn a_pooled_block_made_old_over_a_young_leftover_clears_the_span() {
    let range = small_range();
    let span = span_len(6 * GRANULE);
    let p = range.claim(span);
    range.made_pooled(p, span, Age::Young);

    let marked = young_mark_bytes();
    range.made_pooled(p, span, Age::Old);
    assert_eq!(
        young_mark_bytes() - marked,
        span / GRANULE,
        "the leftover mark is cleared"
    );
    for granule in 0..span / GRANULE {
        assert!(
            !range.is_young(unsafe { p.add(granule * GRANULE) }),
            "granule {granule} reads not young"
        );
    }
    #[cfg(debug_assertions)]
    assert!(range.in_block(p), "a debug build records the old block");

    let again = young_mark_bytes();
    range.made_pooled(p, span, Age::Old);
    assert_eq!(
        young_mark_bytes(),
        again,
        "an old block over an old span writes nothing"
    );
    range.made_pooled(p, span, Age::Young);
    assert!(
        range.is_young(unsafe { p.add(span - 1) }),
        "made young again, the whole span reads young"
    );
}

#[test]
fn an_exact_block_marks_when_made_young_and_clears_when_released() {
    let range = small_range();
    let span = span_len(3 * GRANULE + 5);
    let p = range.take_span(span);

    let start = young_mark_bytes();
    range.made_exact(p, span, Age::Young);
    assert!(range.is_young(unsafe { p.add(span - 1) }));
    range.released_exact(p, span);
    assert_eq!(
        young_mark_bytes() - start,
        2 * (span / GRANULE),
        "a young exact block writes its mark and clears it"
    );
    assert!(
        !range.is_young(p),
        "its span is unmarked, whatever block is cut from it next"
    );

    let start = young_mark_bytes();
    range.made_exact(p, span, Age::Old);
    assert!(!range.is_young(p));
    range.released_exact(p, span);
    assert_eq!(young_mark_bytes(), start, "an old exact block never writes youth");
}

#[test]
fn two_blocks_never_share_a_granule() {
    let range = small_range();
    let capacities = [
        1,
        16,
        48,
        GRANULE.saturating_sub(16).max(1),
        GRANULE,
        GRANULE + 16,
        1024,
        1536,
        7 * GRANULE + 3,
    ];
    let mut owned = std::collections::BTreeSet::new();
    for capacity in capacities {
        let span = span_len(capacity);
        let p = range.claim(span);
        for granule in 0..span / GRANULE {
            assert!(
                owned.insert(granule_index(&range, p) + granule),
                "a granule of a {capacity}-byte block already belongs to another block"
            );
        }
    }
}

#[test]
fn an_address_outside_the_range_is_not_contained() {
    let range = small_range();
    let on_stack = 0u64;
    let on_heap = Box::new(0u64);
    assert!(!range.contains(&on_stack as *const u64 as *const u8));
    assert!(!range.contains(&*on_heap as *const u64 as *const u8));
    assert!(!range.contains(std::ptr::null()));
    assert!(
        !range.contains((range.base + range.reserved.load(Ordering::Relaxed)) as *const u8),
        "one past the end"
    );
}

#[test]
fn the_range_grows_by_a_chunk_at_exactly_its_end_and_ages_read_across_the_boundary() {
    let range = small_range();
    assert_eq!(range.reserved.load(Ordering::Relaxed), COMMIT_CHUNK);
    let end = range.base + COMMIT_CHUNK;

    // A block that straddles the first chunk's end.
    let filler = range.claim(COMMIT_CHUNK - 4 * GRANULE);
    let straddler_span = 8 * GRANULE;
    let straddler = range.claim(straddler_span);
    assert_eq!(
        straddler as usize,
        end - 4 * GRANULE,
        "the bump continued past the old end"
    );
    assert_eq!(
        range.reserved.load(Ordering::Relaxed),
        2 * COMMIT_CHUNK,
        "one chunk was added"
    );
    assert!(range.contains(end as *const u8), "the new chunk is part of the range");

    range.made_pooled(straddler, straddler_span, Age::Young);
    for granule in 0..8 {
        assert!(
            range.is_young(unsafe { straddler.add(granule * GRANULE) }),
            "granule {granule}, {} the old end",
            if granule < 4 { "before" } else { "after" }
        );
    }
    assert!(!range.is_young(filler), "the block before is not young");
    let beyond = range.claim(GRANULE);
    assert!(!range.is_young(beyond), "the block after is not young");
}

#[test]
fn a_block_wider_than_a_chunk_grows_the_range_by_as_many_chunks_as_it_needs() {
    let range = small_range();
    let p = range.claim(3 * COMMIT_CHUNK);
    assert_eq!(p as usize, range.base);
    assert!(range.reserved.load(Ordering::Relaxed) >= 3 * COMMIT_CHUNK);
    unsafe { p.add(3 * COMMIT_CHUNK - 1).write(7) };
}

#[test]
fn growing_where_the_next_chunk_is_taken_panics_naming_the_reserved_size_and_the_bytes_claimed() {
    let range = small_range();
    // Take the address the next chunk belongs at.
    let squatter =
        map_inaccessible(range.base + COMMIT_CHUNK, GRANULE.max(16384), true).expect("the space above is free");
    range.claim(COMMIT_CHUNK);
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| range.claim(GRANULE)))
        .expect_err("a range that cannot grow in place panics");
    unsafe { libc::munmap(squatter as *mut libc::c_void, GRANULE.max(16384)) };
    let message = panic
        .downcast_ref::<String>()
        .expect("the panic carries a message")
        .clone();
    assert!(message.contains("heap range cannot grow"), "{message}");
    assert!(message.contains(&format!("{COMMIT_CHUNK} bytes reserved")), "{message}");
    assert!(message.contains(&format!("{COMMIT_CHUNK} claimed")), "{message}");
}

#[test]
fn a_freed_span_is_reused_before_the_range_grows() {
    let range = small_range();
    let span = span_len(8 << 20);
    let p = range.take_span(span);
    let claimed = range.claimed_bytes();
    range.give_span(p, span);
    assert_eq!(range.free_span_bytes(), span);

    let again = range.take_span(span);
    assert_eq!(again, p, "the freed span came back");
    assert_eq!(range.claimed_bytes(), claimed, "the range did not grow");
    assert_eq!(range.free_span_bytes(), 0);
}

#[test]
fn a_smaller_block_takes_part_of_a_freed_span_and_the_rest_stays_free() {
    let range = small_range();
    let big = span_len(8 << 20);
    let small = span_len(3 << 20);
    let p = range.take_span(big);
    range.give_span(p, big);

    let part = range.take_span(small);
    assert_eq!(part, p);
    assert_eq!(range.free_span_bytes(), big - small);
    let rest = range.take_span(big - small);
    assert_eq!(rest as usize, p as usize + small, "the remainder is the next span");
    assert_eq!(range.free_span_bytes(), 0);
}

#[test]
fn neighbouring_freed_spans_rejoin_into_one() {
    let range = small_range();
    let span = span_len(2 << 20);
    let a = range.take_span(span);
    let b = range.take_span(span);
    let c = range.take_span(span);
    range.give_span(a, span);
    range.give_span(c, span);
    range.give_span(b, span);
    assert_eq!(range.free_span_bytes(), 3 * span);

    let claimed = range.claimed_bytes();
    let whole = range.take_span(3 * span);
    assert_eq!(whole, a, "three freed neighbours serve one block of their total");
    assert_eq!(range.claimed_bytes(), claimed);
}

#[test]
fn the_smallest_freed_span_that_fits_is_the_one_reused() {
    let range = small_range();
    let big = span_len(6 << 20);
    let snug = span_len(4 << 20);
    let a = range.take_span(big);
    let _gap = range.take_span(GRANULE);
    let b = range.take_span(snug);
    range.give_span(a, big);
    range.give_span(b, snug);
    assert_eq!(range.take_span(snug), b);
}

/// The bytes of `[p, p + bytes)` that are resident, by `mincore` over exactly
/// those pages, so that other threads' allocation elsewhere cannot move it.
fn held_bytes(p: *mut u8, bytes: usize) -> usize {
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let mut flags = vec![0 as libc::c_char; bytes / page];
    let result = unsafe { libc::mincore(p as *mut libc::c_void, bytes, flags.as_mut_ptr() as _) };
    assert_eq!(result, 0, "mincore: {}", std::io::Error::last_os_error());
    flags.iter().filter(|&&flag| flag & 1 != 0).count() * page
}

#[test]
fn a_freed_span_gives_its_pages_back_and_a_reused_one_can_be_written_again() {
    let range = small_range();
    let bytes = 48 << 20;
    let span = span_len(bytes);
    let p = range.take_span(span);
    unsafe { p.write_bytes(0xAB, bytes) };
    let touched = held_bytes(p, bytes);

    range.give_span(p, span);
    let freed = held_bytes(p, bytes);
    assert!(
        freed + bytes / 2 <= touched,
        "a freed span's pages leave memory: {touched} bytes held touched, {freed} freed"
    );

    let again = range.take_span(span);
    assert_eq!(again, p);
    unsafe { again.write_bytes(0xCD, bytes) };
    assert_eq!(unsafe { *again.add(bytes - 1) }, 0xCD);
}

#[test]
fn the_granule_is_a_power_of_two_a_block_alignment_divides() {
    assert!(GRANULE >= 16 && GRANULE.is_power_of_two());
}
