//! Block size table + per-thread block pool.

use std::alloc::{Layout, alloc, dealloc};
use std::cell::RefCell;
#[cfg(debug_assertions)]
use std::ptr::write_bytes;

/// Preset block capacities (bytes). Fibonacci-shape at the low end (§6.3) then
/// geometric tail (~×1.2, ceiling-rounded to 16 alignment). A tip starts at the
/// first entry and climbs the table.
///
/// The 32 entries reach ~7 MiB and are capacities the pool recycles, and so is
/// every multiple of 16 below the first entry (`SMALL_CLASSES` of them). A
/// block needing more than the last entry is allocated at exactly the size
/// asked for (rounded to 16) and returned to the system allocator when it is
/// released.
pub const SIZE_TABLE: [usize; 32] = build_size_table();

const fn build_size_table() -> [usize; 32] {
    let mut t = [0usize; 32];
    let prefix: [usize; 12] = [
        1024, 1536, 2560, 4096, 6656, 10752, 17408, 28160, 45568, 73728, 119296, 192768,
    ];
    let mut i = 0;
    while i < 12 {
        t[i] = prefix[i];
        i += 1;
    }
    while i < 32 {
        // next ≈ ceil(prev * 1.2) then aligned up to 16. Integer-only:
        //   ceil(prev * 6 / 5) = (prev * 6 + 4) / 5.
        let raw = (t[i - 1] * 6).div_ceil(5);
        t[i] = (raw + 15) & !15;
        i += 1;
    }
    t
}

/// `bytes` rounded up to the 16-byte slot every allocation occupies.
pub(super) fn round_up_16(bytes: usize) -> usize {
    (bytes + 15) & !15
}

/// The capacity of the smallest block that holds `bytes`: the smallest table
/// entry that fits when the request is within the table's range, and `bytes`
/// rounded up to 16 otherwise, below the first entry as well as past the last.
/// A block is at least one 16-byte slot.
pub fn pick_block_capacity(bytes: usize) -> usize {
    if bytes < SIZE_TABLE[0] {
        return round_up_16(bytes.max(1));
    }
    SIZE_TABLE
        .iter()
        .copied()
        .find(|&size| size >= bytes)
        .unwrap_or_else(|| round_up_16(bytes))
}

/// The capacity one step above `capacity`: the next table entry, and the last
/// entry once `capacity` has reached it.
pub fn next_block_capacity(capacity: usize) -> usize {
    SIZE_TABLE
        .iter()
        .copied()
        .find(|&size| size > capacity)
        .unwrap_or(SIZE_TABLE[SIZE_TABLE.len() - 1])
}

/// The capacity of a tip or to-space block for `bytes`: `pick_block_capacity`
/// clamped to the last table entry, so a young space past the table is a chain
/// of pooled blocks rather than one exact block.
pub fn pick_tip_capacity(bytes: usize) -> usize {
    pick_block_capacity(bytes).min(SIZE_TABLE[SIZE_TABLE.len() - 1])
}

/// The multiples of 16 below the first table entry: the 16-byte classes that
/// small blocks are pooled in.
const SMALL_CLASSES: usize = SIZE_TABLE[0] / 16 - 1;

/// One free list per small class, then one per table entry.
const CLASSES: usize = SMALL_CLASSES + SIZE_TABLE.len();

/// The pool's free-list index for `capacity`, or `None` for an exact block.
fn pooled_class(capacity: usize) -> Option<usize> {
    if capacity < SIZE_TABLE[0] {
        return (capacity != 0 && capacity.is_multiple_of(16)).then(|| capacity / 16 - 1);
    }
    SIZE_TABLE
        .binary_search(&capacity)
        .ok()
        .map(|entry| SMALL_CLASSES + entry)
}

/// The capacity of the blocks on free list `class`.
fn class_capacity(class: usize) -> usize {
    match class.checked_sub(SMALL_CLASSES) {
        None => (class + 1) * 16,
        Some(entry) => SIZE_TABLE[entry],
    }
}

fn block_layout(capacity: usize) -> Layout {
    Layout::from_size_align(capacity, 16).expect("bad block layout")
}

/// A block the heap has stopped bumping into: `start` is the block, `top` is
/// where its last allocation ended, and `capacity` is its size in bytes.
/// Abandoned blocks (overflowed mid-quantum) and adopted blocks (grafted from
/// another heap's gift) are both recorded this way, so a block's fill and its
/// capacity are each one subtraction, and the block carries what it needs to
/// release itself.
#[derive(Clone, Copy, Debug)]
pub(super) struct Block {
    pub(super) start: *mut u8,
    pub(super) top: *mut u8,
    pub(super) capacity: usize,
}

impl Block {
    pub(super) fn end(&self) -> *mut u8 {
        unsafe { self.start.add(self.capacity) }
    }

    pub(super) fn fill(&self) -> usize {
        unsafe { self.top.offset_from(self.start) as usize }
    }

    /// Hand the block back: to the pool when its capacity is pooled (a table
    /// entry or a multiple of 16 below the first), to the system allocator
    /// otherwise.
    pub(super) fn release(self) {
        pool_free(self.start, self.capacity);
    }
}

/// Per-thread block pool (§6.6). One free list per pooled capacity. Spawn /
/// grow / gc pull from here; Heap::drop and gc()'s old-block release
/// return blocks here. Avoids per-spawn `malloc`/`free` churn under
/// heavy spawn pressure. Single-threaded for v1 (worker pool = 1); the multi-worker follow-up will switch to either
/// per-worker pools or a Mutex-guarded shared pool.
struct BlockPool {
    free_lists: [Vec<*mut u8>; CLASSES],
    /// Blocks handed out by `alloc` and not yet returned through `free`.
    outstanding: usize,
    /// Capacity of the blocks handed out and not returned.
    block_bytes: usize,
    /// Capacity of the blocks resting in the free lists.
    idle_bytes: usize,
    /// The largest in-use total any grow has reached.
    peak_in_use_bytes: usize,
    /// Bytes of off-heap binary buffers allocated on this thread less those
    /// freed on it. A buffer freed on another thread leaves this thread's net
    /// below zero, so the net is signed; the in-use total carries only its
    /// positive part.
    binary_bytes: isize,
}

/// The bytes this thread's runtime holds, by who holds them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Footprint {
    /// Capacity of every block handed out and not returned, pooled and exact
    /// alike, plus the bytes of every off-heap binary buffer not yet freed.
    pub in_use_bytes: usize,
    /// Capacity of the blocks resting in the pool's free lists.
    pub idle_bytes: usize,
    /// The largest `in_use_bytes` any grow has reached.
    pub peak_in_use_bytes: usize,
}

impl BlockPool {
    const fn new() -> Self {
        // Const init: an empty Vec per class. `[Vec::new(); N]` doesn't const-init
        // because Vec is not Copy; use a manual array build.
        Self {
            free_lists: [const { Vec::new() }; CLASSES],
            outstanding: 0,
            block_bytes: 0,
            idle_bytes: 0,
            peak_in_use_bytes: 0,
            binary_bytes: 0,
        }
    }

    /// A block of `capacity` bytes whose contents are unspecified: recycled from the free list when
    /// the capacity is pooled, otherwise fresh from the system
    /// allocator and not counted as outstanding. Either way its bytes are in use.
    fn alloc(&mut self, capacity: usize) -> *mut u8 {
        self.block_bytes += capacity;
        self.record_peak();
        let Some(idx) = pooled_class(capacity) else {
            return alloc_exact(capacity);
        };
        self.outstanding += 1;
        if let Some(p) = self.free_lists[idx].pop() {
            self.idle_bytes -= capacity;
            return poisoned(p, capacity);
        }
        alloc_exact(capacity)
    }

    fn in_use_bytes(&self) -> usize {
        self.block_bytes + self.binary_bytes.max(0) as usize
    }

    fn record_peak(&mut self) {
        let in_use = self.in_use_bytes();
        self.peak_in_use_bytes = self.peak_in_use_bytes.max(in_use);
    }

    fn free(&mut self, p: *mut u8, capacity: usize) {
        self.block_bytes -= capacity;
        let Some(idx) = pooled_class(capacity) else {
            unsafe { dealloc(p, block_layout(capacity)) };
            return;
        };
        self.outstanding -= 1;
        self.idle_bytes += capacity;
        // Free lists grow unbounded in v1. A real-world deployment would
        // cap each list (e.g., 4 entries) and `dealloc` the overflow.
        // For now we accept the worst-case memory footprint to keep the
        // pool deterministic.
        self.free_lists[idx].push(p);
    }
}

fn alloc_exact(capacity: usize) -> *mut u8 {
    let p = unsafe { alloc(block_layout(capacity)) };
    assert!(!p.is_null(), "block pool: malloc failed");
    poisoned(p, capacity)
}

/// The byte a handed-out block is filled with in debug builds, so a read of
/// memory the heap has not written sees an implausible value, not a lucky zero.
#[cfg(debug_assertions)]
pub(crate) const UNWRITTEN_BYTE: u8 = 0xA5;

/// `p`, a block the heap has not yet written: filled with `UNWRITTEN_BYTE` in
/// debug builds, untouched in release builds.
#[cfg(debug_assertions)]
pub(crate) fn poisoned(p: *mut u8, capacity: usize) -> *mut u8 {
    unsafe { write_bytes(p, UNWRITTEN_BYTE, capacity) };
    p
}

#[cfg(not(debug_assertions))]
pub(crate) fn poisoned(p: *mut u8, _capacity: usize) -> *mut u8 {
    p
}

impl Drop for BlockPool {
    fn drop(&mut self) {
        // At thread exit (or test teardown), free any cached blocks.
        for (idx, list) in self.free_lists.iter_mut().enumerate() {
            let layout = block_layout(class_capacity(idx));
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
    }
}

thread_local! {
    static BLOCK_POOL: RefCell<BlockPool> = const { RefCell::new(BlockPool::new()) };
}

pub(super) fn pool_alloc(capacity: usize) -> *mut u8 {
    BLOCK_POOL.with(|p| p.borrow_mut().alloc(capacity))
}

/// Returns a block to the pool. If the TLS pool has already been dropped
/// (thread teardown ordering), falls back to a direct `dealloc` — the
/// block leaks nothing, just bypasses the cache.
pub(super) fn pool_free(p: *mut u8, capacity: usize) {
    let result = BLOCK_POOL.try_with(|pool| pool.borrow_mut().free(p, capacity));
    if result.is_err() {
        unsafe {
            dealloc(p, block_layout(capacity));
        }
    }
}

/// Test-only: drains every cached block in the per-thread pool back to
/// `dealloc`. Used to assert pool occupancy in acceptance tests; not
/// called from the runtime hot path.
#[cfg(test)]
pub fn pool_drain_for_test() {
    BLOCK_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        for (idx, list) in pool.free_lists.iter_mut().enumerate() {
            let layout = block_layout(class_capacity(idx));
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
        pool.idle_bytes = 0;
    });
}

/// Pooled blocks this thread's pool has handed out and not had returned. Zero
/// once every heap and gift segment the thread created has been dropped. Exact
/// blocks, above the table, are the system allocator's and are not counted.
pub fn pool_outstanding_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().outstanding)
}

/// Total cached blocks across all pooled capacities.
pub fn pool_total_cached_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().free_lists.iter().map(|l| l.len()).sum())
}

/// The bytes this thread's runtime holds right now, and the most it has held.
pub fn pool_footprint() -> Footprint {
    BLOCK_POOL.with(|pool| {
        let pool = pool.borrow();
        Footprint {
            in_use_bytes: pool.in_use_bytes(),
            idle_bytes: pool.idle_bytes,
            peak_in_use_bytes: pool.peak_in_use_bytes,
        }
    })
}

/// An off-heap binary block of `bytes` bytes (header, bytes and trailing NUL)
/// came into existence: its bytes are in use until `binary_buffer_freed`.
pub(crate) fn binary_buffer_allocated(bytes: usize) {
    BLOCK_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        pool.binary_bytes += bytes as isize;
        pool.record_peak();
    });
}

/// An off-heap binary block of `bytes` bytes was freed, on any thread. A
/// thread whose pool is already torn down has nothing left to count.
pub(crate) fn binary_buffer_freed(bytes: usize) {
    let _ = BLOCK_POOL.try_with(|pool| pool.borrow_mut().binary_bytes -= bytes as isize);
}

#[cfg(test)]
#[path = "block_pool_test.rs"]
mod block_pool_test;
