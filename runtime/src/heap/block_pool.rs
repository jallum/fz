//! Block size table + per-thread block pool.

use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::ptr::write_bytes;

/// Preset block capacities (bytes). Fibonacci-shape at the low end (§6.3) then
/// geometric tail (~×1.2, ceiling-rounded to 16 alignment). A tip starts at the
/// first entry and climbs the table.
///
/// The 32 entries reach ~7 MiB and are the capacities the pool recycles. A
/// block needing less than the first entry or more than the last is allocated
/// at exactly the size asked for (rounded to 16) and returned to the system
/// allocator when it is released.
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

/// The capacity one step above `capacity`: the next table entry, or 1.2x
/// rounded up to 16 once past the table.
pub fn next_block_capacity(capacity: usize) -> usize {
    SIZE_TABLE
        .iter()
        .copied()
        .find(|&size| size > capacity)
        .unwrap_or_else(|| round_up_16((capacity * 6).div_ceil(5)))
}

/// The pool's free-list index for `capacity`, or `None` for an exact block.
fn pooled_class(capacity: usize) -> Option<usize> {
    SIZE_TABLE.binary_search(&capacity).ok()
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

    /// Hand the block back: to the pool when its capacity is a table entry,
    /// to the system allocator otherwise.
    pub(super) fn release(self) {
        pool_free(self.start, self.capacity);
    }
}

/// Per-thread block pool (§6.6). One free list per table capacity. Spawn /
/// grow / gc pull from here; Heap::drop and gc()'s old-block release
/// return blocks here. Avoids per-spawn `malloc`/`free` churn under
/// heavy spawn pressure. Single-threaded for v1 (worker pool = 1); the multi-worker follow-up will switch to either
/// per-worker pools or a Mutex-guarded shared pool.
struct BlockPool {
    free_lists: [Vec<*mut u8>; SIZE_TABLE.len()],
    /// Blocks handed out by `alloc` and not yet returned through `free`.
    outstanding: usize,
}

impl BlockPool {
    const fn new() -> Self {
        // Const init: 32 empty Vecs. `[Vec::new(); N]` doesn't const-init
        // because Vec is not Copy; use a manual array build.
        Self {
            free_lists: [const { Vec::new() }; SIZE_TABLE.len()],
            outstanding: 0,
        }
    }

    /// A zeroed block of `capacity` bytes: recycled from the free list when
    /// the capacity is a table entry, otherwise fresh from the system
    /// allocator and not counted as outstanding.
    fn alloc(&mut self, capacity: usize) -> *mut u8 {
        let Some(idx) = pooled_class(capacity) else {
            return alloc_exact(capacity);
        };
        self.outstanding += 1;
        if let Some(p) = self.free_lists[idx].pop() {
            // Recycled blocks: zero before returning. Cheney + Heap::new
            // expect zero pages.
            unsafe {
                write_bytes(p, 0, capacity);
            }
            return p;
        }
        alloc_exact(capacity)
    }

    fn free(&mut self, p: *mut u8, capacity: usize) {
        let Some(idx) = pooled_class(capacity) else {
            unsafe { dealloc(p, block_layout(capacity)) };
            return;
        };
        self.outstanding -= 1;
        // Free lists grow unbounded in v1. A real-world deployment would
        // cap each list (e.g., 4 entries) and `dealloc` the overflow.
        // For now we accept the worst-case memory footprint to keep the
        // pool deterministic.
        self.free_lists[idx].push(p);
    }
}

fn alloc_exact(capacity: usize) -> *mut u8 {
    let p = unsafe { alloc_zeroed(block_layout(capacity)) };
    assert!(!p.is_null(), "block pool: malloc failed");
    p
}

impl Drop for BlockPool {
    fn drop(&mut self) {
        // At thread exit (or test teardown), free any cached blocks.
        for (idx, list) in self.free_lists.iter_mut().enumerate() {
            let layout = block_layout(SIZE_TABLE[idx]);
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
            let layout = block_layout(SIZE_TABLE[idx]);
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
    });
}

/// Pooled blocks this thread's pool has handed out and not had returned. Zero
/// once every heap and gift segment the thread created has been dropped. Exact
/// blocks, below the table or above it, are the system allocator's and are not
/// counted.
pub fn pool_outstanding_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().outstanding)
}

/// Total cached blocks across all table capacities.
pub fn pool_total_cached_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().free_lists.iter().map(|l| l.len()).sum())
}
