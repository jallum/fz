//! Block size table + per-thread block pool.

use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;

/// Preset block sizes (bytes). Fibonacci-shape at the low end (§6.3) then
/// geometric tail (~×1.2, ceiling-rounded to 16 alignment). Cheney picks the
/// smallest entry that fits `live_bytes + slack`.
///
/// 32 entries covers ~6 MiB — heaps larger than the tail clamp to the last
/// class (`pick_size_class` never panics).
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

/// Smallest size_class whose `SIZE_TABLE[class]` ≥ `bytes`. Clamps to the
/// last index for inputs that exceed the tail (§6.3) — never panics.
pub fn pick_size_class(bytes: usize) -> u8 {
    for (idx, &size) in SIZE_TABLE.iter().enumerate() {
        if size >= bytes {
            return idx as u8;
        }
    }
    (SIZE_TABLE.len() - 1) as u8
}

/// Per-thread block pool (§6.6). One free list per size_class. Spawn /
/// grow / gc pull from here; Heap::drop and gc()'s old-block release
/// return blocks here. Avoids per-spawn `malloc`/`free` churn under
/// heavy spawn pressure. Single-threaded for v1 (worker pool = 1, per
/// fz-ul4.19.1); the multi-worker follow-up will switch to either
/// per-worker pools or a Mutex-guarded shared pool.
struct BlockPool {
    free_lists: [Vec<*mut u8>; SIZE_TABLE.len()],
}

impl BlockPool {
    const fn new() -> Self {
        // Const init: 32 empty Vecs. `[Vec::new(); N]` doesn't const-init
        // because Vec is not Copy; use a manual array build.
        Self {
            free_lists: [const { Vec::new() }; SIZE_TABLE.len()],
        }
    }

    fn alloc(&mut self, size_class: u8) -> *mut u8 {
        let idx = size_class as usize;
        let size = SIZE_TABLE[idx];
        if let Some(p) = self.free_lists[idx].pop() {
            // Recycled blocks: zero before returning. Cheney + Heap::new
            // expect zero pages.
            unsafe {
                std::ptr::write_bytes(p, 0, size);
            }
            return p;
        }
        let layout = Layout::from_size_align(size, 16).expect("bad block layout");
        let p = unsafe { alloc_zeroed(layout) };
        assert!(!p.is_null(), "block pool: malloc failed");
        p
    }

    fn free(&mut self, p: *mut u8, size_class: u8) {
        // Free lists grow unbounded in v1. A real-world deployment would
        // cap each list (e.g., 4 entries) and `dealloc` the overflow.
        // For now we accept the worst-case memory footprint to keep the
        // pool deterministic.
        self.free_lists[size_class as usize].push(p);
    }
}

impl Drop for BlockPool {
    fn drop(&mut self) {
        // At thread exit (or test teardown), free any cached blocks.
        for (idx, list) in self.free_lists.iter_mut().enumerate() {
            let size = SIZE_TABLE[idx];
            let layout = Layout::from_size_align(size, 16).expect("bad block layout");
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

pub(super) fn pool_alloc(size_class: u8) -> *mut u8 {
    BLOCK_POOL.with(|p| p.borrow_mut().alloc(size_class))
}

/// Returns a block to the pool. If the TLS pool has already been dropped
/// (thread teardown ordering), falls back to a direct `dealloc` — the
/// block leaks nothing, just bypasses the cache.
pub(super) fn pool_free(p: *mut u8, size_class: u8) {
    let result = BLOCK_POOL.try_with(|pool| pool.borrow_mut().free(p, size_class));
    if result.is_err() {
        let size = SIZE_TABLE[size_class as usize];
        let layout = Layout::from_size_align(size, 16).expect("bad block layout");
        unsafe {
            dealloc(p, layout);
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
            let size = SIZE_TABLE[idx];
            let layout = Layout::from_size_align(size, 16).expect("bad block layout");
            for p in list.drain(..) {
                unsafe {
                    dealloc(p, layout);
                }
            }
        }
    });
}

/// Test-only: total cached blocks across all size classes.
#[cfg(test)]
pub fn pool_total_cached_blocks() -> usize {
    BLOCK_POOL.with(|pool| pool.borrow().free_lists.iter().map(|l| l.len()).sum())
}
