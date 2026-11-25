//! Block size table + per-thread block pool.
//!
//! Every block is a span of the process's reserved range (`arena`). A pooled
//! capacity (a table entry, or a multiple of 16 below the first) recycles
//! through the thread's free list; a thread that exits hands its free blocks to
//! a process-wide spill list, which any thread's pool draws on before it claims
//! fresh space. A block off the table is a span of its own: its pages return to
//! the operating system when it is released, and the span is reused.
//!
//! A free list keeps blocks warm (their pages resident) for as long as they are
//! wanted. A block of a trimmed class (`TRIM_FROM_CAPACITY` and up) that no
//! allocation of its class has needed for a whole epoch, an epoch being as many
//! bytes handed out as `EPOCH_FACTOR` times what the pool holds in use (and at
//! least `EPOCH_FLOOR`), gives
//! its pages back to the operating system and stays on the list as a cold block:
//! it is handed out again as any other and its pages come back as they are
//! touched. The bytes a pool keeps resident for idle blocks are therefore those
//! its recent allocations used, not those of every size the heap once needed.
//!
//! A pooled block marks the age table (`arena::is_young`) when it is made, and
//! only when the span's mark is not already the one it wants: a released pooled
//! block keeps its bytes, and a span is one capacity at one address for good, so
//! a block reused at the same age writes nothing, and one made old over a young
//! block's leftover mark clears it. A block off the table marks the table when
//! it is made young and clears it when it is released, because its span may be
//! split or joined to another.

use super::arena::{Age, range, span_len};
use std::cell::RefCell;
#[cfg(debug_assertions)]
use std::ptr::write_bytes;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Preset block capacities (bytes). Fibonacci-shape at the low end (§6.3) then
/// geometric tail (~×1.2, ceiling-rounded to 16 alignment). A tip starts at the
/// first entry and climbs the table.
///
/// The 32 entries reach ~7 MiB and are capacities the pool recycles, and so is
/// every multiple of 16 below the first entry (`SMALL_CLASSES` of them). A
/// block needing more than the last entry is allocated at exactly the size
/// asked for (rounded to 16), a span of its own that is given back when it is
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

/// Whether a block of `capacity` bytes returns to the pool when released,
/// rather than to the span list.
pub(super) fn is_pooled_capacity(capacity: usize) -> bool {
    pooled_class(capacity).is_some()
}

/// The smallest capacity whose idle blocks are trimmed: below it a block is
/// fewer than a few pages, and returning them costs more than they hold.
const TRIM_FROM_CAPACITY: usize = 64 << 10;

/// The first free list that is trimmed.
const TRIM_FROM_CLASS: usize = SMALL_CLASSES + trim_entry();

const fn trim_entry() -> usize {
    let mut entry = 0;
    while SIZE_TABLE[entry] < TRIM_FROM_CAPACITY {
        entry += 1;
    }
    entry
}

/// How many times the in-use bytes an epoch hands out. A shorter epoch trims
/// blocks a program is about to want again and pays to fault their pages back;
/// a longer one holds idle pages resident longer.
const EPOCH_FACTOR: usize = 4;

/// The fewest bytes an epoch lasts, so a small heap does not trim at every
/// allocation.
const EPOCH_FLOOR: usize = 1 << 20;

/// The capacity of the blocks on free list `class`.
fn class_capacity(class: usize) -> usize {
    match class.checked_sub(SMALL_CLASSES) {
        None => (class + 1) * 16,
        Some(entry) => SIZE_TABLE[entry],
    }
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
    /// entry or a multiple of 16 below the first), to the span list
    /// otherwise.
    pub(super) fn release(self) {
        pool_free(self.start, self.capacity);
    }
}

/// Per-thread block pool (§6.6). One free list per pooled capacity. Spawn /
/// grow / gc pull from here; Heap::drop and gc()'s old-block release
/// return blocks here. Avoids per-spawn `malloc`/`free` churn under
/// heavy spawn pressure. The lists are the thread's own; fresh space and the
/// spill list are the process's.
struct BlockPool {
    free_lists: [Vec<*mut u8>; CLASSES],
    /// Per trimmed list, how many blocks at the bottom of the list are cold.
    cold: [usize; CLASSES],
    /// Per trimmed list, the fewest blocks it has held since the epoch began:
    /// those below it have gone the whole epoch unwanted.
    low_water: [usize; CLASSES],
    /// Bytes handed out since the epoch began.
    epoch_bytes: usize,
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
            cold: [0; CLASSES],
            low_water: [0; CLASSES],
            epoch_bytes: 0,
            outstanding: 0,
            block_bytes: 0,
            idle_bytes: 0,
            peak_in_use_bytes: 0,
            binary_bytes: 0,
        }
    }

    /// A block of `capacity` bytes of age `age` whose contents are unspecified:
    /// recycled from the free list or the spill list when the capacity is
    /// pooled, otherwise a span of the range. Either way its bytes are in use.
    /// Only pooled blocks count as outstanding.
    fn alloc(&mut self, capacity: usize, age: Age) -> *mut u8 {
        self.block_bytes += capacity;
        self.record_peak();
        let span = span_len(capacity);
        let p = match pooled_class(capacity) {
            None => {
                let p = range().take_span(span);
                range().made_exact(p, span, age);
                p
            }
            Some(idx) => {
                self.outstanding += 1;
                let p = match self.take_idle(idx, capacity) {
                    Some(p) => p,
                    None => spilled(idx).unwrap_or_else(|| range().claim(span)),
                };
                range().made_pooled(p, span, age);
                self.end_epoch_if_over(capacity);
                p
            }
        };
        poisoned(p, capacity)
    }

    /// The block most recently freed to list `idx`, if any.
    fn take_idle(&mut self, idx: usize, capacity: usize) -> Option<*mut u8> {
        let list = &mut self.free_lists[idx];
        let p = list.pop()?;
        self.idle_bytes -= capacity;
        if idx >= TRIM_FROM_CLASS {
            self.low_water[idx] = self.low_water[idx].min(list.len());
            self.cold[idx] = self.cold[idx].min(list.len());
        }
        Some(p)
    }

    /// Count `capacity` bytes toward the epoch, and when the pool has handed
    /// out `EPOCH_FACTOR` times the bytes it holds in use, trim.
    fn end_epoch_if_over(&mut self, capacity: usize) {
        self.epoch_bytes += capacity;
        if self.epoch_bytes >= (self.in_use_bytes() * EPOCH_FACTOR).max(EPOCH_FLOOR) {
            self.trim();
        }
    }

    /// Give back the pages of every block that went unwanted for the whole
    /// epoch, and begin the next one.
    fn trim(&mut self) {
        self.epoch_bytes = 0;
        for idx in TRIM_FROM_CLASS..CLASSES {
            let capacity = class_capacity(idx);
            let span = span_len(capacity);
            while self.cold[idx] < self.low_water[idx] {
                range().drop_pages(self.free_lists[idx][self.cold[idx]], span);
                self.cold[idx] += 1;
            }
            self.low_water[idx] = self.free_lists[idx].len();
        }
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
            give_back(p, capacity);
            return;
        };
        self.outstanding -= 1;
        self.idle_bytes += capacity;
        // Free lists grow unbounded in v1. A real-world deployment would
        // cap each list (e.g., 4 entries) and spill the overflow.
        // For now we accept the worst-case memory footprint to keep the
        // pool deterministic.
        self.free_lists[idx].push(p);
    }

    /// Hand every resting block to the spill list: each free list's storage
    /// moves whole, so no pointer is copied and no capacity stays behind.
    fn spill_all(&mut self) {
        let mut spill = SPILL.lock().unwrap();
        for (idx, list) in self.free_lists.iter_mut().enumerate() {
            if list.is_empty() {
                continue;
            }
            SPILLED.fetch_add(list.len(), Ordering::Relaxed);
            spill.0[idx].push(std::mem::take(list));
        }
        self.cold = [0; CLASSES];
        self.low_water = [0; CLASSES];
    }
}

/// The pooled blocks of exited threads, by class: per class, the free lists
/// the threads exited with (and blocks released after) in the order they came.
struct Spilled([Vec<Vec<*mut u8>>; CLASSES]);

// The blocks are spans of the process's range, owned by no thread.
unsafe impl Send for Spilled {}

static SPILL: Mutex<Spilled> = Mutex::new(Spilled([const { Vec::new() }; CLASSES]));

/// How many blocks `SPILL` holds, so a pool with nothing spilled to take never
/// locks.
static SPILLED: AtomicUsize = AtomicUsize::new(0);

fn spilled(class: usize) -> Option<*mut u8> {
    if SPILLED.load(Ordering::Relaxed) == 0 {
        return None;
    }
    let lists = &mut SPILL.lock().unwrap().0[class];
    let list = lists.last_mut()?;
    let p = list.pop();
    if list.is_empty() {
        lists.pop();
    }
    SPILLED.fetch_sub(1, Ordering::Relaxed);
    p
}

fn spill(class: usize, p: *mut u8) {
    let lists = &mut SPILL.lock().unwrap().0[class];
    match lists.last_mut() {
        Some(list) => list.push(p),
        None => lists.push(vec![p]),
    }
    SPILLED.fetch_add(1, Ordering::Relaxed);
}

/// A block released with no pool to take it: a pooled one goes to the spill
/// list with its mark as it is, any other one's span to the span list with its
/// mark cleared.
fn give_back(p: *mut u8, capacity: usize) {
    match pooled_class(capacity) {
        Some(class) => spill(class, p),
        None => {
            let span = span_len(capacity);
            range().released_exact(p, span);
            range().give_span(p, span);
        }
    }
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
        // At thread exit (or test teardown), the cached blocks go to the spill list.
        self.spill_all();
    }
}

thread_local! {
    static BLOCK_POOL: RefCell<BlockPool> = const { RefCell::new(BlockPool::new()) };
}

/// A block of `capacity` bytes that is `age` from the moment it exists.
pub(super) fn pool_alloc(capacity: usize, age: Age) -> *mut u8 {
    BLOCK_POOL.with(|p| p.borrow_mut().alloc(capacity, age))
}

/// Returns a block to the pool. If the TLS pool has
/// already been dropped (thread teardown ordering), the block goes straight to
/// the spill list or span list: it leaks nothing, just bypasses the cache.
pub(super) fn pool_free(p: *mut u8, capacity: usize) {
    let result = BLOCK_POOL.try_with(|pool| pool.borrow_mut().free(p, capacity));
    if result.is_err() {
        give_back(p, capacity);
    }
}

/// Test-only: hands every cached block in the per-thread pool to the spill
/// list. Used to assert pool occupancy in acceptance tests; not called from
/// the runtime hot path.
#[cfg(test)]
pub fn pool_drain_for_test() {
    BLOCK_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        pool.spill_all();
        pool.idle_bytes = 0;
    });
}

/// Pooled blocks this thread's pool has handed out and not had returned. Zero
/// once every heap and gift segment the thread created has been dropped. Exact
/// blocks, above the table, are spans of their own and are not counted.
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
