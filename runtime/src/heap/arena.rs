//! The reserved range every heap block lives in, and the age table beside it.
//!
//! One range of address space is reserved for the whole process, `PROT_NONE`,
//! and committed read-write in chunks as the bump reaches them. A heap block
//! is a span of it: a granule-aligned run of whole granules. A table holds one
//! byte per granule, and a granule reads young when its byte is `YOUNG`: its
//! block an allocation is filling or has filled since the last collection,
//! or a gift's block that no collection has seen. Every other granule (an old
//! block's, an unused one's) reads zero, and so does an address outside the
//! range. Whether an object is young is therefore a subtract, a bound check, a
//! shift and a byte load from its address.
//!
//! The range grows instead of capping. The first chunk is reserved at a high
//! address (`RANGE_HINT`) with nothing mapped above it, and when the bump
//! reaches the end the next chunk is reserved at exactly the end address, so
//! the range stays one run and `(addr - base)` stays the whole test. The table
//! grows the same way, from its own hint. A chunk that lands anywhere else is a
//! panic naming the reserved size and the bytes claimed; there is no fallback.
//!
//! Blocks never share a granule, so a table byte has one owner at a time: the
//! thread whose heap holds the block. A span is typed for good by how it is
//! first claimed. A pooled span (a table capacity, or a multiple of 16 below
//! the first) is claimed for one capacity and only ever holds a block of that
//! capacity, at that address: it is never split, merged or resized, so all its
//! table bytes are always equal. A block takes its mark when it is made by
//! reading the byte under its first granule, and writes the span only when that
//! byte is not already the mark it wants; a released pooled block leaves its
//! bytes as they are. An exact or huge span comes from the span list, which
//! splits and rejoins, so it keeps the stricter discipline: a young exact block
//! writes its mark when it is made and clears it when it is released, and a
//! free span's table bytes are all zero.
//!
//! Nothing reads the age of a free block: `Reservation::is_young`, `FromSpace::moves`
//! and `assert_classified` are asked only about addresses of live objects (a
//! live frame, a pointer a live object holds, an object just written), and a
//! block is released only once nothing live points into it. A free pooled block
//! therefore reads as it was last made, which a debug build's `in_block` cannot
//! tell from a live block.
//!
//! A debug build also records `OLD` under an old block, so that a check can
//! tell a block from the absence of one (`in_block`); that byte is never read
//! as youth. In a release build `OLD` is zero.
//!
//! Off-heap binaries, resources and static literals are the system
//! allocator's and lie outside the range.

use std::collections::BTreeMap;
use std::ptr::write_bytes;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// The table's granule is `1 << GRANULE_SHIFT` bytes: 32.
pub(super) const GRANULE_SHIFT: u32 = 5;

/// Bytes of address space one table byte describes.
pub(super) const GRANULE: usize = 1 << GRANULE_SHIFT;

/// `bytes` rounded up to whole granules: the span a block of that capacity
/// occupies.
pub(super) const fn span_len(bytes: usize) -> usize {
    (bytes + GRANULE - 1) & !(GRANULE - 1)
}

/// How old a block is when it is made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Age {
    /// Allocation fills the block, or it is a gift's block that no collection
    /// has seen.
    Young,
    /// A collection made the block.
    Old,
}

/// The table byte under a young block's granules.
const YOUNG: u8 = 1;

/// The table byte under an old block's granules, in a debug build.
#[cfg(debug_assertions)]
const OLD: u8 = 2;

/// The size of a chunk the process asks for first, and the least it settles
/// for when the system refuses. The kernel's work to set up and tear down a
/// mapping grows with its size, about 7,000 instructions per GiB on macOS
/// whether or not a page is ever touched, so the first chunk is the heap a
/// small process may hold, not more; the range grows by chunks of the size the
/// first one got.
const CHUNK_MAX: usize = 16 << 30;
const CHUNK_MIN: usize = 4 << 30;

/// Where the first chunk of the range and of the table are asked for: high in
/// the address space, where the system maps nothing for a long way above (the
/// system's own allocations sit far below or far above). The range may grow to
/// `TABLE_HINT - RANGE_HINT` bytes before it meets the table.
const RANGE_HINT: usize = 0x2000_0000_0000;
const TABLE_HINT: usize = 0x3000_0000_0000;

/// The unit in which the range and its table become read-write. A multiple of
/// the page size times the granule for every page size and granule the runtime
/// supports.
const COMMIT_CHUNK: usize = 64 << 20;

/// One reserved range, its age table, and the bump and span list that hand out
/// spans of it.
pub(crate) struct Reservation {
    base: usize,
    /// The table's first byte, which describes the range's first granule. The
    /// table is reserved and grows with the range: `reserved >> GRANULE_SHIFT`
    /// bytes of it are mapped.
    table: *mut AtomicU8,
    /// The bytes added each time the range grows.
    chunk: usize,
    /// Bytes of the range, from `base`, that are reserved. Only grows.
    reserved: AtomicUsize,
    grow_lock: Mutex<()>,
    page: usize,
    /// Bytes of the range handed out by the bump, from `base`.
    claimed: AtomicUsize,
    /// Bytes of the range, from `base`, that are read-write.
    committed: AtomicUsize,
    commit_lock: Mutex<()>,
    spans: Mutex<FreeSpans>,
}

// SAFETY: the pointers name mappings owned for the reservation's life. A table
// byte is written only by the thread that owns the block over its granule, and
// is read and written as an atomic.
unsafe impl Send for Reservation {}
unsafe impl Sync for Reservation {}

static RANGE: OnceLock<Reservation> = OnceLock::new();

/// The process's range, reserved on first use.
pub(crate) fn range() -> &'static Reservation {
    RANGE.get_or_init(Reservation::reserve_largest)
}

impl Reservation {
    /// The largest first chunk the system grants, halving from `CHUNK_MAX` to
    /// `CHUNK_MIN`; a refusal of the least is fatal.
    fn reserve_largest() -> Reservation {
        let mut chunk = CHUNK_MAX;
        loop {
            match Reservation::reserve(chunk, RANGE_HINT, TABLE_HINT) {
                Ok(reservation) => return reservation,
                Err(_) if chunk > CHUNK_MIN => chunk /= 2,
                Err(error) => {
                    panic!("heap range: the system refused to reserve {chunk} bytes of address space: {error}")
                }
            }
        }
    }

    /// Reserve a first chunk of `chunk` bytes (a multiple of `COMMIT_CHUNK`)
    /// of address space, and the table for it, both inaccessible until
    /// committed, asking for them at the hints. Where the system puts them
    /// when a hint is taken is its choice; growing is what insists on an
    /// address.
    pub(super) fn reserve(chunk: usize, range_hint: usize, table_hint: usize) -> Result<Reservation, std::io::Error> {
        assert!(chunk.is_multiple_of(COMMIT_CHUNK), "a chunk is whole commit chunks");
        let base = map_inaccessible(range_hint, chunk, false)?;
        let table = match map_inaccessible(table_hint, chunk >> GRANULE_SHIFT, false) {
            Ok(table) => table,
            Err(error) => {
                unsafe { libc::munmap(base as *mut libc::c_void, chunk) };
                return Err(error);
            }
        };
        Ok(Reservation {
            base,
            table: table as *mut AtomicU8,
            chunk,
            reserved: AtomicUsize::new(chunk),
            grow_lock: Mutex::new(()),
            page: unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize,
            claimed: AtomicUsize::new(0),
            committed: AtomicUsize::new(0),
            commit_lock: Mutex::new(()),
            spans: Mutex::new(FreeSpans::new()),
        })
    }

    #[cfg(test)]
    /// The bytes the bump has handed out.
    pub(super) fn claimed_bytes(&self) -> usize {
        self.claimed.load(Ordering::Relaxed)
    }

    #[cfg(test)]
    /// The bytes of freed spans waiting for reuse.
    pub(super) fn free_span_bytes(&self) -> usize {
        self.spans.lock().unwrap().total()
    }

    /// Whether `p` lies in the range.
    #[inline]
    pub(super) fn contains(&self, p: *const u8) -> bool {
        (p as usize).wrapping_sub(self.base) < self.reserved.load(Ordering::Relaxed)
    }

    /// Whether `p` lies in a young block. The one question the collector, the
    /// frame-write check and the debug asserts ask of age. `p` must lie in the
    /// range: a heap object, never a literal (whose address word carries the
    /// literal bit) and never the system allocator's; a debug build panics on
    /// one, and a release build would read past the table. The caller's literal
    /// bit is the bounds check.
    #[inline]
    pub(crate) fn is_young(&self, p: *const u8) -> bool {
        self.table_byte(p) == YOUNG
    }

    /// Whether `p` lies in a block, young or old: for a debug check that the
    /// literal bit and the address agree.
    #[cfg(debug_assertions)]
    pub(super) fn in_block(&self, p: *const u8) -> bool {
        self.contains(p) && self.table_byte(p) != 0
    }

    #[inline]
    fn table_byte(&self, p: *const u8) -> u8 {
        debug_assert!(self.contains(p), "{p:p} is outside the heap range");
        let granule = (p as usize - self.base) >> GRANULE_SHIFT;
        unsafe { (*self.table.add(granule)).load(Ordering::Relaxed) }
    }

    /// The table byte a block of age `age` reads: `YOUNG` for a young block,
    /// and for an old one zero, or `OLD` in a debug build.
    fn mark(age: Age) -> u8 {
        match age {
            Age::Young => YOUNG,
            #[cfg(debug_assertions)]
            Age::Old => OLD,
            #[cfg(not(debug_assertions))]
            Age::Old => 0,
        }
    }

    /// Record that the pooled span at `p` is a block of age `age`, made just
    /// now. The span is whole granules owned by the caller, so no other thread
    /// reads or writes these table bytes, and they are all equal (a pooled
    /// span is one capacity for good), so the byte under the first granule
    /// says what all of them say: the span is written only when that is not
    /// the wanted mark. A block whose last life had the same age writes
    /// nothing.
    pub(super) fn made_pooled(&self, p: *mut u8, span: usize, age: Age) {
        self.debug_assert_one_mark(p, span);
        let wanted = Self::mark(age);
        if self.table_byte(p) != wanted {
            self.write(p, span, wanted);
        }
    }

    /// Record that the exact or huge span at `p` is a block of age `age`, made
    /// just now. Its table bytes are all zero (see `released_exact`), so only a
    /// young block, or a debug build's record of an old one, writes.
    pub(super) fn made_exact(&self, p: *mut u8, span: usize, age: Age) {
        self.debug_assert_one_mark(p, span);
        debug_assert_eq!(self.table_byte(p), 0, "a span from the span list is unmarked");
        let wanted = Self::mark(age);
        if wanted != 0 {
            self.write(p, span, wanted);
        }
    }

    /// Record that the block over the exact or huge span at `p` is released.
    /// The span goes back to the span list, which may split it or join it to a
    /// neighbour, so its table bytes are cleared (a young block's, and in a
    /// debug build an old block's record): the first granule says whether
    /// there is anything to clear.
    pub(super) fn released_exact(&self, p: *mut u8, span: usize) {
        if self.table_byte(p) != 0 {
            self.write(p, span, 0);
        }
    }

    /// Debug: every table byte under the span is the same as the first. This
    /// is what lets one byte decide for the whole of a pooled span, and what
    /// leaves the first granule's byte enough for an exact span.
    fn debug_assert_one_mark(&self, p: *mut u8, span: usize) {
        #[cfg(debug_assertions)]
        {
            debug_assert!(self.contains(p) && span.is_multiple_of(GRANULE));
            let first = (p as usize - self.base) >> GRANULE_SHIFT;
            let bytes =
                unsafe { std::slice::from_raw_parts(self.table.add(first) as *const u8, span >> GRANULE_SHIFT) };
            debug_assert!(
                bytes.iter().all(|&byte| byte == bytes[0]),
                "the table under the {span}-byte span at {p:p} is not one mark"
            );
        }
        #[cfg(not(debug_assertions))]
        let _ = (p, span);
    }

    fn write(&self, p: *mut u8, span: usize, byte: u8) {
        debug_assert!(self.contains(p) && span.is_multiple_of(GRANULE));
        debug_assert!((p as usize - self.base).is_multiple_of(GRANULE));
        #[cfg(test)]
        if byte == YOUNG || self.table_byte(p) == YOUNG {
            YOUNG_MARK_BYTES.with(|bytes| bytes.set(bytes.get() + (span >> GRANULE_SHIFT)));
        }
        let first = (p as usize - self.base) >> GRANULE_SHIFT;
        unsafe { write_bytes(self.table.add(first) as *mut u8, byte, span >> GRANULE_SHIFT) };
    }

    /// A fresh span of `span` bytes from the bump, growing the range when the
    /// bump reaches its end. It reads not young.
    pub(super) fn claim(&self, span: usize) -> *mut u8 {
        debug_assert!(span != 0 && span.is_multiple_of(GRANULE));
        let offset = loop {
            let reserved = self.reserved.load(Ordering::Acquire);
            let claimed = self
                .claimed
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |claimed| {
                    claimed.checked_add(span).filter(|&end| end <= reserved)
                });
            match claimed {
                Ok(offset) => break offset,
                Err(claimed) => self.grow(claimed.saturating_add(span)),
            }
        };
        self.commit_to(offset + span);
        (self.base + offset) as *mut u8
    }

    /// Reserve chunks, each at exactly the end of the last, until the range
    /// reaches `end` bytes from the base; the table grows with it. Another
    /// thread may have grown it already.
    fn grow(&self, end: usize) {
        let _guard = self.grow_lock.lock().unwrap();
        loop {
            let reserved = self.reserved.load(Ordering::Acquire);
            if reserved >= end {
                return;
            }
            let claimed = self.claimed.load(Ordering::Relaxed);
            self.reserve_next(self.base + reserved, self.chunk, "range", reserved, claimed);
            self.reserve_next(
                self.table as usize + (reserved >> GRANULE_SHIFT),
                self.chunk >> GRANULE_SHIFT,
                "table",
                reserved,
                claimed,
            );
            self.reserved.store(reserved + self.chunk, Ordering::Release);
        }
    }

    /// Reserve `bytes` at exactly `at`, or panic: the range is one run, and
    /// there is nowhere else to put the rest of it.
    fn reserve_next(&self, at: usize, bytes: usize, what: &str, reserved: usize, claimed: usize) {
        if let Err(error) = map_inaccessible(at, bytes, true) {
            panic!(
                "heap range cannot grow: {reserved} bytes reserved, {claimed} claimed;                  the next {bytes} bytes of the {what} belong at {at:#x}: {error}"
            );
        }
    }

    /// A span of `span` bytes for a block the pool does not recycle: a freed
    /// span when one is big enough, a fresh one otherwise.
    pub(super) fn take_span(&self, span: usize) -> *mut u8 {
        let reused = self.spans.lock().unwrap().take(span);
        match reused {
            Some(addr) => addr as *mut u8,
            None => self.claim(span),
        }
    }

    /// Take back a span of `span` bytes at `p`: its pages return to the
    /// operating system and the span joins the free spans.
    pub(super) fn give_span(&self, p: *mut u8, span: usize) {
        self.drop_pages(p, span);
        self.spans.lock().unwrap().give(p as usize, span);
    }

    /// Return the pages of the span at `p` to the operating system, and say how
    /// many there were. They read as zeros, and become resident again as they
    /// are touched.
    pub(super) fn drop_pages(&self, p: *mut u8, span: usize) -> usize {
        let Some((start, bytes)) = inner_pages(p as usize, span, self.page) else {
            return 0;
        };
        discard_pages(start, bytes);
        bytes / self.page
    }

    /// Make the range readable and writable up to `end` bytes from the base,
    /// and the table with it.
    fn commit_to(&self, end: usize) {
        if self.committed.load(Ordering::Acquire) >= end {
            return;
        }
        let _guard = self.commit_lock.lock().unwrap();
        let from = self.committed.load(Ordering::Acquire);
        if from >= end {
            return;
        }
        let to = end.next_multiple_of(COMMIT_CHUNK);
        make_accessible(self.base + from, to - from);
        make_accessible(
            self.table as usize + (from >> GRANULE_SHIFT),
            (to - from) >> GRANULE_SHIFT,
        );
        self.committed.store(to, Ordering::Release);
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        unsafe {
            let reserved = self.reserved.load(Ordering::Relaxed);
            libc::munmap(self.base as *mut libc::c_void, reserved);
            libc::munmap(self.table as *mut libc::c_void, reserved >> GRANULE_SHIFT);
        }
    }
}

#[cfg(test)]
thread_local! {
    /// How many table bytes this thread has written or cleared to make a block
    /// young or to take its youth away.
    static YOUNG_MARK_BYTES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The table bytes this thread has written or cleared for youth.
#[cfg(test)]
pub(super) fn young_mark_bytes() -> usize {
    YOUNG_MARK_BYTES.with(|bytes| bytes.get())
}

/// `bytes` of address space mapped with no access and no swap reserved, at
/// `hint` when it is free. With `exact` the mapping must be at `hint`: Linux
/// is told not to replace what is there, and any other system's answer is
/// checked, and unmapped when it is elsewhere.
fn map_inaccessible(hint: usize, bytes: usize, exact: bool) -> Result<usize, std::io::Error> {
    #[cfg(target_os = "linux")]
    let placement = if exact { libc::MAP_FIXED_NOREPLACE } else { 0 };
    #[cfg(not(target_os = "linux"))]
    let placement = 0;
    let p = unsafe {
        libc::mmap(
            hint as *mut libc::c_void,
            bytes,
            libc::PROT_NONE,
            libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE | placement,
            -1,
            0,
        )
    };
    if p == libc::MAP_FAILED {
        return Err(std::io::Error::last_os_error());
    }
    if exact && p as usize != hint {
        unsafe { libc::munmap(p, bytes) };
        return Err(std::io::Error::other(format!(
            "the system mapped it at {p:p}, not there"
        )));
    }
    Ok(p as usize)
}

fn make_accessible(addr: usize, bytes: usize) {
    let result = unsafe { libc::mprotect(addr as *mut libc::c_void, bytes, libc::PROT_READ | libc::PROT_WRITE) };
    assert_eq!(
        result,
        0,
        "heap range: the system refused to commit {bytes} bytes: {}",
        std::io::Error::last_os_error()
    );
}

/// The whole pages inside `[addr, addr + len)`.
fn inner_pages(addr: usize, len: usize, page: usize) -> Option<(usize, usize)> {
    let start = addr.next_multiple_of(page);
    let end = (addr + len) & !(page - 1);
    (end > start).then_some((start, end - start))
}

/// Give `bytes` of whole pages at `addr` back to the operating system so that
/// the process no longer holds them, and the next touch reads zeros.
///
/// Linux drops them with `MADV_DONTNEED`. macOS has no madvise that does: its
/// `MADV_FREE_REUSABLE` takes the pages out of the physical footprint but
/// leaves them in the resident size, and `MADV_FREE_REUSE` puts the whole span
/// back in the footprint again whether or not it is touched. So the pages are
/// replaced with fresh anonymous ones by mapping over them, which keeps the
/// range's one run unbroken.
#[cfg(any(target_os = "macos", target_os = "ios"))]
fn discard_pages(addr: usize, bytes: usize) {
    let p = unsafe {
        libc::mmap(
            addr as *mut libc::c_void,
            bytes,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_FIXED,
            -1,
            0,
        )
    };
    assert!(
        p != libc::MAP_FAILED,
        "heap range: replacing {bytes} bytes at {addr:#x} failed: {}",
        std::io::Error::last_os_error()
    );
}

#[cfg(not(any(target_os = "macos", target_os = "ios")))]
fn discard_pages(addr: usize, bytes: usize) {
    let result = unsafe { libc::madvise(addr as *mut libc::c_void, bytes, libc::MADV_DONTNEED) };
    assert_eq!(
        result,
        0,
        "heap range: madvise failed: {}",
        std::io::Error::last_os_error()
    );
}

/// The freed spans of blocks the pool does not recycle, by address, so that a
/// span freed beside another rejoins it.
struct FreeSpans {
    by_addr: BTreeMap<usize, usize>,
}

impl FreeSpans {
    const fn new() -> Self {
        Self {
            by_addr: BTreeMap::new(),
        }
    }

    #[cfg(test)]
    fn total(&self) -> usize {
        self.by_addr.values().sum()
    }

    /// The start of `span` bytes cut from the smallest free span that holds
    /// them, lowest address first among equals; the rest stays free.
    fn take(&mut self, span: usize) -> Option<usize> {
        let (&addr, &len) = self
            .by_addr
            .iter()
            .filter(|&(_, &len)| len >= span)
            .min_by_key(|&(&addr, &len)| (len, addr))?;
        self.by_addr.remove(&addr);
        if len > span {
            self.by_addr.insert(addr + span, len - span);
        }
        Some(addr)
    }

    /// Add the span `[addr, addr + len)`, joined to the free spans on either
    /// side of it.
    fn give(&mut self, addr: usize, len: usize) {
        let mut start = addr;
        let mut end = addr + len;
        if let Some((&before, &before_len)) = self.by_addr.range(..addr).next_back()
            && before + before_len == addr
        {
            self.by_addr.remove(&before);
            start = before;
        }
        if let Some(after_len) = self.by_addr.remove(&end) {
            end += after_len;
        }
        self.by_addr.insert(start, end - start);
    }
}

#[cfg(test)]
#[path = "arena_test.rs"]
mod arena_test;
