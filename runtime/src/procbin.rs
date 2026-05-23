//! fz-q8d.1 — sealed procbin / off-heap binary abstraction.
//!
//! This module owns the entire off-heap binary story:
//!
//!   * `SharedBin` — refcounted byte buffer carrying its own destructor
//!     pointer. The destructor is a permanent property set at allocation
//!     time. Heap-allocated bins use `shared_bin_destructor_heap`; future
//!     compiler-baked static bins (fz-q8d.2) use `shared_bin_destructor_noop`.
//!   * `SharedBinHandle` — Arc-shaped owning wrapper. `Drop` releases.
//!   * `ProcBin` — `#[repr(transparent)]` newtype over the per-heap
//!     `HeapHeader*` stub. All offset arithmetic for ProcBin payload lives
//!     here; outside this module no code reads ProcBin layout directly.
//!   * `alloc_procbin` — safe constructor. Consumes a `SharedBinHandle`
//!     (refcount ownership transfers in), pushes the new ProcBin onto the
//!     heap's intrusive MSO chain via the `mso_next` link inside the
//!     ProcBin payload.
//!   * MSO sweep + drop — post-Cheney sweep walks `Heap::mso_head` chain,
//!     rewriting survivors to their to-space copy and releasing dead
//!     entries' shared_ptrs. `Heap::drop` releases the whole chain.
//!
//! Refcount ordering uses the canonical `Arc` pattern (Relaxed on retain,
//! Release on release, Acquire fence on final drop). Loom verification
//! lands in fz-q8d.3 via the `crate::sync` abstraction module.

use crate::fz_value::{HeapHeader, HeapKind, TAG_BITSTRING, TAG_FWD, TAG_MASK, TAG_PROCBIN};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::ptr::NonNull;

// ===== SharedBin layout =====================================================

/// Off-heap refcounted binary. `refcount` controls lifetime; `destructor` is
/// invoked exactly once when the refcount transitions to zero, with the
/// SharedBin pointer as its argument.
#[repr(C)]
pub struct SharedBin {
    pub refcount: AtomicUsize,                            // offset 0..8
    pub bit_len: u64,                                     // offset 8..16
    pub bytes_ptr: *const u8,                             // offset 16..24
    pub bytes_len: usize,                                 // offset 24..32
    pub destructor: unsafe extern "C" fn(*mut SharedBin), // offset 32..40
}

const _: () = {
    assert!(std::mem::size_of::<SharedBin>() == 40);
};

// Safety: refcount is atomic; the byte buffer is either an owned Box<[u8]>
// (heap destructor reclaims) or a static `.rodata` payload (noop dtor).
unsafe impl Send for SharedBin {}
unsafe impl Sync for SharedBin {}

// ===== Destructors ==========================================================

/// Final-release destructor for heap-allocated SharedBins. Reconstructs
/// both the bytes box and the SharedBin box and drops them in turn.
///
/// # Safety
/// `p` must point at a SharedBin allocated via `shared_bin_alloc` and the
/// caller must be the last live reference (refcount transition 1 → 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared_bin_destructor_heap(p: *mut SharedBin) {
    let bin = unsafe { Box::from_raw(p) };
    // The buffer was overallocated by 1 for the invisible trailing NUL
    // ([[fz-wu9]]). Free the full allocation.
    let bytes = unsafe {
        Box::from_raw(std::ptr::slice_from_raw_parts_mut(
            bin.bytes_ptr as *mut u8,
            bin.bytes_len + 1,
        ))
    };
    drop(bytes);
    drop(bin);
    // The LIVE_COUNT gauge is a production debug counter; loom doesn't
    // model it (and shouldn't — it's incidental to the ordering claims
    // we're trying to verify). Skip the update under cfg(loom).
    #[cfg(not(loom))]
    LIVE_COUNT.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
}

/// No-op destructor for compiler-baked static SharedBins (fz-q8d.2). The
/// bytes and the struct itself live in the program binary's `.data`
/// section; this destructor is reachable in principle but in practice
/// never fires because the static refcount is anchored at 1.
///
/// # Safety
/// `_p` is unused; signature matches the `destructor` field type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared_bin_destructor_noop(_p: *mut SharedBin) {}

// ===== Allocation + refcount primitives =====================================

/// Allocate a fresh heap-backed SharedBin with refcount = 1 and the heap
/// destructor installed. Bytes are leaked separately as a `Box<[u8]>` so
/// the destructor can reconstruct both boxes independently.
pub fn shared_bin_alloc(bytes: &[u8], bit_len: u64) -> *mut SharedBin {
    // fz-wu9 — overallocate one byte beyond bytes_len and zero it.
    // The trailing NUL is invisible to the language (bytes_len/bit_len
    // unchanged) and underwrites the cstring extern marshal contract.
    let bytes_len = bytes.len();
    let mut v: Vec<u8> = Vec::with_capacity(bytes_len + 1);
    v.extend_from_slice(bytes);
    v.push(0);
    debug_assert_eq!(v.len(), bytes_len + 1);
    let buf: Box<[u8]> = v.into_boxed_slice();
    let bytes_ptr: *const u8 = Box::leak(buf).as_ptr();
    let bin = Box::new(SharedBin {
        refcount: AtomicUsize::new(1),
        bit_len,
        bytes_ptr,
        bytes_len,
        destructor: shared_bin_destructor_heap,
    });
    LIVE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    Box::into_raw(bin)
}

/// Increment the refcount on an already-owned SharedBin.
///
/// # Safety
/// `p` must point at a live SharedBin (refcount > 0).
pub unsafe fn shared_bin_retain(p: *mut SharedBin) {
    debug_assert!(!p.is_null());
    let bin = unsafe { &*p };
    let old = bin.refcount.fetch_add(1, Ordering::Relaxed);
    debug_assert!(old < usize::MAX / 2, "SharedBin refcount overflow");
}

/// Decrement the refcount and run the destructor if this was the last
/// reference. Release ordering publishes prior writes; the Acquire fence
/// on final drop synchronises with every other releaser.
///
/// # Safety
/// `p` must point at a live SharedBin. After calling, the caller must not
/// dereference `p` again.
pub unsafe fn shared_bin_release(p: *mut SharedBin) {
    debug_assert!(!p.is_null());
    let bin = unsafe { &*p };
    if bin.refcount.fetch_sub(1, Ordering::Release) == 1 {
        fence(Ordering::Acquire);
        unsafe {
            (bin.destructor)(p);
        }
    }
}

// ===== Live-count gauge =====================================================
//
// Tracks heap-allocated SharedBin objects. Heap destructor decrements;
// static SharedBins from fz-q8d.2 will not touch it (their dtor is noop).
// `pub(crate)` so tests inside the crate can baseline-delta against it.

// LIVE_COUNT is always a std atomic — not part of the ordering claim
// the loom test verifies. Use std types directly so cfg(loom) builds
// don't accidentally pull this gauge into the model.
static LIVE_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Number of currently-live heap-allocated SharedBin objects.
#[cfg(test)]
pub(crate) fn live_count() -> usize {
    LIVE_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}

// ===== SharedBinHandle ======================================================

/// Owning handle to a SharedBin. `Drop` releases. `Clone` retains.
pub struct SharedBinHandle(NonNull<SharedBin>);

impl SharedBinHandle {
    /// Allocate a new heap-backed SharedBin and wrap the initial refcount.
    pub fn from_bytes(bytes: &[u8], bit_len: u64) -> Self {
        let p = shared_bin_alloc(bytes, bit_len);
        Self(NonNull::new(p).expect("shared_bin_alloc returned null"))
    }

    /// Retain `p` and wrap the new reference.
    ///
    /// # Safety
    /// `p` must point at a live SharedBin.
    pub unsafe fn retain_from_raw(p: *mut SharedBin) -> Self {
        unsafe { shared_bin_retain(p) };
        Self(NonNull::new(p).expect("retain_from_raw: null ptr"))
    }

    /// Wrap `p` without retaining. Caller transfers their existing
    /// refcount edge to the handle.
    ///
    /// # Safety
    /// `p` must point at a live SharedBin; caller must own exactly one
    /// refcount edge that they relinquish to the handle.
    pub unsafe fn from_raw_already_retained(p: *mut SharedBin) -> Self {
        Self(NonNull::new(p).expect("from_raw_already_retained: null ptr"))
    }

    pub fn as_raw(&self) -> *mut SharedBin {
        self.0.as_ptr()
    }

    /// Consume the handle without releasing. The caller now owns one
    /// refcount edge represented by the returned pointer.
    pub fn into_raw(self) -> *mut SharedBin {
        let p = self.0.as_ptr();
        std::mem::forget(self);
        p
    }

    pub fn bit_len(&self) -> u64 {
        unsafe { (*self.as_raw()).bit_len }
    }
    pub fn bytes_ptr(&self) -> *const u8 {
        unsafe { (*self.as_raw()).bytes_ptr }
    }
    pub fn bytes_len(&self) -> usize {
        unsafe { (*self.as_raw()).bytes_len }
    }
}

impl Clone for SharedBinHandle {
    fn clone(&self) -> Self {
        unsafe { Self::retain_from_raw(self.as_raw()) }
    }
}

impl Drop for SharedBinHandle {
    fn drop(&mut self) {
        unsafe { shared_bin_release(self.as_raw()) };
    }
}

// ===== ProcBin newtype ======================================================

/// Per-heap stub referencing a `SharedBin`. 16 bytes total:
///   offset 0..8   shared_ptr: *mut SharedBin
///   offset 8..16  mso_next:   *mut HeapHeader   (intrusive MSO link)
///
/// Cheney forwarding overwrites offset 0 with a headerless forwarding marker.
/// Offset 8 is preserved in from-space, so MSO sweep reads `mso_next` from the
/// old stub and `shared_ptr` from the to-space copy if the stub survived.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ProcBin(NonNull<HeapHeader>);

impl ProcBin {
    /// # Safety
    /// `p` must point at a live strict ProcBin object.
    pub unsafe fn from_raw(p: *mut HeapHeader) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("ProcBin::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut HeapHeader {
        self.0.as_ptr()
    }

    pub fn shared_raw(&self) -> *mut SharedBin {
        unsafe { std::ptr::read(self.as_raw() as *const *mut SharedBin) }
    }

    fn shared_raw_set(&self, p: *mut SharedBin) {
        unsafe {
            std::ptr::write(self.as_raw() as *mut *mut SharedBin, p);
        }
    }

    pub fn mso_next(&self) -> *mut HeapHeader {
        unsafe { std::ptr::read((self.as_raw() as *const u8).add(8) as *const *mut HeapHeader) }
    }

    pub(crate) fn mso_next_set(&self, next: *mut HeapHeader) {
        unsafe {
            std::ptr::write(
                (self.as_raw() as *mut u8).add(8) as *mut *mut HeapHeader,
                next,
            );
        }
    }

    pub fn bit_len(&self) -> u64 {
        unsafe { (*self.shared_raw()).bit_len }
    }

    pub fn bytes_ptr(&self) -> *const u8 {
        unsafe { (*self.shared_raw()).bytes_ptr }
    }

    pub fn bytes_len(&self) -> usize {
        unsafe { (*self.shared_raw()).bytes_len }
    }
}

// ===== Allocation on a per-process heap =====================================

use crate::heap::Heap;

/// Allocate a 16-byte ProcBin stub on `heap`, taking ownership of the
/// SharedBin reference encapsulated in `handle`. The new ProcBin is
/// pushed onto `heap.mso_head` as the new chain head.
pub fn alloc_procbin(heap: &mut Heap, handle: SharedBinHandle) -> ProcBin {
    let p = heap.alloc(16);
    let pb = unsafe { ProcBin::from_raw(p) };
    pb.shared_raw_set(handle.into_raw());
    pb.mso_next_set(heap.mso_head);
    heap.mso_head = p;
    pb
}

// ===== MSO sweep + drop =====================================================

/// Walk `heap.mso_head` after Cheney BFS completes. Strict ProcBin/Resource
/// survivors carry a headerless forwarding marker at offset 0, so their
/// off-heap pointer must be read from the to-space copy.
pub fn mso_sweep(heap: &mut Heap) {
    use crate::resource::{ResourceStub, fz_resource_release};
    let mut new_head: *mut HeapHeader = std::ptr::null_mut();
    let mut cur = heap.mso_head;
    while !cur.is_null() {
        let first = unsafe { std::ptr::read(cur as *const u64) };
        if first & TAG_MASK == TAG_FWD {
            let to_p = (first & !TAG_MASK) as *mut HeapHeader;
            let next = if strict_resource_magic(cur) {
                resource_mso_next(cur)
            } else {
                procbin_mso_next(cur)
            };
            if strict_resource_magic(cur) {
                unsafe { ResourceStub::from_raw(to_p).mso_next_set(new_head) };
            } else {
                unsafe { ProcBin::from_raw(to_p).mso_next_set(new_head) };
            }
            new_head = to_p;
            cur = next;
            continue;
        }

        let kind = unsafe { (*cur).kind };
        if kind == crate::heap::FORWARDED_KIND {
            let (next, _) = mso_read_next_headered(cur, kind);
            let to_p = unsafe { std::ptr::read((cur as *const u8).add(8) as *const u64) }
                as *mut HeapHeader;
            // The from-header's original kind is gone (overwritten by
            // FORWARDED_KIND in slot 0..2 plus the to-ptr in slot 8..16).
            // The to-space copy's kind tells us which accessor to call
            // for mso_next_set.
            let to_kind = unsafe { (*to_p).kind };
            mso_set_next_headered(to_p, to_kind, new_head);
            new_head = to_p;
            cur = next;
        } else {
            match headered_mso_kind(cur, kind) {
                Some(HeapKind::ProcBin) => {
                    let (next, _) = mso_read_next_headered(cur, kind);
                    unsafe { shared_bin_release(legacy_procbin_shared(cur)) };
                    cur = next;
                }
                Some(HeapKind::Resource) => {
                    let (next, _) = mso_read_next_headered(cur, kind);
                    let rs = unsafe { ResourceStub::from_raw(cur) };
                    unsafe { fz_resource_release(rs.shared_raw()) };
                    cur = next;
                }
                _ => {
                    if strict_resource_magic(cur) {
                        let next = resource_mso_next(cur);
                        unsafe { fz_resource_release(strict_resource_shared(cur)) };
                        cur = next;
                        continue;
                    }
                    let next = procbin_mso_next(cur);
                    unsafe { shared_bin_release(strict_procbin_shared(cur)) };
                    cur = next;
                }
            }
        }
    }
    heap.mso_head = new_head;
}

/// fz-4mk — deferred variant of `mso_drop_all`. Walks the MSO chain at
/// process shutdown and, for each dead resource, instead of invoking the
/// stored C destructor inline, snapshots the closure value and payload
/// onto `heap.pending_dtors` so the scheduler can dispatch the dtor as
/// real fz code while the process is still alive. ProcBin entries
/// continue to release synchronously (their dtor is owned by the runtime,
/// not user fz code, and has nothing to print or branch on).
///
/// Currently called only by the interpreter leg's shutdown path; the
/// JIT/AOT scheduler loops still use the inline `mso_drop_all` until
/// phase 3 wires their drain. After this returns, the MSO chain is
/// empty and `Heap::drop` -> `mso_drop_all` is a no-op.
pub fn mso_drop_all_deferred(heap: &mut Heap) {
    use crate::resource::{ResourceStub, fz_resource_release_deferred};
    let mut cur = heap.mso_head;
    while !cur.is_null() {
        let kind = unsafe { (*cur).kind };
        match headered_mso_kind(cur, kind) {
            Some(HeapKind::ProcBin) => {
                let (next, _) = mso_read_next_headered(cur, kind);
                unsafe { shared_bin_release(legacy_procbin_shared(cur)) };
                cur = next;
            }
            Some(HeapKind::Resource) => {
                let (next, _) = mso_read_next_headered(cur, kind);
                let rs = unsafe { ResourceStub::from_raw(cur) };
                let closure = rs.closure_ptr();
                if let Some(payload) = unsafe { fz_resource_release_deferred(rs.shared_raw()) } {
                    heap.pending_dtors.push_back((closure.0, payload));
                }
                cur = next;
            }
            _ => {
                if strict_resource_magic(cur) {
                    let next = resource_mso_next(cur);
                    let rs = unsafe { ResourceStub::from_raw(cur) };
                    let closure = rs.closure_ptr();
                    if let Some(payload) = unsafe { fz_resource_release_deferred(rs.shared_raw()) }
                    {
                        heap.pending_dtors.push_back((closure.0, payload));
                    }
                    cur = next;
                    continue;
                }
                let next = procbin_mso_next(cur);
                unsafe { shared_bin_release(strict_procbin_shared(cur)) };
                cur = next;
            }
        }
    }
    heap.mso_head = std::ptr::null_mut();
}

/// Read the `mso_next` link from a legacy headered MSO chain entry.
/// `FORWARDED_KIND` headers keep the original chain link at the same offset
/// the from-header used; we follow whichever offset the original size dictated.
///
/// Returns the next link and the *byte size of the entry* (so the caller
/// has a one-stop shape lookup if it later wants to scrub or step).
fn mso_read_next_headered(p: *mut HeapHeader, kind: u16) -> (*mut HeapHeader, usize) {
    // The from-header has been clobbered with FORWARDED_KIND in low bits,
    // but the original size_bytes lives further into the header at +4
    // (untouched by forwarding). We use it to pick the offset.
    let size = unsafe { (*p).size_bytes } as usize;
    let off = match size {
        32 => 24, // legacy ProcBin
        40 => 32, // Resource (fz-4mk)
        other => panic!(
            "mso_read_next: unexpected MSO entry size {}, kind {}",
            other, kind
        ),
    };
    let next = unsafe { std::ptr::read((p as *const u8).add(off) as *const *mut HeapHeader) };
    (next, size)
}

fn mso_set_next_headered(p: *mut HeapHeader, _kind: u16, next: *mut HeapHeader) {
    let size = unsafe { (*p).size_bytes } as usize;
    let off = match size {
        32 => 24,
        40 => 32,
        other => panic!("mso_set_next: unexpected MSO entry size {}", other),
    };
    unsafe {
        std::ptr::write((p as *mut u8).add(off) as *mut *mut HeapHeader, next);
    }
}

fn procbin_mso_next(p: *mut HeapHeader) -> *mut HeapHeader {
    unsafe { std::ptr::read((p as *const u8).add(8) as *const *mut HeapHeader) }
}

fn resource_mso_next(p: *mut HeapHeader) -> *mut HeapHeader {
    unsafe { std::ptr::read((p as *const u8).add(24) as *const *mut HeapHeader) }
}

fn strict_procbin_shared(p: *mut HeapHeader) -> *mut SharedBin {
    unsafe { std::ptr::read(p as *const *mut SharedBin) }
}

fn strict_resource_shared(p: *mut HeapHeader) -> *mut crate::resource::Resource {
    unsafe { std::ptr::read(p as *const *mut crate::resource::Resource) }
}

fn legacy_procbin_shared(p: *mut HeapHeader) -> *mut SharedBin {
    unsafe { std::ptr::read((p as *const u8).add(16) as *const *mut SharedBin) }
}

fn strict_resource_magic(p: *mut HeapHeader) -> bool {
    let magic = unsafe { std::ptr::read((p as *const u8).add(8) as *const u64) };
    magic == crate::resource::RESOURCE_STUB_MAGIC
}

fn headered_mso_kind(p: *mut HeapHeader, kind: u16) -> Option<HeapKind> {
    let size = unsafe { (*p).size_bytes };
    match (HeapKind::from_u16(kind), size) {
        (Some(HeapKind::ProcBin), 32) => Some(HeapKind::ProcBin),
        (Some(HeapKind::Resource), 40) => Some(HeapKind::Resource),
        _ => None,
    }
}

/// Drop every ProcBin in `heap.mso_head`'s chain, releasing each
/// SharedBin reference. Called from `Heap::drop` before pool reclaim.
pub fn mso_drop_all(heap: &mut Heap) {
    use crate::resource::{ResourceStub, fz_resource_release};
    let mut cur = heap.mso_head;
    while !cur.is_null() {
        let kind = unsafe { (*cur).kind };
        match headered_mso_kind(cur, kind) {
            Some(HeapKind::ProcBin) => {
                let (next, _) = mso_read_next_headered(cur, kind);
                unsafe { shared_bin_release(legacy_procbin_shared(cur)) };
                cur = next;
            }
            Some(HeapKind::Resource) => {
                let (next, _) = mso_read_next_headered(cur, kind);
                let rs = unsafe { ResourceStub::from_raw(cur) };
                unsafe { fz_resource_release(rs.shared_raw()) };
                cur = next;
            }
            _ => {
                if strict_resource_magic(cur) {
                    let next = resource_mso_next(cur);
                    let rs = unsafe { ResourceStub::from_raw(cur) };
                    unsafe { fz_resource_release(rs.shared_raw()) };
                    cur = next;
                    continue;
                }
                let next = procbin_mso_next(cur);
                unsafe { shared_bin_release(strict_procbin_shared(cur)) };
                cur = next;
            }
        }
    }
    heap.mso_head = std::ptr::null_mut();
}

// ===== Bitstring dispatch helpers (moved from fz_value.rs) ==================
//
// fz bitstrings live in one of two storage modes:
//   * `TAG_BITSTRING` — inline payload: bit_len at +0, bytes at +8.
//   * `TAG_PROCBIN` — *mut SharedBin at +0; bytes + bit_len off-heap.

/// True if `p` is a heap value whose bytes can be read as a bitstring.
///
/// # Safety
/// `p` must be a live heap header.
pub unsafe fn is_bitstring_like(p: *const HeapHeader) -> bool {
    if (p as u64) & TAG_MASK == TAG_BITSTRING {
        return true;
    }
    if (p as u64) & TAG_MASK == TAG_PROCBIN {
        return true;
    }
    let kind = unsafe { (*p).kind };
    matches!(
        HeapKind::from_u16(kind),
        Some(HeapKind::Bitstring) | Some(HeapKind::ProcBin)
    )
}

/// Bit length of a bitstring-like heap value.
///
/// # Safety
/// `p` must be a live heap header whose kind is Bitstring or ProcBin.
pub unsafe fn bitstring_bit_len(p: *const HeapHeader) -> u64 {
    if (p as u64) & TAG_MASK == TAG_PROCBIN {
        let p = ((p as u64) & !TAG_MASK) as *mut HeapHeader;
        let pb = unsafe { ProcBin::from_raw(p) };
        return pb.bit_len();
    }
    let p = ((p as u64) & !TAG_MASK) as *const HeapHeader;
    let kind = unsafe { (*p).kind };
    match HeapKind::from_u16(kind) {
        Some(HeapKind::Bitstring) => unsafe { crate::fz_value::bitstring_bit_len(p as *const u8) },
        Some(HeapKind::ProcBin) => {
            let pb = unsafe { ProcBin::from_raw(p as *mut HeapHeader) };
            pb.bit_len()
        }
        _ => unsafe { crate::fz_value::bitstring_bit_len(p as *const u8) },
    }
}

/// Byte pointer to the underlying bitstring payload.
///
/// # Safety
/// `p` must be a live heap header whose kind is Bitstring or ProcBin.
pub unsafe fn bitstring_byte_ptr(p: *const HeapHeader) -> *const u8 {
    if (p as u64) & TAG_MASK == TAG_PROCBIN {
        let p = ((p as u64) & !TAG_MASK) as *mut HeapHeader;
        let pb = unsafe { ProcBin::from_raw(p) };
        return pb.bytes_ptr();
    }
    let p = ((p as u64) & !TAG_MASK) as *const HeapHeader;
    let kind = unsafe { (*p).kind };
    match HeapKind::from_u16(kind) {
        Some(HeapKind::Bitstring) => unsafe {
            crate::fz_value::bitstring_bytes_ptr(p as *const u8)
        },
        Some(HeapKind::ProcBin) => {
            let pb = unsafe { ProcBin::from_raw(p as *mut HeapHeader) };
            pb.bytes_ptr()
        }
        _ => unsafe { crate::fz_value::bitstring_bytes_ptr(p as *const u8) },
    }
}

// ===== Tests ================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    use std::thread;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    /// RAII guard: snapshots `live_count()` on construction; Drop asserts
    /// the count returned to baseline. Use in scopes where every bin
    /// allocated must also be freed before the guard goes out of scope.
    pub(crate) struct LiveCountGuard {
        baseline: usize,
    }
    impl LiveCountGuard {
        pub(crate) fn snap() -> Self {
            Self {
                baseline: live_count(),
            }
        }
        pub(crate) fn baseline(&self) -> usize {
            self.baseline
        }
    }
    impl Drop for LiveCountGuard {
        fn drop(&mut self) {
            assert_eq!(
                live_count(),
                self.baseline,
                "LiveCountGuard: live_count did not return to baseline"
            );
        }
    }

    #[test]
    #[serial_test::serial]
    fn alloc_retain_release_free_pattern() {
        let g = LiveCountGuard::snap();
        let p = shared_bin_alloc(&[1, 2, 3, 4], 32);
        assert_eq!(live_count(), g.baseline() + 1);
        unsafe {
            shared_bin_retain(p);
            shared_bin_retain(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
            shared_bin_release(p);
            shared_bin_release(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
            shared_bin_release(p);
        }
    }

    #[test]
    #[serial_test::serial]
    fn alloc_release_immediately_frees() {
        let _g = LiveCountGuard::snap();
        let p = shared_bin_alloc(b"hello", 40);
        unsafe { shared_bin_release(p) };
    }

    #[test]
    #[serial_test::serial]
    fn bytes_preserved_across_retain_release() {
        let _g = LiveCountGuard::snap();
        let p = shared_bin_alloc(&[0xde, 0xad, 0xbe, 0xef], 32);
        unsafe {
            shared_bin_retain(p);
            let len = (*p).bytes_len;
            let payload = std::slice::from_raw_parts((*p).bytes_ptr, len);
            assert_eq!(payload, &[0xde, 0xad, 0xbe, 0xef][..]);
            assert_eq!((*p).bit_len, 32);
            shared_bin_release(p);
            let payload = std::slice::from_raw_parts((*p).bytes_ptr, len);
            assert_eq!(payload, &[0xde, 0xad, 0xbe, 0xef][..]);
            shared_bin_release(p);
        }
    }

    #[test]
    #[serial_test::serial]
    fn concurrent_retain_release_is_consistent() {
        let _g = LiveCountGuard::snap();
        let p = shared_bin_alloc(&[7; 64], 512);
        let p_addr = p as usize;
        let start = Arc::new(AtomicBool::new(false));
        let mut handles = Vec::new();
        for _ in 0..2 {
            let start = start.clone();
            handles.push(thread::spawn(move || {
                while !start.load(Ordering::Acquire) {
                    std::hint::spin_loop();
                }
                let p = p_addr as *mut SharedBin;
                for _ in 0..100 {
                    unsafe {
                        shared_bin_retain(p);
                        shared_bin_release(p);
                    }
                }
            }));
        }
        start.store(true, Ordering::Release);
        for h in handles {
            h.join().unwrap();
        }
        unsafe {
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
            shared_bin_release(p);
        }
    }

    /// fz-wu9 — every heap-allocated SharedBin's buffer has a trailing
    /// zero byte at offset `bytes_len` (not counted toward bytes_len /
    /// bit_len). Underwrites the cstring extern marshal contract.
    #[test]
    #[serial_test::serial]
    fn shared_bin_alloc_has_trailing_nul() {
        let _g = LiveCountGuard::snap();
        // Non-empty payload.
        let p = shared_bin_alloc(b"hello", 40);
        unsafe {
            assert_eq!((*p).bytes_len, 5);
            assert_eq!(*(*p).bytes_ptr.add(5), 0, "trailing NUL after 'hello'");
            shared_bin_release(p);
        }
        // Empty payload — still gets a trailing zero at offset 0.
        let p = shared_bin_alloc(b"", 0);
        unsafe {
            assert_eq!((*p).bytes_len, 0);
            assert_eq!(*(*p).bytes_ptr, 0, "trailing NUL on empty payload");
            shared_bin_release(p);
        }
        // Payload containing internal zeros (rare but legal).
        let p = shared_bin_alloc(&[1u8, 0, 2, 0, 3], 40);
        unsafe {
            assert_eq!((*p).bytes_len, 5);
            assert_eq!(
                *(*p).bytes_ptr.add(5),
                0,
                "trailing NUL after embedded-zero payload"
            );
            shared_bin_release(p);
        }
    }

    /// Heap-allocated bin's destructor field equals `shared_bin_destructor_heap`.
    #[test]
    #[serial_test::serial]
    fn alloc_installs_heap_destructor() {
        let _g = LiveCountGuard::snap();
        let p = shared_bin_alloc(&[0u8; 4], 32);
        unsafe {
            let d = (*p).destructor as *const () as usize;
            let want = shared_bin_destructor_heap as *const () as usize;
            assert_eq!(d, want);
            shared_bin_release(p);
        }
    }

    /// Construct a SharedBin manually with a test destructor that flips
    /// an AtomicBool; retain/release exactly to zero fires it once.
    #[test]
    #[serial_test::serial]
    fn custom_destructor_fires_exactly_once() {
        static FIRED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        unsafe extern "C" fn test_dtor(_p: *mut SharedBin) {
            FIRED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        FIRED.store(0, std::sync::atomic::Ordering::Relaxed);
        // Allocate bytes + bin without entering shared_bin_alloc (so the
        // global LIVE_COUNT isn't touched and the test destructor isn't
        // shared_bin_destructor_heap). We leak both — test_dtor is a no-op.
        let bytes: Box<[u8]> = vec![0u8; 4].into_boxed_slice();
        let bytes_len = bytes.len();
        let bytes_ptr = Box::leak(bytes).as_ptr();
        let bin = Box::new(SharedBin {
            refcount: AtomicUsize::new(1),
            bit_len: 32,
            bytes_ptr,
            bytes_len,
            destructor: test_dtor,
        });
        let p = Box::into_raw(bin);
        unsafe {
            shared_bin_retain(p);
            shared_bin_release(p);
            assert_eq!(
                FIRED.load(std::sync::atomic::Ordering::Relaxed),
                0,
                "still has 1 ref"
            );
            shared_bin_release(p);
        }
        assert_eq!(
            FIRED.load(std::sync::atomic::Ordering::Relaxed),
            1,
            "fired exactly once"
        );
        // Reclaim manually so we don't actually leak. test_dtor was a noop.
        unsafe {
            let _ = Box::from_raw(p);
            let _ = Box::from_raw(std::slice::from_raw_parts_mut(
                bytes_ptr as *mut u8,
                bytes_len,
            ));
        }
    }

    /// SharedBinHandle Drop releases.
    #[test]
    #[serial_test::serial]
    fn handle_drop_releases() {
        let g = LiveCountGuard::snap();
        {
            let _h = SharedBinHandle::from_bytes(&[1, 2, 3], 24);
            assert_eq!(live_count(), g.baseline() + 1);
        }
    }

    /// SharedBinHandle Clone retains; the destructor fires exactly when
    /// the second Drop runs.
    #[test]
    #[serial_test::serial]
    fn handle_clone_retains_then_balanced_drops_free() {
        let g = LiveCountGuard::snap();
        let h = SharedBinHandle::from_bytes(&[0xab, 0xcd], 16);
        let p = h.as_raw();
        let h2 = h.clone();
        unsafe {
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 2);
        }
        drop(h);
        unsafe {
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
        }
        drop(h2);
        assert_eq!(live_count(), g.baseline());
    }

    /// alloc_procbin pushes onto MSO chain; Heap::drop releases SharedBin.
    #[test]
    #[serial_test::serial]
    fn alloc_procbin_pushes_into_mso_chain() {
        let g = LiveCountGuard::snap();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let handle = SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32);
            let pb = alloc_procbin(&mut h, handle);
            let tagged = crate::fz_value::tagged_procbin_bits(pb.as_raw() as *const u8);
            assert_eq!(tagged & TAG_MASK, TAG_PROCBIN);
            assert_eq!(crate::fz_value::object_size(tagged), 16);
            assert_eq!(h.mso_head, pb.as_raw());
            assert_eq!(pb.mso_next(), std::ptr::null_mut());
            assert_eq!(live_count(), g.baseline() + 1);
        }
    }

    /// Three ProcBins on one heap: intrusive chain links latest → earlier.
    #[test]
    #[serial_test::serial]
    fn mso_chain_threads_through_procbins() {
        let _g = LiveCountGuard::snap();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let pb1 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1], 8));
        let pb2 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[2], 8));
        let pb3 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3], 8));
        assert_eq!(h.mso_head, pb3.as_raw());
        assert_eq!(pb3.mso_next(), pb2.as_raw());
        assert_eq!(pb2.mso_next(), pb1.as_raw());
        assert_eq!(pb1.mso_next(), std::ptr::null_mut());
    }

    /// Heap::drop releases every chain entry.
    #[test]
    #[serial_test::serial]
    fn heap_drop_releases_all_chain_entries() {
        let g = LiveCountGuard::snap();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2], 16));
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[3, 4, 5], 24));
            assert_eq!(live_count(), g.baseline() + 2);
        }
    }
}

// ===== fz-q8d.3 — loom verification of retain/release ordering ==============
//
// Enabled only under `RUSTFLAGS="--cfg loom"`. The two-thread model
// constructs a SharedBin manually (so LIVE_COUNT isn't exercised — that
// gauge is not part of the ordering claim), spawns two children that
// each retain+release, then the "main" thread performs the final
// release. Across every legal interleaving loom can produce, the test
// destructor must fire exactly once.
//
// Run: `RUSTFLAGS="--cfg loom" cargo test --release -p fz-runtime loom_`.
// See `runtime/RUNNING_LOOM.md`.

#[cfg(all(test, loom))]
mod loom_tests {
    use super::*;
    use loom::sync::Arc;
    use loom::sync::atomic::{AtomicBool, Ordering as LoomOrdering};

    // Destructor for the loom test sets a flag on a loom-instrumented
    // `AtomicBool` handed out via the thread-local `LOOM_FLAG` slot. The
    // model asserts the destructor fires exactly once per iteration.
    loom::thread_local! {
        static LOOM_FLAG: std::cell::RefCell<Option<Arc<AtomicBool>>> =
            std::cell::RefCell::new(None);
    }

    unsafe extern "C" fn loom_dtor(_p: *mut SharedBin) {
        LOOM_FLAG.with(|c| {
            let flag = c.borrow();
            let f = flag.as_ref().expect("LOOM_FLAG not installed");
            // Use SeqCst so loom treats the destructor invocation as a
            // single, observable event in the model.
            let prev = f.swap(true, LoomOrdering::SeqCst);
            assert!(!prev, "destructor fired more than once");
        });
    }

    fn install_loom_flag(flag: Arc<AtomicBool>) {
        LOOM_FLAG.with(|c| *c.borrow_mut() = Some(flag));
    }

    /// Build a SharedBin manually with `loom_dtor` installed and
    /// `refcount = 1`. Returns the raw pointer. The byte buffer is a
    /// constant we never free — loom_dtor doesn't reclaim it; the bin
    /// itself is also leaked at end of model iteration. Each loom
    /// model run allocates a fresh one, which is acceptable: loom
    /// runs are tens of thousands of iterations, each allocating one
    /// 40-byte bin and one Box that loom_dtor leaves intact.
    fn build_loom_sharedbin() -> *mut SharedBin {
        static PAYLOAD: [u8; 4] = [0, 0, 0, 0];
        let bin = Box::new(SharedBin {
            refcount: AtomicUsize::new(1),
            bit_len: 32,
            bytes_ptr: PAYLOAD.as_ptr(),
            bytes_len: PAYLOAD.len(),
            destructor: loom_dtor,
        });
        Box::into_raw(bin)
    }

    #[test]
    fn loom_retain_release_two_threads() {
        loom::model(|| {
            let flag = Arc::new(AtomicBool::new(false));
            install_loom_flag(flag.clone());
            let p = build_loom_sharedbin();
            let p_addr = p as usize;

            let f1 = flag.clone();
            let t1 = loom::thread::spawn(move || {
                install_loom_flag(f1);
                let p = p_addr as *mut SharedBin;
                unsafe {
                    shared_bin_retain(p);
                    shared_bin_release(p);
                }
            });
            let f2 = flag.clone();
            let t2 = loom::thread::spawn(move || {
                install_loom_flag(f2);
                let p = p_addr as *mut SharedBin;
                unsafe {
                    shared_bin_retain(p);
                    shared_bin_release(p);
                }
            });
            t1.join().unwrap();
            t2.join().unwrap();
            // Main thread's final release fires the destructor.
            unsafe { shared_bin_release(p_addr as *mut SharedBin) };
            assert!(
                flag.load(LoomOrdering::SeqCst),
                "destructor must fire on last release"
            );
        });
    }
}
