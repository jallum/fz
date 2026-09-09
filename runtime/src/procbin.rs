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
//!     `u8*` stub. All offset arithmetic for ProcBin payload lives
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

use crate::any_value::{
    AnyValue, TAG_BITSTRING, TAG_FWD, TAG_MASK, TAG_PROCBIN, TAG_RESOURCE, ValueKind,
    bitstring_bit_len as any_bitstring_bit_len, bitstring_bytes_ptr, heap_object_word,
};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::mem::{align_of, forget, size_of};
use std::ptr::{NonNull, read, slice_from_raw_parts_mut, write};

// ===== SharedBin layout =====================================================

/// Off-heap refcounted binary. `refcount` controls lifetime; `destructor` is
/// invoked exactly once when the refcount transitions to zero, with the
/// SharedBin pointer as its argument.
///
/// 16-ALIGNED ON PURPOSE. A ProcBin stub holds this address in word 0, and
/// that word is also where the Cheney collector writes its forwarding
/// marker -- a pointer with `TAG_FWD` (0x8) in the low four bits. At 8-byte
/// alignment half of all SharedBin addresses end in 8, and a live stub read
/// as forwarded (fz-5xp.60). Sharing the heap's own 16-alignment invariant
/// is what makes a real pointer and a tag distinguishable by construction.
#[repr(C, align(16))]
pub struct SharedBin {
    pub refcount: AtomicUsize,                            // offset 0..8
    pub bit_len: u64,                                     // offset 8..16
    pub bytes_ptr: *const u8,                             // offset 16..24
    pub bytes_len: usize,                                 // offset 24..32
    pub destructor: unsafe extern "C" fn(*mut SharedBin), // offset 32..40
}

/// 40 bytes of fields, rounded to the 16-byte alignment above. The field
/// offsets are unchanged, and `define_static_sharedbin` emits this many
/// bytes for the compiler-baked copies.
pub const SHARED_BIN_BYTES: usize = 48;

const _: () = {
    assert!(size_of::<SharedBin>() == SHARED_BIN_BYTES);
    assert!(align_of::<SharedBin>() == 16);
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
    let bytes = unsafe { Box::from_raw(slice_from_raw_parts_mut(bin.bytes_ptr as *mut u8, bin.bytes_len + 1)) };
    drop(bytes);
    drop(bin);
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
        forget(self);
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

/// Per-heap stub naming a byte-aligned SUFFIX of a `SharedBin`'s bytes.
/// `PROCBIN_BYTES` total:
///   offset 0..8    shared_ptr:  *mut SharedBin
///   offset 8..16   mso_next:    u64 tagged MSO link, or 0
///   offset 16..24  byte_offset: u64 first byte of this stub's view
///   offset 24..32  unused -- the heap rounds every object to a 16-byte
///                  slot, so 24 and 32 cost the same.
///
/// A whole binary is the suffix at offset 0. A tail match allocates another
/// stub over the SAME SharedBin at a later offset, which is what makes
/// `<<_c, rest :: binary>>` copy nothing (fz-5xp.55).
///
/// SUFFIX, not an arbitrary window, is the load-bearing constraint. The
/// buffer carries one invisible trailing NUL ([[fz-wu9]]), and a suffix
/// ends where the buffer ends -- so the parent's NUL is also every
/// suffix's NUL and `fz_binary_as_cstring` needs no flattening copy. An
/// arbitrary window would not have that, which is why one cannot be built:
/// `alloc_procbin` derives the length from the offset rather than taking
/// it.
///
/// Cheney forwarding overwrites offset 0 with a headerless forwarding marker.
/// Offset 8 is preserved in from-space, so MSO sweep reads `mso_next` from the
/// old stub and `shared_ptr` from the to-space copy if the stub survived.
/// Size of a ProcBin stub in bytes. The single authority: allocation, GC
/// copying and `object_size` all read it here.
pub const PROCBIN_BYTES: usize = 32;

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ProcBin(NonNull<u8>);

impl ProcBin {
    /// # Safety
    /// `p` must point at a live strict ProcBin object.
    pub unsafe fn from_raw(p: *mut u8) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("ProcBin::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    pub fn shared_raw(&self) -> *mut SharedBin {
        unsafe { read(self.as_raw() as *const *mut SharedBin) }
    }

    fn shared_raw_set(&self, p: *mut SharedBin) {
        unsafe {
            write(self.as_raw() as *mut *mut SharedBin, p);
        }
    }

    pub fn mso_next(&self) -> u64 {
        unsafe { read((self.as_raw() as *const u8).add(8) as *const u64) }
    }

    pub(crate) fn mso_next_set(&self, next: u64) {
        unsafe {
            write(self.as_raw().add(8) as *mut u64, next);
        }
    }

    /// First byte of this stub's view into the shared buffer.
    pub fn byte_offset(&self) -> u64 {
        unsafe { read(self.as_raw().add(16) as *const u64) }
    }

    fn byte_offset_set(&self, offset: u64) {
        unsafe {
            write(self.as_raw().add(16) as *mut u64, offset);
        }
    }

    pub fn bit_len(&self) -> u64 {
        unsafe { (*self.shared_raw()).bit_len - self.byte_offset() * 8 }
    }

    pub fn bytes_ptr(&self) -> *const u8 {
        unsafe { (*self.shared_raw()).bytes_ptr.add(self.byte_offset() as usize) }
    }

    pub fn bytes_len(&self) -> usize {
        unsafe { (*self.shared_raw()).bytes_len - self.byte_offset() as usize }
    }
}

// ===== Allocation on a per-process heap =====================================

use crate::heap::{Heap, HeapAllocKind};

/// Allocate a ProcBin stub on `heap` viewing `handle`'s bytes from
/// `byte_offset` to the end, taking ownership of the SharedBin reference
/// encapsulated in `handle`. The new ProcBin is pushed onto `heap.mso_head`
/// as the new chain head.
///
/// Pass `0` for the whole binary. The length is derived, not passed: see
/// the `ProcBin` layout note for why only suffixes are constructible.
pub fn alloc_procbin(heap: &mut Heap, handle: SharedBinHandle, byte_offset: u64) -> ProcBin {
    assert!(
        byte_offset as usize <= handle.bytes_len(),
        "ProcBin suffix offset {byte_offset} past the shared buffer"
    );
    let p = heap.alloc_kind(HeapAllocKind::ProcBin, PROCBIN_BYTES);
    let pb = unsafe { ProcBin::from_raw(p) };
    pb.shared_raw_set(handle.into_raw());
    pb.mso_next_set(heap.mso_head);
    pb.byte_offset_set(byte_offset);
    heap.mso_head = heap_object_word(p, ValueKind::PROCBIN);
    pb
}

// ===== MSO sweep + drop =====================================================

/// Walk `heap.mso_head` after Cheney BFS completes. Strict ProcBin/Resource
/// survivors carry a headerless forwarding marker at offset 0, so their
/// off-heap pointer must be read from the to-space copy.
pub fn mso_sweep(heap: &mut Heap) {
    use crate::resource::{ResourceStub, fz_resource_release};
    let mut new_head = 0_u64;
    let mut cur_bits = heap.mso_head;
    while cur_bits != 0 {
        let kind = cur_bits & TAG_MASK;
        let cur = mso_addr(cur_bits);
        let first = unsafe { read(cur as *const u64) };
        if first & TAG_MASK == TAG_FWD {
            let to_p = (first & !TAG_MASK) as *mut u8;
            let next = match kind {
                TAG_PROCBIN => unsafe { ProcBin::from_raw(cur).mso_next() },
                TAG_RESOURCE => unsafe { ResourceStub::from_raw(cur).mso_next() },
                _ => panic!("mso_sweep: invalid MSO tag {kind:#x}"),
            };
            let new_bits = (to_p as u64) | kind;
            if kind == TAG_RESOURCE {
                unsafe { ResourceStub::from_raw(to_p).mso_next_set(new_head) };
            } else {
                unsafe { ProcBin::from_raw(to_p).mso_next_set(new_head) };
            }
            new_head = new_bits;
            cur_bits = next;
            continue;
        }

        match kind {
            TAG_PROCBIN => {
                let pb = unsafe { ProcBin::from_raw(cur) };
                let next = pb.mso_next();
                unsafe { shared_bin_release(pb.shared_raw()) };
                cur_bits = next;
            }
            TAG_RESOURCE => {
                let rs = unsafe { ResourceStub::from_raw(cur) };
                let next = rs.mso_next();
                unsafe { fz_resource_release(rs.shared_raw()) };
                cur_bits = next;
            }
            _ => panic!("mso_sweep: invalid MSO tag {kind:#x}"),
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
    let mut cur_bits = heap.mso_head;
    while cur_bits != 0 {
        let kind = cur_bits & TAG_MASK;
        let cur = mso_addr(cur_bits);
        match kind {
            TAG_PROCBIN => {
                let pb = unsafe { ProcBin::from_raw(cur) };
                let next = pb.mso_next();
                unsafe { shared_bin_release(pb.shared_raw()) };
                cur_bits = next;
            }
            TAG_RESOURCE => {
                let rs = unsafe { ResourceStub::from_raw(cur) };
                let next = rs.mso_next();
                let closure = rs.closure_value();
                if let Some(payload) = unsafe { fz_resource_release_deferred(rs.shared_raw()) } {
                    let payload_ref = heap.box_any_value_ref(AnyValue::int(payload as i64)).raw_word();
                    let closure_bits = closure.ref_word().raw_word();
                    heap.pending_dtors.push_back((closure_bits, payload_ref));
                }
                cur_bits = next;
            }
            _ => panic!("mso_drop_all_deferred: invalid MSO tag {kind:#x}"),
        }
    }
    heap.mso_head = 0;
}

fn mso_addr(bits: u64) -> *mut u8 {
    (bits & !TAG_MASK) as *mut u8
}

/// Drop every ProcBin in `heap.mso_head`'s chain, releasing each
/// SharedBin reference. Called from `Heap::drop` before pool reclaim.
pub fn mso_drop_all(heap: &mut Heap) {
    use crate::resource::{ResourceStub, fz_resource_release};
    let mut cur_bits = heap.mso_head;
    while cur_bits != 0 {
        let kind = cur_bits & TAG_MASK;
        let cur = mso_addr(cur_bits);
        match kind {
            TAG_PROCBIN => {
                let pb = unsafe { ProcBin::from_raw(cur) };
                let next = pb.mso_next();
                unsafe { shared_bin_release(pb.shared_raw()) };
                cur_bits = next;
            }
            TAG_RESOURCE => {
                let rs = unsafe { ResourceStub::from_raw(cur) };
                let next = rs.mso_next();
                unsafe { fz_resource_release(rs.shared_raw()) };
                cur_bits = next;
            }
            _ => panic!("mso_drop_all: invalid MSO tag {kind:#x}"),
        }
    }
    heap.mso_head = 0;
}

// ===== Bitstring dispatch helpers (moved from any_value.rs) ==================
//
// fz bitstrings live in one of two storage modes:
//   * `TAG_BITSTRING` — inline payload: bit_len at +0, bytes at +8.
//   * `TAG_PROCBIN` — *mut SharedBin at +0; bytes + bit_len off-heap.

/// True if `p` is a heap value whose bytes can be read as a bitstring.
///
/// # Safety
/// `p` must be a live tagged bitstring-like heap pointer.
pub unsafe fn is_bitstring_like(p: *const u8) -> bool {
    matches!((p as u64) & TAG_MASK, TAG_BITSTRING | TAG_PROCBIN)
}

/// Bit length of a bitstring-like heap value.
///
/// # Safety
/// `p` must be a live tagged bitstring-like heap pointer.
pub unsafe fn bitstring_bit_len(p: *const u8) -> u64 {
    if (p as u64) & TAG_MASK == TAG_PROCBIN {
        let p = ((p as u64) & !TAG_MASK) as *mut u8;
        let pb = unsafe { ProcBin::from_raw(p) };
        return pb.bit_len();
    }
    let p = ((p as u64) & !TAG_MASK) as *const u8;
    unsafe { any_bitstring_bit_len(p) }
}

/// Byte pointer to the underlying bitstring payload.
///
/// # Safety
/// `p` must be a live tagged bitstring-like heap pointer.
pub unsafe fn bitstring_byte_ptr(p: *const u8) -> *const u8 {
    if (p as u64) & TAG_MASK == TAG_PROCBIN {
        let p = ((p as u64) & !TAG_MASK) as *mut u8;
        let pb = unsafe { ProcBin::from_raw(p) };
        return pb.bytes_ptr();
    }
    let p = ((p as u64) & !TAG_MASK) as *const u8;
    unsafe { bitstring_bytes_ptr(p) }
}

/// Compare two bitstring-like heap values by language value, not address.
///
/// # Safety
/// Both pointers must identify live Bitstring or ProcBin heap objects.
pub unsafe fn bitstring_like_eq(ap: *const u8, bp: *const u8) -> bool {
    let a_bits = unsafe { bitstring_bit_len(ap) };
    let b_bits = unsafe { bitstring_bit_len(bp) };
    if a_bits != b_bits {
        return false;
    }
    let bit_len = a_bits as usize;
    let full_bytes = bit_len / 8;
    let trailing = bit_len % 8;
    let a_pay = unsafe { bitstring_byte_ptr(ap) };
    let b_pay = unsafe { bitstring_byte_ptr(bp) };
    for i in 0..full_bytes {
        if unsafe { *a_pay.add(i) != *b_pay.add(i) } {
            return false;
        }
    }
    if trailing > 0 {
        let mask: u8 = 0xFFu8 << (8 - trailing);
        let a_last = unsafe { *a_pay.add(full_bytes) } & mask;
        let b_last = unsafe { *b_pay.add(full_bytes) } & mask;
        if a_last != b_last {
            return false;
        }
    }
    true
}

// ===== Tests ================================================================

#[cfg(test)]
#[path = "procbin_test.rs"]
mod procbin_test;

// ===== fz-q8d.3 — loom verification of retain/release ordering ==============
//
// Enabled only under `RUSTFLAGS="--cfg loom"`. The two-thread model
// constructs a SharedBin with an observed destructor, spawns two children that
// each retain+release, then the "main" thread performs the final
// release. Across every legal interleaving loom can produce, the test
// destructor must fire exactly once.
//
// Run: `RUSTFLAGS="--cfg loom" cargo test --release -p fz-runtime loom_`.

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
            assert!(flag.load(LoomOrdering::SeqCst), "destructor must fire on last release");
        });
    }
}

/// fz-5xp.60 — a ProcBin stub holds its SharedBin's address in word 0, and
/// that is the word Cheney overwrites with a `TAG_FWD` (0x8) forwarding
/// marker. At 8-byte alignment half of all SharedBin addresses end in 8 and
/// a LIVE stub reads as forwarded, so the sweep treats the SharedBin itself
/// as a to-space stub and writes into it. 16-alignment is what makes a real
/// pointer and a tag distinguishable.
#[cfg(test)]
mod shared_bin_alignment_test {
    use super::*;

    #[test]
    fn a_shared_bin_address_is_never_mistakable_for_a_forwarding_marker() {
        assert_eq!(align_of::<SharedBin>(), 16);
        // Many at once: at 8-alignment about half of these would end in 8.
        let bins: Vec<SharedBinHandle> = (0..64u8).map(|i| SharedBinHandle::from_bytes(&[i; 8], 64)).collect();
        for bin in &bins {
            let addr = bin.as_raw() as u64;
            assert_eq!(addr % 16, 0, "SharedBin at {addr:#x} is not 16-aligned");
            assert_ne!(addr & TAG_MASK, TAG_FWD);
        }
    }
}
