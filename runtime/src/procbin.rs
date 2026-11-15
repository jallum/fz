//! Sealed procbin / off-heap binary abstraction.
//!
//! This module owns the entire off-heap binary story:
//!
//!   * `SharedBin` — refcounted byte buffer carrying its own destructor
//!     pointer. The destructor is a permanent property set at allocation
//!     time. Heap-allocated bins use `shared_bin_destructor_heap`; future
//!     compiler-baked static bins use `shared_bin_destructor_noop`.
//!   * `SharedBinHandle` — Arc-shaped owning wrapper. `Drop` releases.
//!   * `ProcBin` — `#[repr(transparent)]` newtype over the per-heap
//!     `u8*` stub. All offset arithmetic for ProcBin payload lives
//!     here; outside this module no code reads ProcBin layout directly.
//!   * `alloc_procbin` — safe constructor. Consumes a `SharedBinHandle`
//!     (refcount ownership transfers in), pushes the new ProcBin onto the
//!     heap's intrusive MSO chain via the `mso_next` link inside the
//!     ProcBin payload.
//!   * MSO sweep + drop — post-Cheney sweep walks the binary chains
//!     (`Heap::mso_head`, `Heap::mso_old_head`) and the resource chains
//!     (`Heap::resource_head`, `Heap::resource_old_head`), rewriting
//!     survivors to their to-space copy and releasing dead entries'
//!     shared_ptrs. `Heap::drop` releases every chain.
//!
//! Refcount ordering uses the canonical `Arc` pattern (Relaxed on retain,
//! Release on release, Acquire fence on final drop). Loom verification
//! runs through the `crate::sync` abstraction module.

use crate::any_value::{
    AnyValue, ValueKind, bitstring_bit_len as any_bitstring_bit_len, bitstring_bytes_ptr, heap_kind_from_tagged,
    heap_object_word, heap_word_addr,
};
use crate::heap::forwarded_target;
use crate::resource::{ResourceStub, fz_resource_release, fz_resource_release_deferred};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::mem::{align_of, forget, size_of};
use std::ptr::{NonNull, copy_nonoverlapping, read, slice_from_raw_parts_mut, write};

// ===== SharedBin layout =====================================================

/// Off-heap refcounted binary. `refcount` controls lifetime; `destructor` is
/// invoked exactly once when the refcount transitions to zero, with the
/// SharedBin pointer as its argument.
///
/// 16-ALIGNED ON PURPOSE. A ProcBin stub holds this address in word 0, and
/// that word is also where the Cheney collector writes its forwarding
/// marker, which is told from a live pointer by a set low nibble. Sharing the
/// heap's own 16-alignment invariant is what makes a real pointer and a
/// marker distinguishable by construction.
///
/// A buffer a concatenation allocated has room after its written bytes, and
/// only the process that owns it may write into that room. A view that ends
/// where the written bytes end can be handed to C as a string without a copy,
/// because the one byte after it is a NUL; a write by another process would
/// replace that NUL under a call in progress. Ownership is therefore
/// single: every path that makes a buffer reachable from another process
/// freezes it first (`shared_bin_freeze`), on the owner's thread, and a
/// frozen buffer is never written again. Until then every view of it lives on
/// the owner's heap, so `bytes_len` and `bit_len` change with no concurrent
/// reader, and `bytes_ptr` never moves.
///
/// `room` holds the buffer's capacity (the bytes it can hold ahead of the
/// trailing NUL) in its low bits and `ROOM_FROZEN` above them. The spare room
/// is the capacity less the written bytes; it is zero for a buffer that was
/// frozen and for a buffer with no capacity beyond its bytes, which is every
/// buffer but a concatenation's, and a compiler-baked static one holds 0.
#[repr(C, align(16))]
pub struct SharedBin {
    pub refcount: AtomicUsize,                            // offset 0..8
    pub bit_len: u64,                                     // offset 8..16
    pub bytes_ptr: *const u8,                             // offset 16..24
    pub bytes_len: usize,                                 // offset 24..32
    pub destructor: unsafe extern "C" fn(*mut SharedBin), // offset 32..40
    pub room: usize,                                      // offset 40..48
}

/// 48 bytes of fields, which is the 16-byte alignment above.
/// `define_static_sharedbin` emits this many bytes for the compiler-baked
/// copies, with `room` zero.
pub const SHARED_BIN_BYTES: usize = 48;

/// Set in `SharedBin::room` once the buffer has been made reachable from
/// another process: no one may write into it again.
const ROOM_FROZEN: usize = 1 << (usize::BITS - 1);

const _: () = {
    assert!(size_of::<SharedBin>() == SHARED_BIN_BYTES);
    assert!(align_of::<SharedBin>() == 16);
};

/// The bits of a stub's link word that hold its site.
const SITE_MASK: u64 = 0xF;
const _: () = assert!(StubSite::ALL.len() <= SITE_MASK as usize + 1);

/// Where a ProcBin stub keeps its `SharedBin` pointer, in bytes from the stub.
pub const PROCBIN_SHARED_OFFSET: usize = 0;
/// Where a ProcBin stub keeps the byte offset of its view, in bytes from the stub.
pub const PROCBIN_BYTE_OFFSET_OFFSET: usize = 16;
/// Where a ProcBin stub keeps the bit length of its view, in bytes from the stub.
pub const PROCBIN_BIT_LEN_OFFSET: usize = 24;
/// Where a `SharedBin` keeps the address of its bytes.
pub const SHARED_BIN_BYTES_PTR_OFFSET: usize = std::mem::offset_of!(SharedBin, bytes_ptr);
/// Where a `SharedBin` keeps its capacity and frozen flag. A compiler-baked
/// static buffer holds 0 here.
pub const SHARED_BIN_ROOM_OFFSET: usize = std::mem::offset_of!(SharedBin, room);

impl SharedBin {
    /// Bytes the buffer can hold ahead of its trailing NUL.
    fn capacity(&self) -> usize {
        self.room & !ROOM_FROZEN
    }

    /// Bytes an owner may still write after the written bytes. Zero once
    /// frozen.
    pub fn spare(&self) -> usize {
        if self.room & ROOM_FROZEN != 0 {
            return 0;
        }
        self.capacity().saturating_sub(self.bytes_len)
    }
}

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
    // The buffer was allocated with its capacity and one more byte for the
    // invisible trailing NUL. Free the full allocation.
    let bytes = unsafe { Box::from_raw(slice_from_raw_parts_mut(bin.bytes_ptr as *mut u8, bin.capacity() + 1)) };
    drop(bytes);
    drop(bin);
}

/// No-op destructor for compiler-baked static SharedBins. The
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
    shared_bin_alloc_with(bytes.len(), bit_len, 0, |dest| dest.copy_from_slice(bytes))
}

/// Allocate a heap-backed SharedBin holding `bytes` and `spare` more bytes of
/// room for its owner to append into.
pub fn shared_bin_alloc_with_room(bytes: &[u8], bit_len: u64, spare: usize) -> *mut SharedBin {
    shared_bin_alloc_with(bytes.len(), bit_len, spare, |dest| dest.copy_from_slice(bytes))
}

/// Allocate a heap-backed SharedBin of `bytes_len` bytes and `spare` more
/// bytes of room, and let `fill` write the payload straight into its buffer:
/// the buffer is the one allocation the binary owns, and nothing is staged and
/// copied in. Everything past the written bytes is zero, so the trailing NUL is
/// in place. The trailing NUL is invisible to the language (bytes_len/bit_len
/// unchanged) and underwrites the c_string extern marshal contract.
pub fn shared_bin_alloc_with(
    bytes_len: usize,
    bit_len: u64,
    spare: usize,
    fill: impl FnOnce(&mut [u8]),
) -> *mut SharedBin {
    let capacity = bytes_len + spare;
    let mut buf: Box<[u8]> = vec![0u8; capacity + 1].into_boxed_slice();
    fill(&mut buf[..bytes_len]);
    let bytes_ptr: *const u8 = Box::leak(buf).as_ptr();
    let bin = Box::new(SharedBin {
        refcount: AtomicUsize::new(1),
        bit_len,
        bytes_ptr,
        bytes_len,
        destructor: shared_bin_destructor_heap,
        room: capacity,
    });
    Box::into_raw(bin)
}

/// Forbid any further append into `p`'s buffer. Called on the owner's thread
/// before a view of the buffer becomes reachable from another process. A
/// buffer that is already frozen is left untouched, so a process that
/// received it never writes the word the sender's other receivers read.
///
/// # Safety
/// `p` must point at a live SharedBin, and the caller must be its owner or
/// hold it frozen already.
pub unsafe fn shared_bin_freeze(p: *mut SharedBin) {
    let bin = unsafe { &mut *p };
    if bin.room & ROOM_FROZEN == 0 {
        bin.room |= ROOM_FROZEN;
    }
}

/// Write `bytes` after `p`'s written bytes, widening them. The caller has
/// checked `bytes.len() <= (*p).spare()`.
///
/// # Safety
/// `p` must point at a live SharedBin the caller owns (see `SharedBin`).
pub unsafe fn shared_bin_append(p: *mut SharedBin, bytes: &[u8]) {
    let bin = unsafe { &mut *p };
    assert!(bytes.len() <= bin.spare(), "append past the buffer's spare room");
    unsafe {
        copy_nonoverlapping(
            bytes.as_ptr(),
            (bin.bytes_ptr as *mut u8).add(bin.bytes_len),
            bytes.len(),
        );
    }
    bin.bytes_len += bytes.len();
    bin.bit_len = bin.bytes_len as u64 * 8;
    // The byte after the new end is still zero: the buffer is zeroed beyond
    // its written bytes and only appends write there.
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

    /// Allocate a new heap-backed SharedBin holding `bytes` with `spare` bytes
    /// of room after them, and wrap the initial refcount.
    pub fn from_bytes_with_room(bytes: &[u8], spare: usize) -> Self {
        let p = shared_bin_alloc_with_room(bytes, bytes.len() as u64 * 8, spare);
        Self(NonNull::new(p).expect("shared_bin_alloc_with_room returned null"))
    }

    /// Allocate a new heap-backed SharedBin of `bytes_len` bytes that `fill`
    /// writes in place, and wrap the initial refcount.
    pub fn from_filled(bytes_len: usize, bit_len: u64, fill: impl FnOnce(&mut [u8])) -> Self {
        let p = shared_bin_alloc_with(bytes_len, bit_len, 0, fill);
        Self(NonNull::new(p).expect("shared_bin_alloc_with returned null"))
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

/// Per-heap stub naming a byte-aligned window of a `SharedBin`'s bytes.
/// `PROCBIN_BYTES` total:
///   offset 0..8    shared_ptr:  *mut SharedBin
///   offset 8..16   mso_next:    u64 tagged MSO link, or 0, with the site
///                               that made the stub in its low nibble
///   offset 16..24  byte_offset: u64 first byte of this stub's view
///   offset 24..32  bit_len:     u64 length of this stub's view in bits
///
/// A whole binary is the window at offset 0 spanning the buffer. Slicing
/// allocates another stub over the SAME SharedBin, which is what makes
/// `<<_c, rest :: binary>>` and `<<_ :: binary-size(n), field :: binary, _ :: binary>>`
/// copy nothing.
///
/// The buffer carries one invisible trailing NUL after its last byte. A
/// window that ends where the buffer ends (`ends_at_buffer_end`) has that NUL
/// right after it; any other window does not, and a C string over it needs a
/// copy.
///
/// Cheney forwarding overwrites offset 0 with a forwarding marker.
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
        unsafe { read(self.as_raw().add(PROCBIN_SHARED_OFFSET) as *const *mut SharedBin) }
    }

    fn shared_raw_set(&self, p: *mut SharedBin) {
        unsafe {
            write(self.as_raw().add(PROCBIN_SHARED_OFFSET) as *mut *mut SharedBin, p);
        }
    }

    fn link_word(&self) -> u64 {
        unsafe { read((self.as_raw() as *const u8).add(8) as *const u64) }
    }

    /// The tagged link to the next stub on the chain, or 0. Heap objects are
    /// 16-byte aligned, so a link's low nibble is free: it holds the stub's
    /// site, which a copy of the stub carries along.
    pub fn mso_next(&self) -> u64 {
        self.link_word() & !SITE_MASK
    }

    pub(crate) fn mso_next_set(&self, next: u64) {
        debug_assert_eq!(next & SITE_MASK, 0, "a chain link is a 16-byte aligned heap word");
        let site = self.link_word() & SITE_MASK;
        unsafe {
            write(self.as_raw().add(8) as *mut u64, next | site);
        }
    }

    /// What made this stub.
    pub fn site(&self) -> StubSite {
        StubSite::from_code((self.link_word() & SITE_MASK) as u8)
    }

    fn site_set(&self, site: StubSite) {
        unsafe {
            write(self.as_raw().add(8) as *mut u64, u64::from(site.code()));
        }
    }

    /// First byte of this stub's view into the shared buffer.
    pub fn byte_offset(&self) -> u64 {
        unsafe { read(self.as_raw().add(PROCBIN_BYTE_OFFSET_OFFSET) as *const u64) }
    }

    fn byte_offset_set(&self, offset: u64) {
        unsafe {
            write(self.as_raw().add(PROCBIN_BYTE_OFFSET_OFFSET) as *mut u64, offset);
        }
    }

    pub fn bit_len(&self) -> u64 {
        unsafe { read(self.as_raw().add(PROCBIN_BIT_LEN_OFFSET) as *const u64) }
    }

    fn bit_len_set(&self, bit_len: u64) {
        unsafe {
            write(self.as_raw().add(PROCBIN_BIT_LEN_OFFSET) as *mut u64, bit_len);
        }
    }

    pub fn bytes_ptr(&self) -> *const u8 {
        unsafe { (*self.shared_raw()).bytes_ptr.add(self.byte_offset() as usize) }
    }

    pub fn bytes_len(&self) -> usize {
        (self.bit_len() as usize).div_ceil(8)
    }

    /// True when the buffer's invisible trailing NUL follows this view's last byte.
    pub fn ends_at_buffer_end(&self) -> bool {
        self.byte_offset() as usize + self.bytes_len() == unsafe { (*self.shared_raw()).bytes_len }
    }
}

// ===== Allocation on a per-process heap =====================================

use crate::heap::{Generation, Heap, HeapAllocKind, StubCounts, StubSite};

/// Allocate a ProcBin stub on `heap` viewing `bit_len` bits of `handle`'s
/// bytes from `byte_offset`, taking ownership of the SharedBin reference
/// encapsulated in `handle`. The new ProcBin is pushed onto `heap.mso_head`,
/// the young binary chain, as the new chain head.
///
/// A whole binary is `(0, handle.bit_len())`. `site` names what is making the
/// stub; the heap counts it and the stub remembers it.
pub fn alloc_procbin(
    heap: &mut Heap,
    handle: SharedBinHandle,
    byte_offset: u64,
    bit_len: u64,
    site: StubSite,
) -> ProcBin {
    assert!(
        byte_offset as usize + (bit_len as usize).div_ceil(8) <= handle.bytes_len(),
        "ProcBin view [{byte_offset}, +{bit_len} bits) runs past the shared buffer"
    );
    let p = heap.alloc_kind(HeapAllocKind::ProcBin, PROCBIN_BYTES);
    let pb = unsafe { ProcBin::from_raw(p) };
    pb.site_set(site);
    heap.stubs_made.record(site);
    pb.shared_raw_set(handle.into_raw());
    pb.byte_offset_set(byte_offset);
    pb.bit_len_set(bit_len);
    let previous_head = heap.mso_push(heap_object_word(p, ValueKind::PROCBIN));
    pb.mso_next_set(previous_head);
    pb
}

/// A stub that lives on an MSO chain. The stub's type is its chain's kind:
/// binary stubs and resource stubs keep separate chains, so a walk over one
/// chain names the kind once and never inspects a link to learn it.
pub(crate) trait MsoStub: Copy {
    /// The heap object kind every link of this stub's chains carries.
    const KIND: ValueKind;

    /// # Safety
    /// `addr` must point at a live stub of this kind.
    unsafe fn at(addr: *mut u8) -> Self;
    fn link(&self) -> u64;
    fn set_link(&self, next: u64);
    /// Drop the off-heap reference this stub holds.
    fn release(&self);
}

impl MsoStub for ProcBin {
    const KIND: ValueKind = ValueKind::PROCBIN;

    unsafe fn at(addr: *mut u8) -> Self {
        unsafe { ProcBin::from_raw(addr) }
    }

    fn link(&self) -> u64 {
        self.mso_next()
    }

    fn set_link(&self, next: u64) {
        self.mso_next_set(next)
    }

    fn release(&self) {
        unsafe { shared_bin_release(self.shared_raw()) };
    }
}

impl MsoStub for ResourceStub {
    const KIND: ValueKind = ValueKind::RESOURCE;

    unsafe fn at(addr: *mut u8) -> Self {
        unsafe { ResourceStub::from_raw(addr) }
    }

    fn link(&self) -> u64 {
        self.mso_next()
    }

    fn set_link(&self, next: u64) {
        self.mso_next_set(next)
    }

    fn release(&self) {
        unsafe { fz_resource_release(self.shared_raw()) };
    }
}

/// Point the link of the stub that `link` names, on a chain of `S` stubs, at
/// `next`.
pub(crate) fn mso_set_next<S: MsoStub>(link: u64, next: u64) {
    unsafe { S::at(chain_stub_addr::<S>(link)) }.set_link(next);
}

/// The address of the stub a chain link names. A link is a heap object word:
/// the stub's kind rides above its address, and on a chain of `S` stubs it
/// is `S::KIND`.
fn chain_stub_addr<S: MsoStub>(link: u64) -> *mut u8 {
    debug_assert_eq!(
        heap_kind_from_tagged(link),
        Some(S::KIND),
        "MSO chain link {link:#x} is not a {:?} stub",
        S::KIND
    );
    heap_word_addr(link)
}

// ===== MSO sweep + drop =====================================================

/// A resource whose last reference a sweep dropped: the fz closure that
/// destroys it and the payload that closure receives. `closure` is the
/// closure's value-ref word and `payload` the C payload word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeadResource {
    pub closure: u64,
    pub payload: u64,
}

/// The head of each chain a collection of `generation` examines: the young
/// chain, and for a major collection the old chain too. A stub on the other
/// chain is not examined: a minor collection does not look at an old stub.
fn examined_chain_heads(young: u64, old: u64, generation: Generation) -> impl Iterator<Item = u64> {
    let old_head = (generation == Generation::Major).then_some(old);
    std::iter::once(young).chain(old_head)
}

/// The destructor closures of the resource stubs a collection's trace has not
/// reached, keyed by stub address. Those closures are about to be orphaned
/// with the from-space, so the collector forwards them before the sweep
/// decides the stubs. Claimed resources are skipped: their owner cleans up
/// deterministically and no closure will run. Only the stubs `generation`
/// examines are considered, and only the resource chains are walked: a binary
/// stub has no closure. `visits` counts the chain links followed.
pub(crate) fn mso_unreached_closures(heap: &Heap, generation: Generation, visits: &mut u64) -> Vec<(usize, AnyValue)> {
    let mut unreached = Vec::new();
    for head in examined_chain_heads(heap.resource_head, heap.resource_old_head, generation) {
        let mut cur_bits = head;
        while cur_bits != 0 {
            *visits += 1;
            let cur = chain_stub_addr::<ResourceStub>(cur_bits);
            let rs = unsafe { ResourceStub::from_raw(cur) };
            if forwarded_target(cur, ValueKind::RESOURCE).is_none() && !rs.is_claimed() {
                unreached.push((cur as usize, rs.closure_value()));
            }
            cur_bits = rs.mso_next();
        }
    }
    unreached
}

/// Decide every stub on the chains `generation` examines: the young chains, and
/// for a major collection the old chains too. This is the one place a dead
/// stub is handled, after a collection's trace and when a process exits (a
/// process exit is a major sweep with nothing live). Each stub is visited
/// once, `visits` counting the chain links followed.
///
/// A stub carrying a forwarding marker survived: it is relinked to its
/// to-space copy, on the old chain of its kind, which a minor sweep leaves
/// otherwise untouched and a major sweep rebuilds. Any other stub is dead and
/// drops its off-heap reference. A dead ProcBin releases its SharedBin
/// synchronously. A dead Resource whose last reference this was returns a
/// `DeadResource`, unless it was claimed; its destructor is fz code and runs
/// at the scheduler boundary, never inside the sweep. `closure_of` yields the
/// destructor closure of a dead resource stub as a value that is valid once
/// the sweep returns: the forwarded closure after a collection, the closure
/// as it stands at exit.
///
/// A survivor's from-space word 0 holds a forwarding marker, so its off-heap
/// pointer is read from the to-space copy. Must run before the
/// from-space is released, since dead stubs live there.
pub fn mso_sweep(
    heap: &mut Heap,
    generation: Generation,
    mut closure_of: impl FnMut(&ResourceStub) -> AnyValue,
    visits: &mut u64,
    survived: &mut StubCounts,
) -> Vec<DeadResource> {
    let mut dead = Vec::new();
    heap.mso_old_head = sweep_chains::<ProcBin>(
        heap.mso_head,
        heap.mso_old_head,
        generation,
        visits,
        |pb| unsafe { shared_bin_release(pb.shared_raw()) },
        |pb| survived.record(pb.site()),
    );
    heap.resource_old_head = sweep_chains::<ResourceStub>(
        heap.resource_head,
        heap.resource_old_head,
        generation,
        visits,
        |rs| {
            if let Some(payload) = unsafe { fz_resource_release_deferred(rs.shared_raw()) } {
                dead.push(DeadResource {
                    closure: closure_of(&rs).ref_word().raw_word(),
                    payload,
                });
            }
        },
        |_| {},
    );
    heap.mso_head = 0;
    heap.resource_head = 0;
    dead
}

/// Sweep the chains of `S` stubs `generation` examines and return the new old
/// chain head: survivors, relinked to their to-space copies, ahead of the old
/// chain a minor collection leaves alone.
fn sweep_chains<S: MsoStub>(
    young: u64,
    old: u64,
    generation: Generation,
    visits: &mut u64,
    mut on_dead: impl FnMut(S),
    mut on_survivor: impl FnMut(S),
) -> u64 {
    let mut new_old_head = match generation {
        Generation::Minor => old,
        Generation::Major => 0,
    };
    for head in examined_chain_heads(young, old, generation) {
        let mut cur_bits = head;
        while cur_bits != 0 {
            *visits += 1;
            let cur = chain_stub_addr::<S>(cur_bits);
            let stub = unsafe { S::at(cur) };
            let next = stub.link();
            match forwarded_target(cur, S::KIND) {
                Some(to_p) => {
                    on_survivor(stub);
                    unsafe { S::at(to_p) }.set_link(new_old_head);
                    new_old_head = heap_object_word(to_p, S::KIND);
                }
                None => on_dead(stub),
            }
            cur_bits = next;
        }
    }
    new_old_head
}

/// Drop every stub on the young and old chains, releasing each off-heap
/// reference. Called from `Heap::drop` before pool reclaim.
pub fn mso_drop_all(heap: &mut Heap) {
    mso_release_chain::<ProcBin>(heap.mso_head);
    mso_release_chain::<ProcBin>(heap.mso_old_head);
    mso_release_chain::<ResourceStub>(heap.resource_head);
    mso_release_chain::<ResourceStub>(heap.resource_old_head);
    heap.mso_head = 0;
    heap.mso_old_head = 0;
    heap.resource_head = 0;
    heap.resource_old_head = 0;
}

/// Release every stub on the chain of `S` stubs that starts at `head_bits`:
/// each ProcBin drops its SharedBin reference and each Resource stub drops its
/// Resource reference. The chain's memory is left to its owner.
pub(crate) fn mso_release_chain<S: MsoStub>(head_bits: u64) {
    let mut cur_bits = head_bits;
    while cur_bits != 0 {
        let stub = unsafe { S::at(chain_stub_addr::<S>(cur_bits)) };
        cur_bits = stub.link();
        stub.release();
    }
}

// ===== Bitstring dispatch helpers (moved from any_value.rs) ==================
//
// fz bitstrings live in one of two storage modes:
//   * `ValueKind::BITSTRING` -- inline payload: bit length at +0, bytes at +8.
//   * `ValueKind::PROCBIN` -- *mut SharedBin at +0; bytes + bit_len off-heap.
//
// The helpers below take a heap object word, whose kind says which mode.

/// True if `word` is a heap object word whose bytes can be read as a bitstring.
pub fn is_bitstring_like(word: u64) -> bool {
    heap_kind_from_tagged(word).is_some_and(ValueKind::is_binary_repr)
}

/// Bit length of a bitstring-like heap value.
///
/// # Safety
/// `word` must be the heap object word of a live Bitstring or ProcBin.
pub unsafe fn bitstring_bit_len(word: u64) -> u64 {
    let addr = heap_word_addr(word);
    if heap_kind_from_tagged(word) == Some(ValueKind::PROCBIN) {
        return unsafe { ProcBin::from_raw(addr) }.bit_len();
    }
    unsafe { any_bitstring_bit_len(addr) }
}

/// Byte pointer to the underlying bitstring payload.
///
/// # Safety
/// `word` must be the heap object word of a live Bitstring or ProcBin.
pub unsafe fn bitstring_byte_ptr(word: u64) -> *const u8 {
    let addr = heap_word_addr(word);
    if heap_kind_from_tagged(word) == Some(ValueKind::PROCBIN) {
        return unsafe { ProcBin::from_raw(addr) }.bytes_ptr();
    }
    unsafe { bitstring_bytes_ptr(addr) }
}

/// Bytes of the buffer a bitstring-like heap value references: the whole
/// `SharedBin` for a ProcBin view, however short the view, and the value's own
/// bytes for an inline bitstring.
///
/// # Safety
/// `word` must be the heap object word of a live Bitstring or ProcBin.
pub unsafe fn referenced_byte_len(word: u64) -> usize {
    let addr = heap_word_addr(word);
    if heap_kind_from_tagged(word) == Some(ValueKind::PROCBIN) {
        return unsafe { (*ProcBin::from_raw(addr).shared_raw()).bytes_len };
    }
    (unsafe { any_bitstring_bit_len(addr) } as usize).div_ceil(8)
}

/// Compare two bitstring-like heap values by language value, not address.
///
/// # Safety
/// Both words must be the heap object words of live Bitstring or ProcBin objects.
pub unsafe fn bitstring_like_eq(ap: u64, bp: u64) -> bool {
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
