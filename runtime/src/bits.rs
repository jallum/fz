//! Sealed off-heap binary abstraction.
//!
//! This module owns the entire off-heap binary story:
//!
//!   * `SharedBin` — refcounted byte buffer carrying its own destructor
//!     pointer. The destructor is a permanent property set at allocation
//!     time. Heap-allocated bins use `shared_bin_destructor_heap`; future
//!     compiler-baked static bins use `shared_bin_destructor_noop`.
//!   * `SharedBinHandle` — Arc-shaped owning wrapper. `Drop` releases.
//!   * `BinRef` — the one object per shared buffer per heap that holds the
//!     buffer's reference. It is the only binary object on the heap's sweep
//!     chain, and no language value is a `BinRef`.
//!   * `BinView` — `#[repr(transparent)]` newtype over the per-heap `u8*`
//!     object a binary value points at: a window onto the bytes of a buffer,
//!     reached through its heap's `BinRef`. A view holds no reference and is on
//!     no chain; the collector traces it like any heap object. All offset
//!     arithmetic for both layouts lives here; outside this module no code
//!     reads them directly.
//!   * `alloc_binref`, `alloc_view`, `alloc_buffer_view` — the safe
//!     constructors. A `BinRef` takes ownership of a `SharedBinHandle`'s
//!     reference and is pushed onto the heap's intrusive off-heap chain through the
//!     `off_heap_next` link inside its payload.
//!   * off-heap sweep + drop — post-Cheney sweep walks the one off-heap chain
//!     (`Heap::off_heap_head`, `Heap::off_heap_old_head`), which holds BinRefs and
//!     resource stubs alike, rewriting survivors to their to-space copy and
//!     releasing dead entries' shared_ptrs. `Heap::drop` releases every chain.
//!
//! Refcount ordering uses the canonical `Arc` pattern (Relaxed on retain,
//! Release on release, Acquire fence on final drop). Loom verification
//! runs through the `crate::sync` abstraction module.

use crate::alloc_site::RuntimeAllocSite;
use crate::any_value::{
    AnyValueRefPacking, BINARY_MAX_BIT_LEN, BINARY_SHARED_MASK, ValueKind, bitstring_bit_len as header_bit_len,
    bitstring_bytes_ptr, bitstring_header_word, bitstring_is_shared, heap_kind_from_tagged, heap_object_word,
    heap_word_addr, share_bitstring,
};
use crate::heap::{binary_buffer_allocated, binary_buffer_freed, poisoned};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::alloc::{Layout, alloc, dealloc};
use std::mem::{MaybeUninit, align_of, forget, size_of};
use std::ptr::{NonNull, copy_nonoverlapping, read, write};
use std::slice::{from_raw_parts, from_raw_parts_mut};

// ===== SharedBin layout =====================================================

/// Off-heap refcounted binary. `refcount` controls lifetime; `destructor` is
/// invoked exactly once when the refcount transitions to zero, with the
/// SharedBin pointer as its argument.
///
/// 16-ALIGNED ON PURPOSE. A BinRef holds this address in word 0, and
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
/// closes its spare room first (`shared_bin_freeze`), on the owner's thread,
/// and a frozen buffer is never written again. Until then every view of it
/// lives on the owner's heap, so `bytes_len` changes with no concurrent reader,
/// and `bytes_ptr` never moves. A buffer with no spare room has nothing to
/// close, so no path writes it at all. The buffer holds whole bytes and says nothing of
/// how many bits of the last one a value uses: a view's own `bit_len` is the
/// one authority on a value's length.
///
/// A heap-backed buffer is ONE allocation: this header, then its bytes, then
/// room, then the trailing NUL, with `bytes_ptr` pointing just past the header.
/// The block is never reallocated, which is what keeps the header's address and
/// `bytes_ptr` fixed: a result that outgrows the room is a new block.
///
/// `room` holds the buffer's capacity (the bytes it can hold ahead of the
/// trailing NUL) in its low bits and `ROOM_FROZEN` above them. The spare room
/// is the capacity less the written bytes; it is zero for a buffer that was
/// frozen and for a buffer with no capacity beyond its bytes, which is every
/// buffer but a concatenation's, and a compiler-baked static one holds 0.
#[repr(C, align(16))]
pub struct SharedBin {
    pub refcount: AtomicUsize,                            // offset 0..8
    pub bytes_ptr: *const u8,                             // offset 8..16
    pub bytes_len: usize,                                 // offset 16..24
    pub destructor: unsafe extern "C" fn(*mut SharedBin), // offset 24..32
    pub room: usize,                                      // offset 32..40
}

/// 40 bytes of fields, padded to 48 by the 16-byte alignment above.
/// `define_static_sharedbin` emits this many bytes for the compiler-baked
/// copies, with `room` zero and the padding zero.
pub const SHARED_BIN_BYTES: usize = 48;

/// Set in `SharedBin::room` once the buffer has been made reachable from
/// another process: no one may write into it again.
const ROOM_FROZEN: usize = 1 << (usize::BITS - 1);

const _: () = {
    assert!(size_of::<SharedBin>() == SHARED_BIN_BYTES);
    assert!(align_of::<SharedBin>() == 16);
};

/// The bits of a BinRef's link word that hold its site.
const SITE_MASK: u64 = 0xF;
const _: () = assert!(StubSite::ALL.len() <= SITE_MASK as usize + 1);

/// Where a BinRef keeps its `SharedBin` pointer, in bytes from the BinRef.
pub const BINREF_SHARED_OFFSET: usize = 0;
/// Where a BinRef keeps the link to the next BinRef on its chain, in bytes from
/// the BinRef.
const BINREF_LINK_OFFSET: usize = 8;
/// Where a binary view keeps the address of its first byte, in bytes from the
/// view.
pub const BINVIEW_BYTES_PTR_OFFSET: usize = 8;
/// Where a binary view keeps the tagged pointer to its BinRef, in bytes from the
/// view.
const BINVIEW_BINREF_OFFSET: usize = 16;

impl SharedBin {
    /// Bytes the buffer can hold ahead of its trailing NUL.
    pub(crate) fn capacity(&self) -> usize {
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

// Safety: refcount is atomic; the bytes either follow the header in the one
// block the heap destructor frees, or are a static `.data` payload (noop dtor).
unsafe impl Send for SharedBin {}
unsafe impl Sync for SharedBin {}

// ===== Destructors ==========================================================

/// Final-release destructor for heap-allocated SharedBins: frees the one block
/// that holds the header and the bytes.
///
/// # Safety
/// `p` must point at a SharedBin allocated via `shared_bin_alloc` and the
/// caller must be the last live reference (refcount transition 1 → 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn shared_bin_destructor_heap(p: *mut SharedBin) {
    let size = block_size(unsafe { &*p }.capacity());
    binary_buffer_freed(size);
    unsafe { dealloc(p as *mut u8, block_layout(size)) };
}

/// Bytes of the one block a heap-backed SharedBin of `capacity` occupies: the
/// header, the capacity, and the invisible trailing NUL.
const fn block_size(capacity: usize) -> usize {
    SHARED_BIN_BYTES + capacity + 1
}

fn block_layout(size: usize) -> Layout {
    Layout::from_size_align(size, align_of::<SharedBin>()).expect("a binary block's size fits a layout")
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
/// destructor installed: one block holding the header and the bytes.
pub fn shared_bin_alloc(bytes: &[u8]) -> *mut SharedBin {
    shared_bin_alloc_with(bytes.len(), 0, |dest| {
        dest.write_copy_of_slice(bytes);
    })
}

/// Allocate a heap-backed SharedBin holding `bytes` and `spare` more bytes of
/// room for its owner to append into.
pub fn shared_bin_alloc_with_room(bytes: &[u8], spare: usize) -> *mut SharedBin {
    shared_bin_alloc_with(bytes.len(), spare, |dest| {
        dest.write_copy_of_slice(bytes);
    })
}

/// Allocate a heap-backed SharedBin of `bytes_len` bytes and `spare` more
/// bytes of room, and let `fill` write the payload straight into its block:
/// the block is the one allocation the binary owns, and nothing is staged and
/// copied in. Only the trailing NUL after the written bytes is written here;
/// the room beyond it is unwritten (filled with `UNWRITTEN_BYTE` in debug
/// builds). The trailing NUL is invisible to the language (bytes_len
/// unchanged) and underwrites the c_string extern marshal contract.
pub fn shared_bin_alloc_with(
    bytes_len: usize,
    spare: usize,
    fill: impl FnOnce(&mut [MaybeUninit<u8>]),
) -> *mut SharedBin {
    let capacity = bytes_len + spare;
    assert!(
        capacity as u64 <= BINARY_MAX_BIT_LEN / 8,
        "a binary of {capacity} bytes is longer than a header can count"
    );
    let size = block_size(capacity);
    let block = unsafe { alloc(block_layout(size)) };
    assert!(!block.is_null(), "binary block: malloc failed");
    let block = poisoned(block, size);
    let bytes = unsafe { block.add(SHARED_BIN_BYTES) };
    unsafe {
        fill(from_raw_parts_mut(bytes as *mut MaybeUninit<u8>, bytes_len));
        write(bytes.add(bytes_len), 0);
    }
    binary_buffer_allocated(size);
    let bin = block as *mut SharedBin;
    unsafe {
        write(
            bin,
            SharedBin {
                refcount: AtomicUsize::new(1),
                bytes_ptr: bytes,
                bytes_len,
                destructor: shared_bin_destructor_heap,
                room: capacity,
            },
        );
    }
    bin
}

/// Close `p`'s spare room, so no one appends into the buffer again. Called on
/// the owner's thread before a view of the buffer becomes reachable from
/// another process. A buffer with no spare room, frozen already or never
/// given any, is only read: a compiler-baked static buffer is shared by every
/// scheduler thread, and a buffer a process received is read by the sender's
/// other receivers.
///
/// # Safety
/// `p` must point at a live SharedBin, and the caller must be its owner or
/// find it with no spare room.
pub unsafe fn shared_bin_freeze(p: *mut SharedBin) {
    let bin = unsafe { &mut *p };
    if bin.spare() > 0 {
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
    unsafe { write((bin.bytes_ptr as *mut u8).add(bin.bytes_len), 0) };
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
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let p = shared_bin_alloc(bytes);
        Self(NonNull::new(p).expect("shared_bin_alloc returned null"))
    }

    /// Allocate a new heap-backed SharedBin holding `bytes` with `spare` bytes
    /// of room after them, and wrap the initial refcount.
    pub fn from_bytes_with_room(bytes: &[u8], spare: usize) -> Self {
        let p = shared_bin_alloc_with_room(bytes, spare);
        Self(NonNull::new(p).expect("shared_bin_alloc_with_room returned null"))
    }

    /// Allocate a new heap-backed SharedBin of `bytes_len` bytes that `fill`
    /// writes in place, and wrap the initial refcount.
    pub fn from_filled(bytes_len: usize, fill: impl FnOnce(&mut [MaybeUninit<u8>])) -> Self {
        let p = shared_bin_alloc_with(bytes_len, 0, fill);
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

// ===== BinRef and BinView ===================================================

/// Size of a BinRef in bytes. The single authority: allocation, GC copying and
/// `object_size` all read it here.
pub const BINREF_BYTES: usize = 16;

/// Size of the slot a binary view occupies: its 24 bytes of fields, rounded up
/// to the heap's 16-byte object granule. The single authority: allocation, GC
/// copying and `object_size` all read it here.
pub const BINVIEW_BYTES: usize = 32;

/// The one object per shared buffer per heap: it holds the heap's single
/// reference to the buffer and is the only binary object on the sweep chain.
/// `BINREF_BYTES` total:
///   offset 0..8    shared_ptr: *mut SharedBin
///   offset 8..16   off_heap_next:   u64 tagged off-heap link, or 0, with the site that
///                              made the BinRef in its low nibble
///
/// No language value is a BinRef; binary views point at it, and the collector
/// reaches it only through them. A BinRef no view reaches is dead, and the sweep
/// that finds it dead releases its reference.
///
/// Cheney forwarding overwrites offset 0 with a forwarding marker. Offset 8 is
/// preserved in from-space, so off-heap sweep reads `off_heap_next` from the old BinRef
/// and `shared_ptr` from the to-space copy if the BinRef survived.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct BinRef(NonNull<u8>);

impl BinRef {
    /// # Safety
    /// `p` must point at a live BinRef object.
    pub unsafe fn from_raw(p: *mut u8) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("BinRef::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    /// The heap object word of this BinRef: what a view stores to name it.
    pub(crate) fn word(&self) -> u64 {
        heap_object_word(self.as_raw(), ValueKind::BINREF)
    }

    pub fn shared_raw(&self) -> *mut SharedBin {
        unsafe { read(self.as_raw().add(BINREF_SHARED_OFFSET) as *const *mut SharedBin) }
    }

    fn link_word(&self) -> u64 {
        unsafe { read(self.as_raw().add(BINREF_LINK_OFFSET) as *const u64) }
    }

    /// The tagged link to the next BinRef on the chain, or 0. Heap objects are
    /// 16-byte aligned, so a link's low nibble is free: it holds the BinRef's
    /// site, which a copy of the BinRef carries along.
    pub fn off_heap_next(&self) -> u64 {
        self.link_word() & !SITE_MASK
    }

    pub(crate) fn off_heap_next_set(&self, next: u64) {
        debug_assert_eq!(next & SITE_MASK, 0, "a chain link is a 16-byte aligned heap word");
        let site = self.link_word() & SITE_MASK;
        unsafe {
            write(self.as_raw().add(BINREF_LINK_OFFSET) as *mut u64, next | site);
        }
    }

    /// What made this BinRef.
    pub fn site(&self) -> StubSite {
        StubSite::from_code((self.link_word() & SITE_MASK) as u8)
    }

    fn init(&self, shared: *mut SharedBin, site: StubSite) {
        unsafe {
            write(self.as_raw().add(BINREF_SHARED_OFFSET) as *mut *mut SharedBin, shared);
            write(
                self.as_raw().add(BINREF_LINK_OFFSET) as *mut u64,
                u64::from(site.code()),
            );
        }
    }
}

/// The object a binary value above the inline threshold points at: a
/// byte-aligned window of a `SharedBin`'s bytes, reached through its heap's
/// BinRef. `BINVIEW_BYTES` total, of which the first 24 are fields:
///   offset 0..8    header:    the window's length in bits, with the shared
///                             mark above it, exactly as a small bitstring's
///                             header holds its own (`bitstring_header_word`)
///   offset 8..16   bytes_ptr: address of the window's first byte
///   offset 16..24  binref:    u64 tagged pointer to this heap's BinRef
///
/// Both forms of a binary keep their length and shared mark in their first
/// word, so one read of it answers either, with no test of which form it is.
///
/// A view holds no reference and sits on no chain: it is an ordinary heap
/// object whose one child edge is its `binref`. A whole binary is the window at
/// the buffer's first byte spanning the buffer. Slicing allocates another view
/// over the SAME BinRef, which is what makes `<<_c, rest :: binary>>` and
/// `<<_ :: binary-size(n), field :: binary, _ :: binary>>` copy nothing and
/// retain nothing. A buffer never moves, so `bytes_ptr` stays valid for as long
/// as any view of it lives.
///
/// The buffer carries one invisible trailing NUL after its last byte. A window
/// that ends where the buffer ends (`ends_at_buffer_end`) has that NUL right
/// after it; any other window does not, and a C string over it needs a copy.
///
/// Cheney forwarding overwrites offset 0 with a forwarding marker; a live
/// header has a clear low nibble, so the two are told apart the way every
/// marker is.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct BinView(NonNull<u8>);

impl BinView {
    /// # Safety
    /// `p` must point at a live strict BinView object.
    pub unsafe fn from_raw(p: *mut u8) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("BinView::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    /// The tagged pointer to this view's BinRef.
    pub(crate) fn binref_word(&self) -> u64 {
        unsafe { read(self.as_raw().add(BINVIEW_BINREF_OFFSET) as *const u64) }
    }

    /// Point this view at `word`, a tagged pointer to a BinRef.
    pub(crate) fn binref_word_set(&self, word: u64) {
        unsafe { write(self.as_raw().add(BINVIEW_BINREF_OFFSET) as *mut u64, word) }
    }

    /// Whether this view may have a second holder, or may not own the room
    /// after its last byte.
    pub fn is_shared(&self) -> bool {
        unsafe { bitstring_is_shared(self.as_raw()) }
    }

    /// Mark this view shared. Answers whether this call marked it.
    pub fn share(&self) -> bool {
        unsafe { share_bitstring(self.as_raw()) }
    }

    /// The BinRef that holds the reference to this view's buffer.
    pub fn binref(&self) -> BinRef {
        let word = self.binref_word();
        debug_assert_eq!(heap_kind_from_tagged(word), Some(ValueKind::BINREF));
        unsafe { BinRef::from_raw(heap_word_addr(word)) }
    }

    pub fn shared_raw(&self) -> *mut SharedBin {
        self.binref().shared_raw()
    }

    pub fn bytes_ptr(&self) -> *const u8 {
        unsafe { read(self.as_raw().add(BINVIEW_BYTES_PTR_OFFSET) as *const *const u8) }
    }

    pub fn bit_len(&self) -> u64 {
        unsafe { header_bit_len(self.as_raw()) }
    }

    fn init(&self, binref: BinRef, bytes_ptr: *const u8, bit_len: u64, shared: bool) {
        let mark = if shared { BINARY_SHARED_MASK } else { 0 };
        unsafe {
            write(self.as_raw() as *mut u64, bitstring_header_word(bit_len) | mark);
            write(self.as_raw().add(BINVIEW_BYTES_PTR_OFFSET) as *mut *const u8, bytes_ptr);
            write(self.as_raw().add(BINVIEW_BINREF_OFFSET) as *mut u64, binref.word());
        }
    }

    pub fn bytes_len(&self) -> usize {
        (self.bit_len() as usize).div_ceil(8)
    }

    /// First byte of this view's window, counted from the start of its buffer.
    pub fn byte_offset(&self) -> usize {
        self.bytes_ptr() as usize - unsafe { (*self.shared_raw()).bytes_ptr } as usize
    }

    /// True when the buffer's invisible trailing NUL follows this view's last byte.
    pub fn ends_at_buffer_end(&self) -> bool {
        self.byte_offset() + self.bytes_len() == unsafe { (*self.shared_raw()).bytes_len }
    }
}

// ===== Allocation on a per-process heap =====================================

use crate::heap::{Heap, StubSite};

/// Allocate a BinRef on `heap`, taking ownership of the SharedBin reference
/// encapsulated in `handle`. The new BinRef is pushed onto `heap.off_heap_head`, the
/// young off-heap chain, as the new chain head. `site` names what is making the
/// BinRef; the heap counts it and the BinRef remembers it.
pub fn alloc_binref(heap: &mut Heap, handle: SharedBinHandle, site: StubSite) -> BinRef {
    let p = heap.alloc_at(RuntimeAllocSite::BinRef, BINREF_BYTES);
    let binref = unsafe { BinRef::from_raw(p) };
    binref.init(handle.into_raw(), site);
    heap.binrefs_made.record(site);
    let previous_head = heap.off_heap_push(binref.word());
    binref.off_heap_next_set(previous_head);
    binref
}

/// Allocate a view on `heap` of `bit_len` bits of `binref`'s buffer starting at
/// `bytes_ptr`. It takes no reference and joins no chain; `site` names what is
/// making the view, whether it is born shared, and the heap counts it.
/// A view only ever points at a BinRef of its own heap.
pub fn alloc_view(heap: &mut Heap, binref: BinRef, bytes_ptr: *const u8, bit_len: u64, site: StubSite) -> BinView {
    let shared = unsafe { &*binref.shared_raw() };
    let first = (bytes_ptr as usize).wrapping_sub(shared.bytes_ptr as usize);
    assert!(
        first.saturating_add((bit_len as usize).div_ceil(8)) <= shared.bytes_len,
        "BinView [{first}, +{bit_len} bits) lies outside the shared buffer"
    );
    let p = heap.alloc_at(RuntimeAllocSite::BinView, BINVIEW_BYTES);
    let view = unsafe { BinView::from_raw(p) };
    view.init(binref, bytes_ptr, bit_len, site.born_shared());
    heap.stubs_made.record(site);
    view
}

/// Allocate a BinRef for `handle`'s buffer and a view of its first `bit_len`
/// bits, side by side: the buffer enters the heap here. `site` names what made
/// both.
pub fn alloc_buffer_view(heap: &mut Heap, handle: SharedBinHandle, bit_len: u64, site: StubSite) -> BinView {
    let bytes_ptr = handle.bytes_ptr();
    let binref = alloc_binref(heap, handle, site);
    alloc_view(heap, binref, bytes_ptr, bit_len, site)
}

// ===== Bitstring dispatch helpers (moved from any_value.rs) ==================
//
// fz bitstrings live in one of two storage modes:
//   * `ValueKind::BITSTRING` -- inline payload: bit length at +0, bytes at +8.
//   * `ValueKind::BINVIEW` -- a BinView: bit length at +0, bytes pointer at +8.
//
// The helpers below take a heap object word, whose kind says which mode.

/// True if `word` is a heap object word whose bytes can be read as a bitstring.
pub fn is_bitstring_like(word: u64) -> bool {
    heap_kind_from_tagged(word).is_some_and(ValueKind::is_binary_repr)
}

/// The tag bit a view's kind has and an inline bitstring's lacks. Between the
/// two binary forms it alone decides, so a proven binary's form is one bit test.
const VIEW_TAG_BIT: u64 = (ValueKind::BINVIEW.tag() & !ValueKind::BITSTRING.tag()) as u64;
const _: () = assert!(
    VIEW_TAG_BIT.is_power_of_two(),
    "the binary forms differ in a view-only tag bit"
);

/// Whether a proven binary's tagged word names a view rather than an inline
/// bitstring.
#[inline]
fn names_a_view(word: u64) -> bool {
    (word >> AnyValueRefPacking::current().tag_shift()) & VIEW_TAG_BIT != 0
}

/// A binary as its bits: where they start and how many there are. Every
/// storage of a binary reads as one of these, so equality and order are
/// written once, here.
#[derive(Clone, Copy)]
pub struct Bin {
    ptr: *const u8,
    bit_len: u64,
}

impl Bin {
    pub fn new(ptr: *const u8, bit_len: u64) -> Self {
        Self { ptr, bit_len }
    }

    /// The binary a container stores as `word` with kind `kind`.
    ///
    /// # Safety
    /// `word` must name a live Bitstring or BinView, and `kind` must say
    /// which.
    #[inline]
    pub unsafe fn of_stored(word: u64, kind: ValueKind) -> Self {
        let addr = heap_word_addr(word);
        let bit_len = unsafe { header_bit_len(addr) };
        let ptr = if kind == ValueKind::BINVIEW {
            unsafe { BinView::from_raw(addr) }.bytes_ptr()
        } else {
            unsafe { bitstring_bytes_ptr(addr) }
        };
        Self::new(ptr, bit_len)
    }

    /// The binary a proven binary's tagged word names: the one decoder every
    /// runtime function that reads a binary goes through. The header holds the
    /// length in either form; only where the bytes start depends on the form.
    ///
    /// # Safety
    /// `word` must be the tagged word of a live Bitstring or BinView. The
    /// caller's declared parameter type or its own kind test proves it.
    #[inline]
    pub unsafe fn of_binary(word: u64) -> Self {
        debug_assert!(is_bitstring_like(word), "Bin::of_binary given {word:#x}, not a binary");
        let kind = if names_a_view(word) {
            ValueKind::BINVIEW
        } else {
            ValueKind::BITSTRING
        };
        unsafe { Self::of_stored(word, kind) }
    }

    /// How many bits the binary holds.
    #[inline]
    pub fn bit_len(self) -> u64 {
        self.bit_len
    }

    /// Where its first byte is.
    #[inline]
    pub fn ptr(self) -> *const u8 {
        self.ptr
    }

    /// Its bytes, for a binary of whole bytes. A partial last byte is
    /// excluded; a caller that reads one uses `bit_len` and `ptr`.
    #[inline]
    pub fn bytes<'a>(self) -> &'a [u8] {
        unsafe { from_raw_parts(self.ptr, (self.bit_len / 8) as usize) }
    }

    fn is(self, other: Bin) -> bool {
        self.ptr == other.ptr && self.bit_len == other.bit_len
    }

    /// The whole bytes among the first `bits` bits.
    fn whole_bytes(self, bits: u64) -> &'static [u8] {
        unsafe { from_raw_parts(self.ptr, (bits / 8) as usize) }
    }

    /// The bits of the byte that `bits` bits end partway through, with the
    /// padding after them cleared; zero when they end on a byte boundary.
    fn partial_byte(self, bits: u64) -> u8 {
        if bits.is_multiple_of(8) {
            return 0;
        }
        unsafe { *self.ptr.add((bits / 8) as usize) & (u8::MAX << (8 - bits % 8)) }
    }
}

/// Equal bit length, then equal bits. Lengths that differ settle it before a
/// byte is read.
impl PartialEq for Bin {
    #[inline]
    fn eq(&self, other: &Bin) -> bool {
        if self.bit_len != other.bit_len {
            return false;
        }
        self.is(*other)
            || (self.whole_bytes(self.bit_len) == other.whole_bytes(self.bit_len)
                && self.partial_byte(self.bit_len) == other.partial_byte(self.bit_len))
    }
}

impl Eq for Bin {}

/// Term order: by the bits both hold, and a prefix before what it begins.
impl Ord for Bin {
    #[inline]
    fn cmp(&self, other: &Bin) -> std::cmp::Ordering {
        if self.is(*other) {
            return std::cmp::Ordering::Equal;
        }
        let common = self.bit_len.min(other.bit_len);
        self.whole_bytes(common)
            .cmp(other.whole_bytes(common))
            .then_with(|| self.partial_byte(common).cmp(&other.partial_byte(common)))
            .then_with(|| self.bit_len.cmp(&other.bit_len))
    }
}

impl PartialOrd for Bin {
    fn partial_cmp(&self, other: &Bin) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Bytes of the buffer a bitstring-like heap value references: the whole
/// `SharedBin` for a BinView, however short the view, and the value's own
/// bytes for an inline bitstring.
///
/// # Safety
/// `word` must be the heap object word of a live Bitstring or BinView.
pub unsafe fn referenced_byte_len(word: u64) -> usize {
    let addr = heap_word_addr(word);
    if heap_kind_from_tagged(word) == Some(ValueKind::BINVIEW) {
        return unsafe { (*BinView::from_raw(addr).shared_raw()).bytes_len };
    }
    (unsafe { header_bit_len(addr) } as usize).div_ceil(8)
}

#[cfg(test)]
#[path = "bits_test.rs"]
pub(crate) mod bits_test;
