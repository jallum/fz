//! fz-swt.7 — refcounted off-heap opaque resource with user-supplied dtor.
//!
//! Structurally a copy of `procbin.rs`: an off-heap refcounted object
//! (`Resource`) with an on-heap strict tagged stub (`TAG_RESOURCE`)
//! threaded into the per-heap intrusive MSO chain. The MSO sweep handles
//! retain/release across GC exactly the same way it does for ProcBin.
//!
//! Divergence from `SharedBin`/`ProcBin`:
//!   * The dtor is **user-supplied at allocation time**, not one of two
//!     fixed dtors. Every Resource carries its own
//!     `unsafe extern "C" fn(payload: u64)` pointer.
//!   * The dtor receives the **payload only**, not the wrapper. The
//!     runtime frees the wrapper (Box::from_raw drop) after the dtor
//!     returns. This keeps fz-side externs ergonomic
//!     (`extern fn fd_close(integer)` rather than wrapping/unwrapping).
//!
//! FFI constraint for v0: payload is a raw 64-bit integer handle. That
//! covers fd-like resources today and leaves room for an opaque pointer
//! type later without teaching Resource about fz value kinds.
//!
//! Refcount ordering uses the same canonical Arc pattern as procbin:
//! Relaxed on retain, Release on dec, Acquire fence + dtor on 1→0.
//!
//! # Lifetime contract (fz-swt.9 — interp leg)
//!
//! fz is value-semantics + immutable: a heap handle is a tagged 64-bit
//! word. Let-binding a resource handle (`r2 = r1`) copies the tag bits;
//! both names refer to the *same* on-heap stub, which holds exactly one
//! edge to the off-heap `Resource`. No per-binding retain is needed —
//! the MSO chain pins the stub for as long as its owning heap is alive.
//!
//! Ownership boundaries — points where the runtime *does* need to
//! retain — are exactly those where `Heap::deep_copy_slot` runs:
//!   * `send/2` from one process to another (handled at heap.rs:1308).
//!   * `spawn/1` capturing a resource into the child's heap.
//!
//! Both go through `ResourceHandle::retain_from_raw` + `alloc_resource`
//! in the destination heap, producing a second stub that holds its own
//! refcount edge. Aliasing inside a single process does **not** cross a
//! boundary and so does **not** retain.
//!
//! Release happens via the per-heap MSO sweep (post-Cheney for live
//! processes; `mso_drop_all` at heap drop). On 1→0 we run the user dtor
//! exactly once with the stored payload and free the wrapper. The dtor
//! therefore fires:
//!   * when the owning process exits and its heap is dropped, or
//!   * earlier if a GC sweep finds the stub unreachable from the roots.
//!
//! For the interpreter today (no incremental GC of live processes), the
//! practical observation is "at process heap drop." Multiple aliases
//! within a process collapse to a single 1→0 transition — the dtor
//! fires exactly once per `make_resource` call, regardless of aliasing.

use crate::any_value::{AnyValue, TAG_MASK, ValueKind, heap_object_word};
#[cfg(test)]
use crate::any_value::{TAG_RESOURCE, object_size, resource_addr_from_tagged};
use crate::heap::{Heap, HeapAllocKind};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::mem::{forget, size_of};
#[cfg(test)]
use std::ptr::null_mut;
use std::ptr::{NonNull, addr_of, read, write};

pub(crate) const RESOURCE_STUB_MAGIC: u64 = 0xF75E_5012_CE57_0B0B;

// ===== Resource layout ======================================================

/// Off-heap refcounted resource. `refcount` controls lifetime; `destructor`
/// is invoked exactly once with `payload` when the refcount transitions to
/// zero. The runtime frees the wrapper itself after the dtor returns.
#[repr(C)]
pub struct Resource {
    pub refcount: AtomicUsize,                          // offset 0..8
    pub destructor: unsafe extern "C" fn(payload: u64), // offset 8..16
    pub payload: u64,                                   // offset 16..24
}

const _: () = {
    assert!(size_of::<Resource>() == 24);
};

// Safety: refcount is atomic; payload is an opaque u64 chosen by the host
// (typically an integer fd or, later, an extern pointer). Send/Sync
// liveness is the host author's responsibility — NIF-style trust model.
unsafe impl Send for Resource {}
unsafe impl Sync for Resource {}

// ===== Built-in dtors =======================================================

/// No-op destructor. Useful as a sentinel for tests and for callers who
/// want a Resource whose payload requires no cleanup.
///
/// # Safety
/// `_payload` is unused; signature matches the `destructor` field type.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_destructor_noop(_payload: u64) {}

/// fz-swt.11 — test/fixture dtor: prints `dtor:<n>` to stdout where `n`
/// is the raw integer payload.
/// Always exported (not `cfg(test)`) so AOT-linked fixtures can name it
/// in an `extern "C" fn` declaration and observe dtor invocation through
/// the linked binary's stdout. Stable, documented sink — usable both
/// by the in-process JIT tests (via the existing test-symbol registration
/// hook) and by AOT fixtures (via the regular extern path).
///
/// # Safety
/// `payload` must be the integer originally passed to `make_resource`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_test_print_dtor(payload: u64) {
    println!("dtor:{}", payload as i64);
}

// ===== Allocation + refcount primitives ====================================

/// Allocate a fresh `Resource` with refcount = 1 carrying `payload` and
/// `dtor`. Returns the raw pointer; caller owns one refcount edge.
pub fn resource_alloc(payload: u64, dtor: unsafe extern "C" fn(u64)) -> *mut Resource {
    let r = Box::new(Resource {
        refcount: AtomicUsize::new(1),
        destructor: dtor,
        payload,
    });
    LIVE_COUNT.fetch_add(1, Ordering::Relaxed);
    Box::into_raw(r)
}

/// Increment the refcount on an already-owned Resource.
///
/// # Safety
/// `p` must point at a live Resource (refcount > 0).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_retain(p: *mut Resource) {
    debug_assert!(!p.is_null());
    let r = unsafe { &*p };
    let old = r.refcount.fetch_add(1, Ordering::Relaxed);
    debug_assert!(old < usize::MAX / 2, "Resource refcount overflow");
}

/// Decrement the refcount and run the destructor + free the wrapper if
/// this was the last reference. Release ordering on the decrement;
/// Acquire fence on final drop synchronises with every other releaser.
///
/// # Safety
/// `p` must point at a live Resource. After calling, the caller must not
/// dereference `p` again.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_release(p: *mut Resource) {
    debug_assert!(!p.is_null());
    let r = unsafe { &*p };
    if r.refcount.fetch_sub(1, Ordering::Release) == 1 {
        fence(Ordering::Acquire);
        let dtor = r.destructor;
        let payload = r.payload;
        // SAFETY: refcount went 1 → 0, so we own the unique reference.
        // Reconstruct the Box BEFORE invoking the dtor so the wrapper is
        // reclaimed even if the dtor panics (Box::from_raw drop is in the
        // scope; we've already snapshotted payload/dtor above).
        let _wrapper = unsafe { Box::from_raw(p) };
        unsafe { dtor(payload) };
        #[cfg(not(loom))]
        LIVE_COUNT.fetch_sub(1, Ordering::Relaxed);
    }
}

/// fz-4mk — release variant for the deferred-dispatch path.
///
/// Decrements the refcount, frees the wrapper if this was the final ref,
/// and returns the payload (so the caller can enqueue it onto a per-heap
/// `pending_dtors` queue for fz-side dispatch later). Does **not** invoke
/// the stored C destructor — the new contract is "the closure runs the
/// dtor as fz code at the next scheduler boundary."
///
/// Returns `Some(payload)` on the final-ref transition (1 → 0), `None`
/// otherwise (another stub still holds the resource alive).
///
/// # Safety
/// `p` must point at a live Resource. After `Some(_)` returns the caller
/// must not dereference `p` again — the wrapper has been freed.
pub unsafe fn fz_resource_release_deferred(p: *mut Resource) -> Option<u64> {
    debug_assert!(!p.is_null());
    let r = unsafe { &*p };
    if r.refcount.fetch_sub(1, Ordering::Release) == 1 {
        fence(Ordering::Acquire);
        let payload = r.payload;
        let _wrapper = unsafe { Box::from_raw(p) };
        #[cfg(not(loom))]
        LIVE_COUNT.fetch_sub(1, Ordering::Relaxed);
        Some(payload)
    } else {
        None
    }
}

// ===== Live-count gauge =====================================================

static LIVE_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Number of currently-live heap-allocated Resource objects.
#[cfg(test)]
pub(crate) fn live_count() -> usize {
    LIVE_COUNT.load(Ordering::Relaxed)
}

// ===== ResourceHandle =======================================================

/// Owning handle to a Resource. `Drop` releases. `Clone` retains.
pub struct ResourceHandle(NonNull<Resource>);

impl ResourceHandle {
    /// Allocate a new heap-backed Resource and wrap the initial refcount.
    pub fn new(payload: u64, dtor: unsafe extern "C" fn(u64)) -> Self {
        let p = resource_alloc(payload, dtor);
        Self(NonNull::new(p).expect("resource_alloc returned null"))
    }

    /// Retain `p` and wrap the new reference.
    ///
    /// # Safety
    /// `p` must point at a live Resource.
    pub unsafe fn retain_from_raw(p: *mut Resource) -> Self {
        unsafe { fz_resource_retain(p) };
        Self(NonNull::new(p).expect("retain_from_raw: null ptr"))
    }

    /// Wrap `p` without retaining. Caller transfers their existing
    /// refcount edge to the handle.
    ///
    /// # Safety
    /// `p` must point at a live Resource; caller must own exactly one
    /// refcount edge that they relinquish to the handle.
    pub unsafe fn from_raw_already_retained(p: *mut Resource) -> Self {
        Self(NonNull::new(p).expect("from_raw_already_retained: null ptr"))
    }

    pub fn as_raw(&self) -> *mut Resource {
        self.0.as_ptr()
    }

    /// Consume the handle without releasing. The caller now owns one
    /// refcount edge represented by the returned pointer.
    pub fn into_raw(self) -> *mut Resource {
        let p = self.0.as_ptr();
        forget(self);
        p
    }
}

impl Clone for ResourceHandle {
    fn clone(&self) -> Self {
        unsafe { Self::retain_from_raw(self.as_raw()) }
    }
}

impl Drop for ResourceHandle {
    fn drop(&mut self) {
        unsafe { fz_resource_release(self.as_raw()) };
    }
}

// ===== ResourceStub (on-heap strict tagged stub) ============================

const RESOURCE_STUB_SIZE: usize = 48;
const RESOURCE_STUB_MAGIC_OFFSET: usize = 8;
const RESOURCE_STUB_CLOSURE_RAW_OFFSET: usize = 16;
const RESOURCE_STUB_CLOSURE_KIND_OFFSET: usize = 24;
const RESOURCE_STUB_MSO_NEXT_OFFSET: usize = 32;

/// Per-heap stub referencing a `Resource`. The live payload is 40 bytes,
/// allocated as 48 bytes to preserve the heap's 16-byte object alignment:
///   offset  0..8   shared_ptr:  *mut Resource     (off-heap, refcounted)
///   offset  8..16  resource tag magic             (MSO discriminator)
///   offset 16..24  closure raw word               (on-heap dtor closure)
///   offset 24..25  closure kind byte              (object-local metadata)
///   offset 25..32  padding
///   offset 32..40  mso_next:    u64 tagged MSO link, or 0
///   offset 40..48  padding
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ResourceStub(NonNull<u8>);

impl ResourceStub {
    /// # Safety
    /// `p` must point at a live strict Resource object.
    pub unsafe fn from_raw(p: *mut u8) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("ResourceStub::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    pub fn shared_raw(&self) -> *mut Resource {
        unsafe { read(self.as_raw() as *const *mut Resource) }
    }

    fn shared_raw_set(&self, p: *mut Resource) {
        unsafe {
            write(self.as_raw() as *mut *mut Resource, p);
        }
    }

    /// fz-4mk — the dtor closure value. Filled in by `alloc_resource` and
    /// traced by Cheney like any other heap edge.
    pub fn closure_value(&self) -> AnyValue {
        let raw = unsafe { read(self.as_raw().add(RESOURCE_STUB_CLOSURE_RAW_OFFSET) as *const u64) };
        let kind = unsafe { read(self.as_raw().add(RESOURCE_STUB_CLOSURE_KIND_OFFSET) as *const u8) };
        AnyValue::decode_parts(raw, kind).expect("resource closure kind")
    }

    pub(crate) fn closure_value_set(&self, value: AnyValue) {
        let raw = if value.kind().is_heap() {
            value.raw() & !TAG_MASK
        } else {
            value.raw()
        };
        unsafe {
            write(self.as_raw().add(RESOURCE_STUB_CLOSURE_RAW_OFFSET) as *mut u64, raw);
            write(self.as_raw().add(RESOURCE_STUB_CLOSURE_KIND_OFFSET), value.kind().tag());
        }
    }

    pub fn mso_next(&self) -> u64 {
        unsafe { read(self.as_raw().add(RESOURCE_STUB_MSO_NEXT_OFFSET) as *const u64) }
    }

    pub(crate) fn mso_next_set(&self, next: u64) {
        unsafe {
            write(self.as_raw().add(RESOURCE_STUB_MSO_NEXT_OFFSET) as *mut u64, next);
        }
    }

    pub fn payload(&self) -> u64 {
        unsafe { (*self.shared_raw()).payload }
    }

    pub fn payload_slot(&self) -> *const u64 {
        unsafe { addr_of!((*self.shared_raw()).payload) }
    }

    pub fn payload_value(&self) -> AnyValue {
        AnyValue::int(self.payload() as i64)
    }

    pub fn destructor(&self) -> unsafe extern "C" fn(u64) {
        unsafe { (*self.shared_raw()).destructor }
    }

    pub fn refcount(&self) -> usize {
        unsafe { (*self.shared_raw()).refcount.load(Ordering::Relaxed) }
    }
}

// ===== Allocation on a per-process heap =====================================

/// Allocate a strict 48-byte Resource stub on `heap`, taking ownership of the
/// Resource reference encapsulated in `handle`. `closure` is the dtor
/// closure value — recorded for fz-4mk's deferred fz-side dispatch. The
/// new stub is pushed onto `heap.mso_head` as the new chain head.
pub fn alloc_resource(heap: &mut Heap, handle: ResourceHandle, closure: AnyValue) -> ResourceStub {
    let p = heap.alloc_kind(HeapAllocKind::Resource, RESOURCE_STUB_SIZE);
    let rs = unsafe { ResourceStub::from_raw(p) };
    rs.shared_raw_set(handle.into_raw());
    unsafe {
        write(p.add(RESOURCE_STUB_MAGIC_OFFSET) as *mut u64, RESOURCE_STUB_MAGIC);
    }
    rs.closure_value_set(closure);
    rs.mso_next_set(heap.mso_head);
    heap.mso_head = heap_object_word(p, ValueKind::RESOURCE);
    rs
}

// ===== Tests ================================================================

#[cfg(test)]
#[path = "resource_test.rs"]
mod resource_test;
