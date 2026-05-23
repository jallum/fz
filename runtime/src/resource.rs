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
//! FFI constraint for v0: payload must fit in u64. That covers every
//! existing `ExternTy` variant (I64/F64/Any/Unit/Never — Any is a
//! tagged value word, also u64-wide). Non-scalar payloads wait on
//! fz-0cv/fz-9ss FFI extensions.
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
//! retain — are exactly those where `Heap::deep_copy_value` runs:
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

use crate::sync::{AtomicUsize, Ordering, fence};
use std::ptr::NonNull;

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
    pub payload_kind: u8,                               // offset 24..25
}

const _: () = {
    assert!(std::mem::size_of::<Resource>() == 32);
};

// Safety: refcount is atomic; payload is an opaque u64 chosen by the host
// (typically an integer fd, a tagged fz value, or an extern pointer). Send/Sync
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
/// is the integer carried in `payload`.
/// Always exported (not `cfg(test)`) so AOT-linked fixtures can name it
/// in an `extern "C" fn` declaration and observe dtor invocation through
/// the linked binary's stdout. Stable, documented sink — usable both
/// by the in-process JIT tests (via the existing test-symbol registration
/// hook) and by AOT fixtures (via the regular extern path).
///
/// # Safety
/// `payload` must be the raw integer payload because the fixture routes this
/// helper through the typed/raw extern path.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_test_print_dtor(payload: u64) {
    println!("dtor:{}", payload as i64);
}

// ===== fz-swt.13: File-module test helpers =================================
//
// These exist so the `file_resource_lifecycle` fixture can prove the
// resource dtor mechanism really closes a real Unix fd in all three
// paths (interp/JIT/AOT) without taking on the cstring/binary FFI work
// blocked behind fz-wu9 + fz-0cv. They are NOT a public stdlib surface:
// `File.open(path, mode)` is the v1 entry point and lands once those
// tickets ship.
//
// All three live in the runtime crate (same as `fz_resource_test_print_dtor`)
// so AOT-linked binaries can name them directly via `extern "C"`, the JIT
// can resolve them through the symbol table installed in
// `src/ir_codegen.rs::setup_runtime_module`, and the interpreter reaches
// them through the native table in `src/ir_interp.rs::resolve_symbol`.

/// fz-swt.13 — open an unnamed tmpfile and return its fd as a raw integer. The path is
/// reclaimed automatically by the OS no matter how/whether the fz-side
/// dtor fires. The returned fd is otherwise an ordinary writable fd.
///
/// # Safety
/// Spawns a real fd; the caller is expected to eventually close it.
/// Aborts on `mkstemp`/`unlink` failure — the fixture has no recovery
/// path and silent leaks would defeat the test's purpose.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_test_open_tmpfile() -> u64 {
    use std::ffi::CString;
    // `mkstemp` mutates its template buffer in place; the template must
    // be writable and outlive the call. Use a fixed prefix in $TMPDIR
    // (or /tmp) — the file is unlinked immediately so the name doesn't
    // matter.
    let dir = std::env::temp_dir();
    let template = dir.join("fz_swt13_XXXXXX");
    let template_bytes = template.to_string_lossy().into_owned();
    let cstr = CString::new(template_bytes).expect("fz_test_open_tmpfile: bad template");
    let mut buf: Vec<libc::c_char> = cstr
        .as_bytes_with_nul()
        .iter()
        .map(|&b| b as libc::c_char)
        .collect();
    let fd = unsafe { libc::mkstemp(buf.as_mut_ptr()) };
    if fd < 0 {
        panic!(
            "fz_test_open_tmpfile: mkstemp failed: {}",
            std::io::Error::last_os_error()
        );
    }
    // Unlink immediately; the fd stays valid until closed.
    if unsafe { libc::unlink(buf.as_ptr()) } != 0 {
        // Already-open fd will outlive a failed unlink, but a leaked
        // pathname on disk would surface as test flakiness. Abort.
        panic!(
            "fz_test_open_tmpfile: unlink failed: {}",
            std::io::Error::last_os_error()
        );
    }
    // fz-rb8 — `:: integer` returns raw i64; the runtime boxes on receive.
    // Cast through u64 to preserve the bit pattern (fds are non-negative).
    fd as u64
}

// ===== Allocation + refcount primitives ====================================

/// Allocate a fresh `Resource` with refcount = 1 carrying `payload` and
/// `dtor`. Returns the raw pointer; caller owns one refcount edge.
pub fn resource_alloc(
    payload: u64,
    payload_kind: u8,
    dtor: unsafe extern "C" fn(u64),
) -> *mut Resource {
    let r = Box::new(Resource {
        refcount: AtomicUsize::new(1),
        destructor: dtor,
        payload,
        payload_kind,
    });
    LIVE_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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
        LIVE_COUNT.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
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
pub unsafe fn fz_resource_release_deferred(p: *mut Resource) -> Option<(u64, u8)> {
    debug_assert!(!p.is_null());
    let r = unsafe { &*p };
    if r.refcount.fetch_sub(1, Ordering::Release) == 1 {
        fence(Ordering::Acquire);
        let payload = r.payload;
        let payload_kind = r.payload_kind;
        let _wrapper = unsafe { Box::from_raw(p) };
        #[cfg(not(loom))]
        LIVE_COUNT.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
        Some((payload, payload_kind))
    } else {
        None
    }
}

// ===== Live-count gauge =====================================================

static LIVE_COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Number of currently-live heap-allocated Resource objects.
#[cfg(test)]
pub(crate) fn live_count() -> usize {
    LIVE_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}

// ===== ResourceHandle =======================================================

/// Owning handle to a Resource. `Drop` releases. `Clone` retains.
pub struct ResourceHandle(NonNull<Resource>);

impl ResourceHandle {
    /// Allocate a new heap-backed Resource and wrap the initial refcount.
    pub fn new(payload: u64, payload_kind: u8, dtor: unsafe extern "C" fn(u64)) -> Self {
        let p = resource_alloc(payload, payload_kind, dtor);
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
        std::mem::forget(self);
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
        unsafe { std::ptr::read(self.as_raw() as *const *mut Resource) }
    }

    fn shared_raw_set(&self, p: *mut Resource) {
        unsafe {
            std::ptr::write(self.as_raw() as *mut *mut Resource, p);
        }
    }

    /// fz-4mk — the dtor closure value. Filled in by `alloc_resource` and
    /// traced by Cheney like any other heap edge.
    pub fn closure_value(&self) -> crate::fz_value::FzValue {
        let raw = unsafe {
            std::ptr::read(self.as_raw().add(RESOURCE_STUB_CLOSURE_RAW_OFFSET) as *const u64)
        };
        let kind = unsafe {
            std::ptr::read(self.as_raw().add(RESOURCE_STUB_CLOSURE_KIND_OFFSET) as *const u8)
        };
        crate::fz_value::FzValue::decode_parts(raw, kind).expect("resource closure kind")
    }

    pub(crate) fn closure_value_set(&self, value: crate::fz_value::FzValue) {
        let raw = if value.kind().is_heap() {
            value.raw() & !crate::fz_value::TAG_MASK
        } else {
            value.raw()
        };
        unsafe {
            std::ptr::write(
                self.as_raw().add(RESOURCE_STUB_CLOSURE_RAW_OFFSET) as *mut u64,
                raw,
            );
            std::ptr::write(
                self.as_raw().add(RESOURCE_STUB_CLOSURE_KIND_OFFSET),
                value.kind().tag(),
            );
        }
    }

    pub fn mso_next(&self) -> u64 {
        unsafe { std::ptr::read(self.as_raw().add(RESOURCE_STUB_MSO_NEXT_OFFSET) as *const u64) }
    }

    pub(crate) fn mso_next_set(&self, next: u64) {
        unsafe {
            std::ptr::write(
                self.as_raw().add(RESOURCE_STUB_MSO_NEXT_OFFSET) as *mut u64,
                next,
            );
        }
    }

    pub fn payload(&self) -> u64 {
        unsafe { (*self.shared_raw()).payload }
    }

    pub fn payload_kind(&self) -> u8 {
        unsafe { (*self.shared_raw()).payload_kind }
    }

    pub fn payload_value(&self) -> crate::fz_value::FzValue {
        crate::fz_value::FzValue::decode_parts(self.payload(), self.payload_kind())
            .expect("resource payload kind")
    }

    pub fn destructor(&self) -> unsafe extern "C" fn(u64) {
        unsafe { (*self.shared_raw()).destructor }
    }

    pub fn refcount(&self) -> usize {
        unsafe { (*self.shared_raw()).refcount.load(Ordering::Relaxed) }
    }
}

// ===== Allocation on a per-process heap =====================================

use crate::heap::Heap;

/// Allocate a strict 32-byte Resource stub on `heap`, taking ownership of the
/// Resource reference encapsulated in `handle`. `closure` is the dtor
/// closure value — recorded for fz-4mk's deferred fz-side dispatch. The
/// new stub is pushed onto `heap.mso_head` as the new chain head.
pub fn alloc_resource(
    heap: &mut Heap,
    handle: ResourceHandle,
    closure: crate::fz_value::FzValue,
) -> ResourceStub {
    let p = heap.alloc(RESOURCE_STUB_SIZE);
    let rs = unsafe { ResourceStub::from_raw(p) };
    rs.shared_raw_set(handle.into_raw());
    unsafe {
        std::ptr::write(
            p.add(RESOURCE_STUB_MAGIC_OFFSET) as *mut u64,
            RESOURCE_STUB_MAGIC,
        );
    }
    rs.closure_value_set(closure);
    rs.mso_next_set(heap.mso_head);
    heap.mso_head = crate::fz_value::tagged_resource_bits(p);
    rs
}

// ===== Tests ================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

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

    static DTOR_FIRED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    static DTOR_LAST_PAYLOAD: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

    unsafe extern "C" fn counting_dtor(payload: u64) {
        DTOR_FIRED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        DTOR_LAST_PAYLOAD.store(payload, std::sync::atomic::Ordering::Relaxed);
    }

    fn reset_counters() {
        DTOR_FIRED.store(0, std::sync::atomic::Ordering::Relaxed);
        DTOR_LAST_PAYLOAD.store(0, std::sync::atomic::Ordering::Relaxed);
    }

    #[test]
    fn resource_is_32_bytes() {
        assert_eq!(std::mem::size_of::<Resource>(), 32);
    }

    #[test]
    #[serial_test::serial]
    fn alloc_retain_release_pattern() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let p = resource_alloc(42, crate::fz_value::ValueKind::INT.tag(), counting_dtor);
        unsafe {
            fz_resource_retain(p);
            fz_resource_retain(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
            fz_resource_release(p);
            fz_resource_release(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
            assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 0);
            fz_resource_release(p);
        }
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            42
        );
    }

    #[test]
    #[serial_test::serial]
    fn alloc_release_immediately_fires_dtor() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let p = resource_alloc(
            0xdeadbeef,
            crate::fz_value::ValueKind::INT.tag(),
            counting_dtor,
        );
        unsafe { fz_resource_release(p) };
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            0xdeadbeef
        );
    }

    #[test]
    #[serial_test::serial]
    fn handle_drop_releases() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        {
            let _h = ResourceHandle::new(99, crate::fz_value::ValueKind::INT.tag(), counting_dtor);
            assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 0);
        }
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            99
        );
    }

    #[test]
    #[serial_test::serial]
    fn handle_clone_balanced_drops_fire_once() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let h = ResourceHandle::new(7, crate::fz_value::ValueKind::INT.tag(), counting_dtor);
        let h2 = h.clone();
        assert_eq!(unsafe { (*h.as_raw()).refcount.load(Ordering::Relaxed) }, 2);
        drop(h);
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 0);
        drop(h2);
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            7
        );
    }

    #[test]
    #[serial_test::serial]
    fn noop_dtor_is_safe() {
        let _g = LiveCountGuard::snap();
        let p = resource_alloc(
            123,
            crate::fz_value::ValueKind::INT.tag(),
            fz_resource_destructor_noop,
        );
        unsafe { fz_resource_release(p) };
    }

    #[test]
    #[serial_test::serial]
    fn alloc_resource_pushes_into_mso_chain() {
        let g = LiveCountGuard::snap();
        reset_counters();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let handle =
                ResourceHandle::new(0xabcd, crate::fz_value::ValueKind::INT.tag(), counting_dtor);
            let rs = alloc_resource(&mut h, handle, crate::fz_value::FzValue::nil_atom());
            let tagged = crate::fz_value::tagged_resource_bits(rs.as_raw() as *const u8);
            assert_eq!(
                tagged & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_RESOURCE
            );
            assert_eq!(crate::fz_value::object_size(tagged), RESOURCE_STUB_SIZE);
            assert_eq!(h.mso_head, tagged);
            assert_eq!(rs.mso_next(), 0);
            assert_eq!(rs.payload(), 0xabcd);
            assert_eq!(rs.refcount(), 1);
            assert_eq!(live_count(), g.baseline() + 1);
        }
        // Heap::drop -> mso_drop_all -> fz_resource_release -> dtor fires.
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            0xabcd
        );
    }

    /// Force a GC with no root: the Resource stub becomes unreachable;
    /// MSO sweep must invoke the dtor exactly once and clear the chain.
    #[test]
    #[serial_test::serial]
    fn unrooted_resource_dies_in_gc_and_sweep_fires_dtor() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let _ = alloc_resource(
            &mut h,
            ResourceHandle::new(0x55, crate::fz_value::ValueKind::INT.tag(), counting_dtor),
            crate::fz_value::FzValue::nil_atom(),
        );
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert_eq!(h.mso_head, 0, "dead Resource swept from MSO");
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            0x55
        );
    }

    /// A rooted strict Resource survives Cheney and rewrites the MSO chain to
    /// its to-space copy without firing the destructor during GC.
    #[test]
    #[serial_test::serial]
    fn resource_forwarding_marker_through_gc() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
        let rs = alloc_resource(
            &mut h,
            ResourceHandle::new(0x66, crate::fz_value::ValueKind::INT.tag(), counting_dtor),
            crate::fz_value::FzValue::nil_atom(),
        );
        let from = rs.as_raw();
        let mut root = crate::fz_value::tagged_resource_bits(from as *const u8) as *mut u8;
        h.gc(&mut root);

        let to = crate::fz_value::resource_addr_from_tagged(root as u64).unwrap();
        assert_ne!(to, from);
        assert_eq!(
            h.mso_head,
            crate::fz_value::tagged_resource_bits(to as *const u8)
        );
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 0);
        drop(h);
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            0x66
        );
    }

    /// Mixed chain: ProcBin and Resource on the same heap. Both kinds
    /// must be swept correctly when the heap is dropped.
    #[test]
    #[serial_test::serial]
    fn mixed_mso_chain_with_procbin_and_resource() {
        use crate::procbin::{SharedBinHandle, alloc_procbin};
        let _g = LiveCountGuard::snap();
        reset_counters();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let pb1 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2, 3], 24));
            let rs1 = alloc_resource(
                &mut h,
                ResourceHandle::new(0xfeed, crate::fz_value::ValueKind::INT.tag(), counting_dtor),
                crate::fz_value::FzValue::nil_atom(),
            );
            let pb2 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[4, 5], 16));
            let rs2 = alloc_resource(
                &mut h,
                ResourceHandle::new(0xbeef, crate::fz_value::ValueKind::INT.tag(), counting_dtor),
                crate::fz_value::FzValue::nil_atom(),
            );
            let rs2_bits = crate::fz_value::tagged_resource_bits(rs2.as_raw() as *const u8);
            let pb2_bits = crate::fz_value::tagged_procbin_bits(pb2.as_raw() as *const u8);
            let pb1_bits = crate::fz_value::tagged_procbin_bits(pb1.as_raw() as *const u8);
            let rs1_bits = crate::fz_value::tagged_resource_bits(rs1.as_raw() as *const u8);
            assert_eq!(h.mso_head, rs2_bits);
            assert_eq!(rs2.mso_next(), pb2_bits);
            assert_eq!(pb2.mso_next(), rs1_bits);
            assert_eq!(rs1.mso_next(), pb1_bits);
            assert_eq!(
                pb2.mso_next() & crate::fz_value::TAG_MASK,
                crate::fz_value::TAG_RESOURCE
            );
            assert_eq!(pb1.mso_next(), 0);
        }
        // Both resources fired their dtors exactly once each.
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 2);
    }
}
