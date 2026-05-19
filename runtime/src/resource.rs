//! fz-swt.7 — refcounted off-heap opaque resource with user-supplied dtor.
//!
//! Structurally a copy of `procbin.rs`: an off-heap refcounted object
//! (`Resource`) with an on-heap 32-byte stub (`HeapKind::Resource`)
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
//! tagged FzValue, also u64-wide). Non-scalar payloads wait on
//! fz-0cv/fz-9ss FFI extensions.
//!
//! Refcount ordering uses the same canonical Arc pattern as procbin:
//! Relaxed on retain, Release on dec, Acquire fence + dtor on 1→0.
//!
//! # Lifetime contract (fz-swt.9 — interp leg)
//!
//! fz is value-semantics + immutable: an `FzValue` is a tagged 64-bit
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

use crate::fz_value::{HeapHeader, HeapKind};
use crate::sync::{AtomicUsize, Ordering, fence};
use std::ptr::NonNull;

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
    assert!(std::mem::size_of::<Resource>() == 24);
};

// Safety: refcount is atomic; payload is an opaque u64 chosen by the host
// (typically an integer fd, an FzValue, or an extern pointer). Send/Sync
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
/// is the unboxed integer carried in `payload` (a tagged `FzValue`).
/// Always exported (not `cfg(test)`) so AOT-linked fixtures can name it
/// in an `extern "C" fn` declaration and observe dtor invocation through
/// the linked binary's stdout. Stable, documented sink — usable both
/// by the in-process JIT tests (via the existing test-symbol registration
/// hook) and by AOT fixtures (via the regular extern path).
///
/// # Safety
/// `payload` must be the tagged bits of an `FzValue::Int`. Non-int
/// payloads print `dtor:?` rather than crash so a misuse stays
/// debuggable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_resource_test_print_dtor(payload: u64) {
    let v = crate::fz_value::FzValue(payload);
    match v.unbox_int() {
        Some(n) => println!("dtor:{}", n),
        None => println!("dtor:?"),
    }
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

/// fz-swt.13 — open an unnamed tmpfile and return its fd as a boxed
/// `FzValue::Int`. The path is `unlink`ed before return so the file is
/// reclaimed automatically by the OS no matter how/whether the fz-side
/// dtor fires. The returned fd is otherwise an ordinary writable fd.
///
/// Returns the tagged bits of `FzValue::from_int(fd)`, matching the
/// "extern returns are already tagged" convention used by `fz_self` and
/// every other runtime extern declared to fz as `:: integer` / `:: any`.
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

/// fz-swt.13 — resource dtor for fds produced by `fz_test_open_tmpfile`.
/// Verifies the fd is open *before* the close (catches double-close /
/// stale payload), closes it, and re-checks with `fcntl` that the
/// kernel now reports `EBADF`. Prints exactly one line:
///
///   * `dtor:closed` — every check passed.
///   * `dtor:failed(<reason>)` — at least one check failed; the reason
///     identifies which kernel call disagreed with us so a regression
///     surfaces in the golden diff rather than silently passing.
///
/// # Safety
/// `payload` must be the tagged bits of an `FzValue::Int` holding a
/// fd previously returned by `fz_test_open_tmpfile` (or any other
/// open-for-close fd). Misuse prints a diagnostic; it does not crash.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_test_close_fd(payload: u64) {
    let fd = match crate::fz_value::FzValue(payload).unbox_int() {
        Some(n) => n as libc::c_int,
        None => {
            println!("dtor:failed(payload-not-int)");
            return;
        }
    };
    // 1. Must be open before we close it.
    let pre = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    if pre == -1 {
        println!("dtor:failed(fd-already-closed)");
        return;
    }
    // 2. close() must succeed.
    let rc = unsafe { libc::close(fd) };
    if rc != 0 {
        println!(
            "dtor:failed(close-rc={},errno={})",
            rc,
            std::io::Error::last_os_error().raw_os_error().unwrap_or(0)
        );
        return;
    }
    // 3. Kernel must agree the fd is now closed.
    let post = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    let post_errno = std::io::Error::last_os_error().raw_os_error();
    if post != -1 || post_errno != Some(libc::EBADF) {
        println!(
            "dtor:failed(fd-still-open post={},errno={:?})",
            post, post_errno
        );
        return;
    }
    println!("dtor:closed");
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

// ===== ResourceStub (on-heap 40-byte stub) =================================

/// Per-heap stub referencing a `Resource`. 40 bytes total:
///   offset  0..16  HeapHeader { kind = Resource, size_bytes = 40 }
///   offset 16..24  shared_ptr:  *mut Resource     (off-heap, refcounted)
///   offset 24..32  closure_ptr: FzValue           (on-heap dtor closure;
///                                                  fz-4mk — runs as fz code
///                                                  when refcount hits zero)
///   offset 32..40  mso_next:    *mut HeapHeader   (intrusive MSO link)
///
/// Note: this layout DIVERGES from `ProcBin` (which is 32 bytes, mso_next at
/// +24). The MSO sweep dispatches on `kind` *before* reading the next-link
/// slot so each kind's accessor is used correctly.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ResourceStub(NonNull<HeapHeader>);

impl ResourceStub {
    /// # Safety
    /// `p` must point at a live HeapKind::Resource object.
    pub unsafe fn from_raw(p: *mut HeapHeader) -> Self {
        debug_assert!(!p.is_null());
        Self(NonNull::new(p).expect("ResourceStub::from_raw: null"))
    }

    pub fn as_raw(&self) -> *mut HeapHeader {
        self.0.as_ptr()
    }

    pub fn shared_raw(&self) -> *mut Resource {
        unsafe { std::ptr::read((self.as_raw() as *const u8).add(16) as *const *mut Resource) }
    }

    fn shared_raw_set(&self, p: *mut Resource) {
        unsafe {
            std::ptr::write((self.as_raw() as *mut u8).add(16) as *mut *mut Resource, p);
        }
    }

    /// fz-4mk — the dtor closure tagged FzValue. Filled in by
    /// `alloc_resource` and traced by Cheney like any other heap edge.
    pub fn closure_ptr(&self) -> crate::fz_value::FzValue {
        unsafe {
            std::ptr::read((self.as_raw() as *const u8).add(24) as *const crate::fz_value::FzValue)
        }
    }

    pub(crate) fn closure_ptr_set(&self, v: crate::fz_value::FzValue) {
        unsafe {
            std::ptr::write(
                (self.as_raw() as *mut u8).add(24) as *mut crate::fz_value::FzValue,
                v,
            );
        }
    }

    pub fn mso_next(&self) -> *mut HeapHeader {
        unsafe { std::ptr::read((self.as_raw() as *const u8).add(32) as *const *mut HeapHeader) }
    }

    pub(crate) fn mso_next_set(&self, next: *mut HeapHeader) {
        unsafe {
            std::ptr::write(
                (self.as_raw() as *mut u8).add(32) as *mut *mut HeapHeader,
                next,
            );
        }
    }

    pub fn payload(&self) -> u64 {
        unsafe { (*self.shared_raw()).payload }
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

/// Allocate a 40-byte Resource stub on `heap`, taking ownership of the
/// Resource reference encapsulated in `handle`. `closure` is the dtor
/// closure value — recorded for fz-4mk's deferred fz-side dispatch. The
/// new stub is pushed onto `heap.mso_head` as the new chain head.
pub fn alloc_resource(
    heap: &mut Heap,
    handle: ResourceHandle,
    closure: crate::fz_value::FzValue,
) -> ResourceStub {
    let p = heap.alloc(40);
    unsafe {
        std::ptr::write(
            p,
            HeapHeader {
                kind: HeapKind::Resource as u16,
                flags: 0,
                size_bytes: 40,
                schema_id: 0,
                _reserved: 0,
            },
        );
    }
    let rs = unsafe { ResourceStub::from_raw(p) };
    rs.closure_ptr_set(closure);
    rs.shared_raw_set(handle.into_raw());
    rs.mso_next_set(heap.mso_head);
    heap.mso_head = p;
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
    fn resource_is_24_bytes() {
        assert_eq!(std::mem::size_of::<Resource>(), 24);
    }

    #[test]
    #[serial_test::serial]
    fn alloc_retain_release_pattern() {
        let _g = LiveCountGuard::snap();
        reset_counters();
        let p = resource_alloc(42, counting_dtor);
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
        let p = resource_alloc(0xdeadbeef, counting_dtor);
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
            let _h = ResourceHandle::new(99, counting_dtor);
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
        let h = ResourceHandle::new(7, counting_dtor);
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
        let p = resource_alloc(123, fz_resource_destructor_noop);
        unsafe { fz_resource_release(p) };
    }

    #[test]
    #[serial_test::serial]
    fn alloc_resource_pushes_into_mso_chain() {
        let g = LiveCountGuard::snap();
        reset_counters();
        {
            let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
            let handle = ResourceHandle::new(0xabcd, counting_dtor);
            let rs = alloc_resource(&mut h, handle, crate::fz_value::FzValue::NIL);
            assert_eq!(unsafe { (*rs.as_raw()).kind }, HeapKind::Resource as u16);
            assert_eq!(unsafe { (*rs.as_raw()).size_bytes }, 40);
            assert_eq!(h.mso_head, rs.as_raw());
            assert_eq!(rs.mso_next(), std::ptr::null_mut());
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
            ResourceHandle::new(0x55, counting_dtor),
            crate::fz_value::FzValue::NIL,
        );
        let mut root: *mut u8 = std::ptr::null_mut();
        h.gc(&mut root);
        assert!(h.mso_head.is_null(), "dead Resource swept from MSO");
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 1);
        assert_eq!(
            DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed),
            0x55
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
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[1, 2, 3], 24));
            let _ = alloc_resource(
                &mut h,
                ResourceHandle::new(0xfeed, counting_dtor),
                crate::fz_value::FzValue::NIL,
            );
            let _ = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[4, 5], 16));
            let _ = alloc_resource(
                &mut h,
                ResourceHandle::new(0xbeef, counting_dtor),
                crate::fz_value::FzValue::NIL,
            );
        }
        // Both resources fired their dtors exactly once each.
        assert_eq!(DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed), 2);
    }
}
