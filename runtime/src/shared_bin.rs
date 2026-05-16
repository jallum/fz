//! fz-cty.2 — refcounted off-heap binary store.
//!
//! Each `SharedBin` is its own `Box`-allocated object whose lifetime is
//! governed by an atomic refcount. There is no global registry and no
//! mutex: concurrent allocation goes through the system allocator, and
//! concurrent retain/release uses the canonical Arc pattern (Relaxed on
//! retain, Release on release, Acquire fence on the final drop).
//!
//! The bins live outside any process heap. They are referenced from
//! per-process heaps via small `ProcBin` stubs (added in fz-cty.3); the
//! Cheney trace ignores their pointers because they fall outside every
//! per-heap arena range. Tracking which heaps still hold a reference is
//! the job of each heap's MSO list (also fz-cty.3) — this module just
//! owns the bin and its refcount.

use std::sync::atomic::{AtomicUsize, Ordering, fence};

/// Off-heap refcounted binary. Holds a heap-allocated byte buffer plus
/// the bit length of the logical bitstring it backs (so 7-bit and 9-bit
/// payloads round-trip without losing the trailing-bit count).
#[repr(C)]
pub struct SharedBin {
    pub refcount: AtomicUsize,
    pub bit_len: u64,
    pub bytes: Box<[u8]>,
}

/// Allocate a fresh SharedBin with refcount = 1. Copies `bytes` into a
/// new `Box<[u8]>` so the caller does not need to keep the source slice
/// alive. The returned pointer must be released via `shared_bin_release`
/// when the holder's reference drops; `shared_bin_retain` may be called
/// any number of times in between.
pub fn shared_bin_alloc(bytes: &[u8], bit_len: u64) -> *mut SharedBin {
    let buf: Box<[u8]> = bytes.to_vec().into_boxed_slice();
    let bin = Box::new(SharedBin {
        refcount: AtomicUsize::new(1),
        bit_len,
        bytes: buf,
    });
    #[cfg(test)]
    SHARED_BIN_LIVE_COUNT.fetch_add(1, Ordering::Relaxed);
    Box::into_raw(bin)
}

/// Increment the refcount on an already-owned SharedBin. The caller must
/// already hold at least one reference, so `Relaxed` is the correct
/// ordering — there is no synchronisation edge to publish here, just an
/// atomic count update.
///
/// # Safety
/// `p` must point at a live SharedBin allocated by `shared_bin_alloc`.
pub unsafe fn shared_bin_retain(p: *mut SharedBin) {
    debug_assert!(!p.is_null());
    let bin = unsafe { &*p };
    let old = bin.refcount.fetch_add(1, Ordering::Relaxed);
    // Overflow is impossible in any realistic program but cheap to guard
    // against; matches `std::sync::Arc::clone`'s posture.
    debug_assert!(old < usize::MAX / 2, "SharedBin refcount overflow");
}

/// Decrement the refcount and free the SharedBin if this was the last
/// reference. Release ordering on the decrement publishes any prior
/// writes to the buffer; the Acquire fence before drop synchronises
/// with the Release on every other releaser so the drop sees all writes.
///
/// # Safety
/// `p` must point at a live SharedBin allocated by `shared_bin_alloc`.
/// After calling, the caller must not dereference `p` again.
pub unsafe fn shared_bin_release(p: *mut SharedBin) {
    debug_assert!(!p.is_null());
    let bin = unsafe { &*p };
    let prev = bin.refcount.fetch_sub(1, Ordering::Release);
    if prev == 1 {
        fence(Ordering::Acquire);
        // Reclaim the Box. Drop of the contained Box<[u8]> frees the bytes.
        unsafe {
            drop(Box::from_raw(p));
        }
        #[cfg(test)]
        SHARED_BIN_LIVE_COUNT.fetch_sub(1, Ordering::Relaxed);
    }
}

// ===== Test infrastructure =====================================================
//
// A live-count gauge for assertions. Increments on alloc, decrements on the
// final release. Not used by the runtime hot path.

#[cfg(test)]
static SHARED_BIN_LIVE_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
pub fn shared_bin_live_count() -> usize {
    SHARED_BIN_LIVE_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    use std::thread;

    /// Allocate one bin, retain N times, release N+1 times → freed; live
    /// count drops by one across the test.
    #[test]
    fn alloc_retain_release_free_pattern() {
        let baseline = shared_bin_live_count();
        let p = shared_bin_alloc(&[1, 2, 3, 4], 32);
        assert_eq!(shared_bin_live_count(), baseline + 1);
        unsafe {
            shared_bin_retain(p);
            shared_bin_retain(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 3);
            shared_bin_release(p);
            shared_bin_release(p);
            assert_eq!((*p).refcount.load(Ordering::Relaxed), 1);
            shared_bin_release(p);
        }
        assert_eq!(shared_bin_live_count(), baseline);
    }

    /// Single alloc → single release frees immediately.
    #[test]
    fn alloc_release_immediately_frees() {
        let baseline = shared_bin_live_count();
        let p = shared_bin_alloc(b"hello", 40);
        assert_eq!(shared_bin_live_count(), baseline + 1);
        unsafe {
            shared_bin_release(p);
        }
        assert_eq!(shared_bin_live_count(), baseline);
    }

    /// Bytes round-trip across retains and partial releases.
    #[test]
    fn bytes_preserved_across_retain_release() {
        let p = shared_bin_alloc(&[0xde, 0xad, 0xbe, 0xef], 32);
        unsafe {
            shared_bin_retain(p);
            assert_eq!(&*(*p).bytes, &[0xde, 0xad, 0xbe, 0xef][..]);
            assert_eq!((*p).bit_len, 32);
            shared_bin_release(p);
            // Still alive — refcount went 1 -> 2 -> 1.
            assert_eq!(&*(*p).bytes, &[0xde, 0xad, 0xbe, 0xef][..]);
            shared_bin_release(p);
        }
    }

    /// Concurrent retain/release from two threads — final refcount is
    /// the producer's single owned reference; live count drops to the
    /// baseline only after the producer releases.
    #[test]
    fn concurrent_retain_release_is_consistent() {
        let baseline = shared_bin_live_count();
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
            assert_eq!(
                (*p).refcount.load(Ordering::Relaxed),
                1,
                "transient retains and releases must balance"
            );
            shared_bin_release(p);
        }
        assert_eq!(shared_bin_live_count(), baseline);
    }
}
