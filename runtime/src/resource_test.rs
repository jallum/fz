use super::*;
use crate::heap::{Heap, SIZE_TABLE, SchemaRegistry};
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::AtomicU64;

fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

pub(crate) struct LiveCountGuard {
    baseline: usize,
}
impl LiveCountGuard {
    pub(crate) fn snap() -> Self {
        Self { baseline: live_count() }
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

static DTOR_FIRED: AtomicUsize = AtomicUsize::new(0);
static DTOR_LAST_PAYLOAD: AtomicU64 = AtomicU64::new(0);

unsafe extern "C" fn counting_dtor(payload: u64) {
    DTOR_FIRED.fetch_add(1, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(payload, Ordering::Relaxed);
}

fn reset_counters() {
    DTOR_FIRED.store(0, Ordering::Relaxed);
    DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);
}

#[test]
fn resource_is_24_bytes() {
    assert_eq!(size_of::<Resource>(), 24);
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
        assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 0);
        fz_resource_release(p);
    }
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 42);
}

#[test]
#[serial_test::serial]
fn alloc_release_immediately_fires_dtor() {
    let _g = LiveCountGuard::snap();
    reset_counters();
    let p = resource_alloc(0xdeadbeef, counting_dtor);
    unsafe { fz_resource_release(p) };
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 0xdeadbeef);
}

#[test]
#[serial_test::serial]
fn handle_drop_releases() {
    let _g = LiveCountGuard::snap();
    reset_counters();
    {
        let _h = ResourceHandle::new(99, counting_dtor);
        assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 0);
    }
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 99);
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
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 0);
    drop(h2);
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 7);
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
        let rs = alloc_resource(&mut h, handle, AnyValue::nil_atom());
        let tagged = heap_object_word(rs.as_raw() as *const u8, ValueKind::RESOURCE);
        assert_eq!(tagged & TAG_MASK, TAG_RESOURCE);
        assert_eq!(object_size(tagged), RESOURCE_STUB_SIZE);
        assert_eq!(h.mso_head, tagged);
        assert_eq!(rs.mso_next(), 0);
        assert_eq!(rs.payload(), 0xabcd);
        assert_eq!(rs.refcount(), 1);
        assert_eq!(live_count(), g.baseline() + 1);
    }
    // Heap::drop -> mso_drop_all -> fz_resource_release -> dtor fires.
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 0xabcd);
}

/// Force a GC with no root: the Resource stub becomes unreachable;
/// MSO sweep must invoke the dtor exactly once and clear the chain.
#[test]
#[serial_test::serial]
fn unrooted_resource_dies_in_gc_and_sweep_fires_dtor() {
    let _g = LiveCountGuard::snap();
    reset_counters();
    let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
    let _ = alloc_resource(&mut h, ResourceHandle::new(0x55, counting_dtor), AnyValue::nil_atom());
    let mut root: *mut u8 = null_mut();
    h.gc(&mut root);
    assert_eq!(h.mso_head, 0, "dead Resource swept from MSO");
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 0x55);
}

/// A rooted strict Resource survives Cheney and rewrites the MSO chain to
/// its to-space copy without firing the destructor during GC.
#[test]
#[serial_test::serial]
fn resource_forwarding_marker_through_gc() {
    let _g = LiveCountGuard::snap();
    reset_counters();
    let mut h = Heap::new(SIZE_TABLE[0], empty_registry());
    let rs = alloc_resource(&mut h, ResourceHandle::new(0x66, counting_dtor), AnyValue::nil_atom());
    let from = rs.as_raw();
    let mut root = heap_object_word(from as *const u8, ValueKind::RESOURCE) as *mut u8;
    h.gc(&mut root);

    let to = resource_addr_from_tagged(root as u64).unwrap();
    assert_ne!(to, from);
    assert_eq!(h.mso_head, heap_object_word(to as *const u8, ValueKind::RESOURCE));
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 0);
    drop(h);
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 1);
    assert_eq!(DTOR_LAST_PAYLOAD.load(Ordering::Relaxed), 0x66);
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
        let rs1 = alloc_resource(&mut h, ResourceHandle::new(0xfeed, counting_dtor), AnyValue::nil_atom());
        let pb2 = alloc_procbin(&mut h, SharedBinHandle::from_bytes(&[4, 5], 16));
        let rs2 = alloc_resource(&mut h, ResourceHandle::new(0xbeef, counting_dtor), AnyValue::nil_atom());
        let rs2_bits = heap_object_word(rs2.as_raw() as *const u8, ValueKind::RESOURCE);
        let pb2_bits = heap_object_word(pb2.as_raw() as *const u8, ValueKind::PROCBIN);
        let pb1_bits = heap_object_word(pb1.as_raw() as *const u8, ValueKind::PROCBIN);
        let rs1_bits = heap_object_word(rs1.as_raw() as *const u8, ValueKind::RESOURCE);
        assert_eq!(h.mso_head, rs2_bits);
        assert_eq!(rs2.mso_next(), pb2_bits);
        assert_eq!(pb2.mso_next(), rs1_bits);
        assert_eq!(rs1.mso_next(), pb1_bits);
        assert_eq!(pb2.mso_next() & TAG_MASK, TAG_RESOURCE);
        assert_eq!(pb1.mso_next(), 0);
    }
    // Both resources fired their dtors exactly once each.
    assert_eq!(DTOR_FIRED.load(Ordering::Relaxed), 2);
}
