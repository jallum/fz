//! GC telemetry — facts captured from the most recent Cheney pass.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AllocStat {
    pub allocs: u64,
    pub bytes: u64,
}

impl AllocStat {
    pub fn record(&mut self, bytes: u64) {
        self.allocs += 1;
        self.bytes += bytes;
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HeapAllocStats {
    pub total: AllocStat,
    pub list_cons: AllocStat,
    pub struct_: AllocStat,
    pub closure: AllocStat,
    pub map: AllocStat,
    pub bitstring: AllocStat,
    pub procbin: AllocStat,
    pub scalar_box: AllocStat,
    pub frame: AllocStat,
    pub resource: AllocStat,
    pub other: AllocStat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapAllocKind {
    ListCons,
    Struct,
    Closure,
    Map,
    Bitstring,
    ProcBin,
    ScalarBox,
    Frame,
    Resource,
    Other,
}

impl HeapAllocStats {
    pub fn record(&mut self, kind: HeapAllocKind, bytes: u64) {
        self.total.record(bytes);
        match kind {
            HeapAllocKind::ListCons => self.list_cons.record(bytes),
            HeapAllocKind::Struct => self.struct_.record(bytes),
            HeapAllocKind::Closure => self.closure.record(bytes),
            HeapAllocKind::Map => self.map.record(bytes),
            HeapAllocKind::Bitstring => self.bitstring.record(bytes),
            HeapAllocKind::ProcBin => self.procbin.record(bytes),
            HeapAllocKind::ScalarBox => self.scalar_box.record(bytes),
            HeapAllocKind::Frame => self.frame.record(bytes),
            HeapAllocKind::Resource => self.resource.record(bytes),
            HeapAllocKind::Other => self.other.record(bytes),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GcStats {
    pub copied_objects: u64,
    pub copied_bytes: u64,
    pub fragment_survivors: u64,
    pub fragment_live_bytes: u64,
    pub live_objects: u64,
    pub live_bytes: u64,
    pub from_space_capacity_bytes: u64,
    pub to_space_capacity_bytes: u64,
    pub size_class: u8,
    pub root_heap_edges: u64,
    pub root_scalar_slots: u64,
    pub list_head_heap_edges: u64,
    pub list_head_scalar_slots: u64,
    pub list_tail_edges: u64,
    pub struct_heap_edges: u64,
    pub struct_scalar_slots: u64,
    pub map_heap_edges: u64,
    pub map_scalar_slots: u64,
    pub closure_heap_edges: u64,
    pub closure_scalar_slots: u64,
    pub resource_heap_edges: u64,
    pub resource_scalar_slots: u64,
}
