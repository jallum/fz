//! GC telemetry — facts captured from the most recent Cheney pass.

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
