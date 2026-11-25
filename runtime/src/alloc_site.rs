//! Where a program allocates.
//!
//! An allocation site is one place in compiled code that puts an object on
//! the heap. Its kind and size are fixed when the code is compiled, so the
//! code counts each allocation with one increment of the site's own counter
//! and every other figure is a sum over the sites. Compiled sites live in the
//! program's [`crate::site_table::SiteTable`].
//!
//! The runtime allocates too, on behalf of compiled code that calls it. Each
//! runtime function that places an object is a site of its own, a
//! [`RuntimeAllocSite`], counted on the node with the bytes it placed because
//! its objects vary in size.

use crate::heap::{AllocStat, HeapAllocKind};
use std::cell::Cell;

/// One allocation site: what it allocates and the function it is in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocSite {
    pub kind: HeapAllocKind,
    /// The bytes one allocation takes, rounded as the heap rounds them.
    pub bytes: u32,
    /// The function the site is in, as diagnostics name it.
    pub function: String,
}

/// A runtime function that places an object on a heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RuntimeAllocSite {
    ListConsValue,
    ListConsStorage,
    ListConsCopy,
    Struct,
    Closure,
    Continuation,
    OrderedMapEntries,
    MapDestination,
    FlatMap,
    MapNode,
    InlineBitstring,
    BinView,
    BinRef,
    ScalarBox,
    ScalarBoxCopy,
    Resource,
    Other,
    /// An off-heap binary buffer, counted with the bytes of the buffer.
    SharedBin,
}

impl RuntimeAllocSite {
    pub const ALL: [Self; 18] = [
        Self::ListConsValue,
        Self::ListConsStorage,
        Self::ListConsCopy,
        Self::Struct,
        Self::Closure,
        Self::Continuation,
        Self::OrderedMapEntries,
        Self::MapDestination,
        Self::FlatMap,
        Self::MapNode,
        Self::InlineBitstring,
        Self::BinView,
        Self::BinRef,
        Self::ScalarBox,
        Self::ScalarBoxCopy,
        Self::Resource,
        Self::Other,
        Self::SharedBin,
    ];

    pub fn kind(self) -> HeapAllocKind {
        match self {
            Self::ListConsValue | Self::ListConsStorage | Self::ListConsCopy => HeapAllocKind::ListCons,
            Self::Struct => HeapAllocKind::Struct,
            Self::Closure => HeapAllocKind::Closure,
            Self::Continuation => HeapAllocKind::Continuation,
            Self::OrderedMapEntries | Self::MapDestination | Self::FlatMap | Self::MapNode => HeapAllocKind::Map,
            Self::InlineBitstring => HeapAllocKind::Bitstring,
            Self::BinView => HeapAllocKind::BinView,
            Self::BinRef => HeapAllocKind::BinRef,
            Self::ScalarBox | Self::ScalarBoxCopy => HeapAllocKind::ScalarBox,
            Self::Resource => HeapAllocKind::Resource,
            Self::Other => HeapAllocKind::Other,
            Self::SharedBin => HeapAllocKind::SharedBin,
        }
    }

    /// The runtime function the site is, as the run's report names it.
    pub fn function(self) -> &'static str {
        match self {
            Self::ListConsValue => "runtime::alloc_list_cons_value",
            Self::ListConsStorage => "runtime::alloc_list_cons_storage",
            Self::ListConsCopy => "runtime::copy_list_cell",
            Self::Struct => "runtime::alloc_struct_unwritten",
            Self::Closure => "runtime::alloc_closure",
            Self::Continuation => "runtime::alloc_continuation",
            Self::OrderedMapEntries => "runtime::alloc_ordered_map_entries",
            Self::MapDestination => "runtime::alloc_map_destination",
            Self::FlatMap => "runtime::write_flat_map",
            Self::MapNode => "runtime::alloc_map_node",
            Self::InlineBitstring => "runtime::alloc_inline_bitstring",
            Self::BinView => "runtime::alloc_view",
            Self::BinRef => "runtime::alloc_binref",
            Self::ScalarBox => "runtime::box_any_value_ref",
            Self::ScalarBoxCopy => "runtime::deep_copy_any_value_ref",
            Self::Resource => "runtime::alloc_resource",
            Self::Other => "runtime::alloc",
            Self::SharedBin => "runtime::alloc_shared_bin",
        }
    }
}

/// What each runtime site has placed for one program.
#[derive(Default)]
pub struct RuntimeAllocCounts([Cell<AllocStat>; RuntimeAllocSite::ALL.len()]);

impl RuntimeAllocCounts {
    #[inline]
    pub fn record(&self, site: RuntimeAllocSite, bytes: u64) {
        self.record_run(site, 1, bytes);
    }

    /// `count` placements of `bytes` each at `site`.
    #[inline]
    pub fn record_run(&self, site: RuntimeAllocSite, count: u64, bytes: u64) {
        let cell = &self.0[site as usize];
        let mut stat = cell.get();
        stat.record_run(count, bytes);
        cell.set(stat);
    }

    pub fn counted(&self) -> impl Iterator<Item = (RuntimeAllocSite, AllocStat)> {
        RuntimeAllocSite::ALL
            .into_iter()
            .map(|site| (site, self.0[site as usize].get()))
    }
}

/// What one site placed during a run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllocSiteCount {
    pub function: String,
    pub kind: HeapAllocKind,
    pub placed: AllocStat,
}

#[cfg(test)]
#[path = "alloc_site_test.rs"]
mod alloc_site_test;
