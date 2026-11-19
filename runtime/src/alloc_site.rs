//! Where a program allocates.
//!
//! An allocation site is one place in compiled code that puts an object on
//! the heap. Its kind and size are fixed when the code is compiled, so the
//! code counts each allocation with one increment of the site's own counter
//! and every other figure is a sum over the sites.
//!
//! A compiled module owns one counter per site. The table describing them is
//! registered with the program's [`crate::process::Node`] when the module is
//! loaded, so it costs a process nothing to spawn.
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

/// A module's allocation sites and the counters its code increments.
pub struct AllocSites {
    sites: Vec<AllocSite>,
    counts: *mut u64,
}

impl AllocSites {
    /// # Safety
    /// `counts` points at one `u64` per site and outlives the table.
    pub unsafe fn new(sites: Vec<AllocSite>, counts: *mut u64) -> Self {
        assert!(
            sites.is_empty() || !counts.is_null(),
            "allocation sites need their counters"
        );
        Self { sites, counts }
    }

    /// Each site with the allocations it has made since the module was loaded.
    pub fn counted(&self) -> impl Iterator<Item = (&AllocSite, u64)> {
        self.sites
            .iter()
            .enumerate()
            .map(|(index, site)| (site, unsafe { self.counts.add(index).read() }))
    }
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
}

impl RuntimeAllocSite {
    pub const ALL: [Self; 17] = [
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
        }
    }
}

/// What each runtime site has placed for one program.
#[derive(Default)]
pub struct RuntimeAllocCounts([Cell<AllocStat>; RuntimeAllocSite::ALL.len()]);

impl RuntimeAllocCounts {
    #[inline]
    pub fn record(&self, site: RuntimeAllocSite, bytes: u64) {
        let count = &self.0[site as usize];
        let mut stat = count.get();
        stat.record(bytes);
        count.set(stat);
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

/// The sites as the bytes a linked program carries: a count, then per site
/// its kind, its size, and its function's name.
pub fn encode_alloc_sites(sites: &[AllocSite]) -> Vec<u8> {
    let mut bytes = (sites.len() as u32).to_le_bytes().to_vec();
    for site in sites {
        bytes.push(site.kind as u8);
        bytes.extend_from_slice(&site.bytes.to_le_bytes());
        bytes.extend_from_slice(&(site.function.len() as u32).to_le_bytes());
        bytes.extend_from_slice(site.function.as_bytes());
    }
    bytes
}

pub fn decode_alloc_sites(mut bytes: &[u8]) -> Result<Vec<AllocSite>, String> {
    let mut take = |n: usize| -> Result<&[u8], String> {
        if bytes.len() < n {
            return Err("allocation site table ends early".to_owned());
        }
        let (head, rest) = bytes.split_at(n);
        bytes = rest;
        Ok(head)
    };
    let word = |four: &[u8]| u32::from_le_bytes(four.try_into().expect("four bytes"));
    let count = word(take(4)?);
    let mut sites = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let kind = HeapAllocKind::from_u8(take(1)?[0])?;
        let size = word(take(4)?);
        let name_len = word(take(4)?) as usize;
        let function = std::str::from_utf8(take(name_len)?)
            .map_err(|error| format!("allocation site function name: {error}"))?
            .to_owned();
        sites.push(AllocSite {
            kind,
            bytes: size,
            function,
        });
    }
    Ok(sites)
}

#[cfg(test)]
#[path = "alloc_site_test.rs"]
mod alloc_site_test;
