//! Where a program reuses an object in place.
//!
//! A reuse site is one place that rebuilds a list cell or a struct from the
//! object it took apart. The object may be written in place, which is a hit,
//! or a new one is placed, which is a miss. Each reuse bumps exactly one of
//! its site's two counters, and every other figure is a sum over the sites.
//!
//! A compiled module's reuse sites share its table of sites with its
//! allocation sites; see [`crate::site_table`]. The runtime reuses on behalf
//! of compiled code and the interpreter too. Each runtime function that does
//! is a site of its own, a [`RuntimeReuseSite`], counted on the node.

use std::cell::Cell;

/// What a reuse site rebuilds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ReuseKind {
    List,
    Struct,
    Tuple,
}

impl ReuseKind {
    pub const ALL: [Self; 3] = [Self::List, Self::Struct, Self::Tuple];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::List => "list",
            Self::Struct => "struct",
            Self::Tuple => "tuple",
        }
    }

    /// The kind whose discriminant is `byte`.
    pub fn from_u8(byte: u8) -> Result<Self, String> {
        Self::ALL
            .into_iter()
            .find(|kind| *kind as u8 == byte)
            .ok_or_else(|| format!("no reuse kind {byte}"))
    }
}

/// One compiled reuse site: what it rebuilds and the function it is in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReuseSite {
    pub kind: ReuseKind,
    /// The function the site is in, as diagnostics name it.
    pub function: String,
}

/// What reuses came to: written in place, or replaced by a new object.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReuseStat {
    pub hits: u64,
    pub misses: u64,
}

impl ReuseStat {
    pub fn attempts(self) -> u64 {
        self.hits + self.misses
    }

    pub fn add(&mut self, other: ReuseStat) {
        self.hits += other.hits;
        self.misses += other.misses;
    }
}

/// A runtime function that reuses an object or replaces it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum RuntimeReuseSite {
    ListReuse,
    StructCopy,
    StructReuse,
    TupleCopy,
}

impl RuntimeReuseSite {
    pub const ALL: [Self; 4] = [Self::ListReuse, Self::StructCopy, Self::StructReuse, Self::TupleCopy];

    pub fn kind(self) -> ReuseKind {
        match self {
            Self::ListReuse => ReuseKind::List,
            Self::StructCopy | Self::StructReuse => ReuseKind::Struct,
            Self::TupleCopy => ReuseKind::Tuple,
        }
    }

    /// The runtime function the site is, as the run's report names it.
    pub fn function(self) -> &'static str {
        match self {
            Self::ListReuse => "runtime::fz_list_reuse_or_cons_parts",
            Self::StructCopy => "runtime::fz_struct_copy",
            Self::StructReuse => "runtime::fz_struct_reuse_or_copy",
            Self::TupleCopy => "runtime::fz_tuple_put",
        }
    }
}

/// What each runtime reuse site has done for one program.
#[derive(Default)]
pub struct RuntimeReuseCounts([Cell<ReuseStat>; RuntimeReuseSite::ALL.len()]);

impl RuntimeReuseCounts {
    #[inline]
    pub fn hit(&self, site: RuntimeReuseSite) {
        self.update(site, |stat| stat.hits += 1);
    }

    #[inline]
    pub fn miss(&self, site: RuntimeReuseSite) {
        self.update(site, |stat| stat.misses += 1);
    }

    #[inline]
    fn update(&self, site: RuntimeReuseSite, change: impl FnOnce(&mut ReuseStat)) {
        let cell = &self.0[site as usize];
        let mut stat = cell.get();
        change(&mut stat);
        cell.set(stat);
    }

    pub fn counted(&self) -> impl Iterator<Item = (RuntimeReuseSite, ReuseStat)> {
        RuntimeReuseSite::ALL
            .into_iter()
            .map(|site| (site, self.0[site as usize].get()))
    }
}

/// What one site did during a run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReuseSiteCount {
    pub function: String,
    pub kind: ReuseKind,
    pub reused: ReuseStat,
}

/// What a program's reuses came to, for lists and for structs. The struct
/// figure includes tuple copies.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Retention {
    pub list: ReuseStat,
    pub struct_: ReuseStat,
}

impl Retention {
    /// The figure the sites come to: lists, and structs with their tuple
    /// copies.
    pub fn sum<'a>(sites: impl IntoIterator<Item = &'a ReuseSiteCount>) -> Self {
        let mut retention = Self::default();
        for site in sites {
            match site.kind {
                ReuseKind::List => retention.list.add(site.reused),
                ReuseKind::Struct | ReuseKind::Tuple => retention.struct_.add(site.reused),
            }
        }
        retention
    }
}
