//! The sites of a compiled program: where it allocates and where it reuses.
//!
//! A site's kind, and for an allocation its size, are fixed when the code is
//! compiled, so the code counts each event with one increment of the site's
//! own counter and every other figure is a sum over the sites. An allocation
//! site owns one counter word, the allocations. A reuse site owns two, its
//! hits and then its misses.
//!
//! A compiled module owns the counters, one zeroed object. The table
//! describing them is registered with the program's [`crate::process::Node`]
//! when the module is loaded, so it costs a process nothing to spawn.

use crate::alloc_site::AllocSite;
use crate::heap::HeapAllocKind;
use crate::reuse_site::{ReuseKind, ReuseSite, ReuseStat};

/// One compiled site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Site {
    Alloc(AllocSite),
    Reuse(ReuseSite),
}

impl Site {
    /// The counter words the site owns.
    pub fn counter_words(&self) -> usize {
        match self {
            Site::Alloc(_) => 1,
            Site::Reuse(_) => 2,
        }
    }
}

/// A module's sites and the counters its code increments.
pub struct SiteTable {
    sites: Vec<Site>,
    counts: *mut u64,
}

impl SiteTable {
    /// # Safety
    /// `counts` points at the counter words of every site, in order, and
    /// outlives the table.
    pub unsafe fn new(sites: Vec<Site>, counts: *mut u64) -> Self {
        assert!(sites.is_empty() || !counts.is_null(), "sites need their counters");
        Self { sites, counts }
    }

    /// Each site with its counter words as they stand.
    fn counted(&self) -> impl Iterator<Item = (&Site, &[u64])> {
        let mut next = 0;
        self.sites.iter().map(move |site| {
            let words = site.counter_words();
            let counters = unsafe { std::slice::from_raw_parts(self.counts.add(next), words) };
            next += words;
            (site, counters)
        })
    }

    /// Each allocation site with the allocations it has made since the
    /// module was loaded.
    pub fn allocations(&self) -> impl Iterator<Item = (&AllocSite, u64)> {
        self.counted().filter_map(|(site, counters)| match site {
            Site::Alloc(site) => Some((site, counters[0])),
            Site::Reuse(_) => None,
        })
    }

    /// Each reuse site with what it has done since the module was loaded.
    pub fn reuses(&self) -> impl Iterator<Item = (&ReuseSite, ReuseStat)> {
        self.counted().filter_map(|(site, counters)| match site {
            Site::Reuse(site) => Some((
                site,
                ReuseStat {
                    hits: counters[0],
                    misses: counters[1],
                },
            )),
            Site::Alloc(_) => None,
        })
    }
}

const ALLOC: u8 = 0;
const REUSE: u8 = 1;

/// The sites as the bytes a linked program carries: a count, then per site a
/// tag and its fields.
pub fn encode_sites(sites: &[Site]) -> Vec<u8> {
    let mut bytes = (sites.len() as u32).to_le_bytes().to_vec();
    for site in sites {
        match site {
            Site::Alloc(site) => {
                bytes.push(ALLOC);
                bytes.push(site.kind as u8);
                bytes.extend_from_slice(&site.bytes.to_le_bytes());
                push_name(&mut bytes, &site.function);
            }
            Site::Reuse(site) => {
                bytes.push(REUSE);
                bytes.push(site.kind as u8);
                push_name(&mut bytes, &site.function);
            }
        }
    }
    bytes
}

fn push_name(bytes: &mut Vec<u8>, function: &str) {
    bytes.extend_from_slice(&(function.len() as u32).to_le_bytes());
    bytes.extend_from_slice(function.as_bytes());
}

pub fn decode_sites(mut bytes: &[u8]) -> Result<Vec<Site>, String> {
    let mut take = |n: usize| -> Result<&[u8], String> {
        if bytes.len() < n {
            return Err("site table ends early".to_owned());
        }
        let (head, rest) = bytes.split_at(n);
        bytes = rest;
        Ok(head)
    };
    let word = |four: &[u8]| u32::from_le_bytes(four.try_into().expect("four bytes"));
    let count = word(take(4)?);
    let mut sites = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let tag = take(1)?[0];
        let kind = take(1)?[0];
        let site = match tag {
            ALLOC => {
                let kind = HeapAllocKind::from_u8(kind)?;
                let size = word(take(4)?);
                let function = take_name(&mut take, &word)?;
                Site::Alloc(AllocSite {
                    kind,
                    bytes: size,
                    function,
                })
            }
            REUSE => {
                let kind = ReuseKind::from_u8(kind)?;
                let function = take_name(&mut take, &word)?;
                Site::Reuse(ReuseSite { kind, function })
            }
            other => return Err(format!("no site tag {other}")),
        };
        sites.push(site);
    }
    Ok(sites)
}

fn take_name<'a>(
    take: &mut impl FnMut(usize) -> Result<&'a [u8], String>,
    word: &impl Fn(&[u8]) -> u32,
) -> Result<String, String> {
    let len = word(take(4)?) as usize;
    std::str::from_utf8(take(len)?)
        .map(str::to_owned)
        .map_err(|error| format!("site function name: {error}"))
}

#[cfg(test)]
#[path = "site_table_test.rs"]
mod site_table_test;
