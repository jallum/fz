//! The sites a module's code contains, and the counters each one increments.
//!
//! Every place the module allocates inline, and every place it reuses an
//! object in place, registers here as it is lowered and gets counter words
//! of its own: one for an allocation, a hit word and a miss word for a
//! reuse. The counters are one writable, zeroed object of the module, defined
//! once every function has been lowered and the number of sites is known.

use super::CodegenError;
use super::fn_ctx::CodegenFn;
use super::static_object::data_addr;
use cranelift_codegen::ir::{InstBuilder, MemFlagsData, types};
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use fz_runtime::alloc_site::AllocSite;
use fz_runtime::reuse_site::{ReuseKind, ReuseSite};
use fz_runtime::site_table::Site;
use std::cell::RefCell;

const COUNTER_BYTES: usize = size_of::<u64>();

/// Where a site registers: the module's table of sites and the name of the
/// function being lowered.
#[derive(Clone, Copy)]
pub(crate) struct SiteScope<'a> {
    pub(crate) sites: &'a RefCell<SiteTable>,
    pub(crate) function: &'a str,
}

/// Where in the counters object a reuse site counts its two outcomes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ReuseCounters {
    pub(crate) hits: i32,
    pub(crate) misses: i32,
}

pub(crate) struct SiteTable {
    counts: DataId,
    sites: Vec<Site>,
    words: usize,
}

impl SiteTable {
    pub(crate) fn declare<M: Module>(jmod: &mut M) -> Result<Self, CodegenError> {
        let counts = jmod
            .declare_data(".fz_site_counts", Linkage::Local, /*writable=*/ true, false)
            .map_err(|e| CodegenError::new(format!("declare site counters: {e}")))?;
        Ok(Self {
            counts,
            sites: Vec::new(),
            words: 0,
        })
    }

    /// Register `site` and answer the byte offset of its first counter.
    fn register(&mut self, site: Site) -> i32 {
        let offset = i32::try_from(self.words * COUNTER_BYTES).expect("site counters fit an i32 offset");
        self.words += site.counter_words();
        self.sites.push(site);
        offset
    }

    /// Register an allocation site and emit the increment of its counter.
    pub(crate) fn count_alloc<M: Module>(&mut self, body: &mut CodegenFn<'_, '_, M>, site: AllocSite) {
        let offset = self.register(Site::Alloc(site));
        self.bump(body, offset);
    }

    /// Register a reuse site of `kind` in `function`.
    pub(crate) fn register_reuse(&mut self, kind: ReuseKind, function: &str) -> ReuseCounters {
        let hits = self.register(Site::Reuse(ReuseSite {
            kind,
            function: function.to_owned(),
        }));
        ReuseCounters {
            hits,
            misses: hits + COUNTER_BYTES as i32,
        }
    }

    /// Emit the increment of the counter at `offset`.
    pub(crate) fn bump<M: Module>(&self, body: &mut CodegenFn<'_, '_, M>, offset: i32) {
        let flags = MemFlagsData::trusted();
        let counts = data_addr(body.jmod, self.counts, body.b);
        let old = body.b.ins().load(types::I64, flags, counts, offset);
        let new = body.b.ins().iadd_imm_s(old, 1);
        body.b.ins().store(flags, new, counts, offset);
    }

    /// Define the counters, zeroed words for every registered site.
    pub(crate) fn define<M: Module>(self, jmod: &mut M) -> Result<(DataId, Vec<Site>), CodegenError> {
        let mut desc = DataDescription::new();
        desc.define_zeroinit(self.words.max(1) * COUNTER_BYTES);
        desc.set_align(COUNTER_BYTES as u64);
        jmod.define_data(self.counts, &desc)
            .map_err(|e| CodegenError::new(format!("define site counters: {e}")))?;
        Ok((self.counts, self.sites))
    }
}

#[cfg(test)]
#[path = "site_table_test.rs"]
mod site_table_test;
