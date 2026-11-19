//! The allocation sites a module's code contains, and the counter each one
//! increments.
//!
//! Every place the module allocates inline registers here as it is lowered and
//! gets the index of its own counter. The counters are one writable, zeroed
//! object of the module, defined once every function has been lowered and the
//! number of sites is known.

use super::CodegenError;
use super::fn_ctx::CodegenFn;
use super::static_object::data_addr;
use cranelift_codegen::ir::{InstBuilder, MemFlagsData, types};
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use fz_runtime::alloc_site::AllocSite;

const COUNTER_BYTES: usize = size_of::<u64>();

pub(crate) struct AllocSites {
    counts: DataId,
    sites: Vec<AllocSite>,
}

impl AllocSites {
    pub(crate) fn declare<M: Module>(jmod: &mut M) -> Result<Self, CodegenError> {
        let counts = jmod
            .declare_data(".fz_alloc_site_counts", Linkage::Local, /*writable=*/ true, false)
            .map_err(|e| CodegenError::new(format!("declare allocation site counters: {e}")))?;
        Ok(Self {
            counts,
            sites: Vec::new(),
        })
    }

    /// Register `site` and emit the increment of its counter.
    pub(crate) fn count<M: Module>(&mut self, body: &mut CodegenFn<'_, '_, M>, site: AllocSite) {
        let offset =
            i32::try_from(self.sites.len() * COUNTER_BYTES).expect("allocation site counters fit an i32 offset");
        self.sites.push(site);
        let flags = MemFlagsData::trusted();
        let counts = data_addr(body.jmod, self.counts, body.b);
        let old = body.b.ins().load(types::I64, flags, counts, offset);
        let new = body.b.ins().iadd_imm_s(old, 1);
        body.b.ins().store(flags, new, counts, offset);
    }

    /// Define the counters, one zeroed word per registered site.
    pub(crate) fn define<M: Module>(self, jmod: &mut M) -> Result<(DataId, Vec<AllocSite>), CodegenError> {
        let mut desc = DataDescription::new();
        desc.define_zeroinit(self.sites.len().max(1) * COUNTER_BYTES);
        desc.set_align(COUNTER_BYTES as u64);
        jmod.define_data(self.counts, &desc)
            .map_err(|e| CodegenError::new(format!("define allocation site counters: {e}")))?;
        Ok((self.counts, self.sites))
    }
}

#[cfg(test)]
#[path = "alloc_site_test.rs"]
mod alloc_site_test;
