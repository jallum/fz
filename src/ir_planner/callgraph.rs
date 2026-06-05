//! Planner-private call-graph utilities over `fz_ir::Module`.
//!
//! Recursion-component discovery lives on `Module::recursive_fns` (shared with
//! type inference so both agree on "recursive fn"); this module owns the
//! planner's entry-seed selection.

use crate::fz_ir::{FnId, Module};
use crate::types::{Ty, Types};

pub(crate) fn entry_seed_fn_ids(m: &Module) -> Vec<FnId> {
    m.fns
        .iter()
        .find(|f| f.name == "main")
        .map(|main| vec![main.id])
        .unwrap_or_default()
}

pub(crate) fn entry_seeds_for_fn_ids<T: Types<Ty = Ty>>(
    t: &mut T,
    m: &Module,
    entry_fn_ids: &[FnId],
) -> Vec<(FnId, Vec<Ty>)> {
    let any = t.any();
    entry_fn_ids
        .iter()
        .filter_map(|fn_id| {
            let fn_ir = m.fn_by_id(*fn_id);
            let n_params = fn_ir.block(fn_ir.entry).params.len();
            Some((*fn_id, t.repeat(any.clone(), n_params)))
        })
        .collect()
}

/// Root set for planner discovery: `main` seeded with an any-keyed arg vector.
pub(crate) fn entry_seeds<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> Vec<(FnId, Vec<Ty>)> {
    entry_seeds_for_fn_ids(t, m, &entry_seed_fn_ids(m))
}

#[cfg(test)]
#[path = "callgraph_test.rs"]
mod callgraph_test;
