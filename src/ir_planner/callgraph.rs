//! Planner-private call-graph utilities over `fz_ir::Module`.
//!
//! Recursion-component discovery lives on `Module::recursive_fns` (shared with
//! type inference so both agree on "recursive fn"); this module owns the
//! planner's entry-seed selection.

use crate::fz_ir::{FnId, Module};
use crate::types::{Ty, Types};

/// Root set for planner discovery: `main` seeded with an any-keyed arg vector.
pub(crate) fn entry_seeds<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> Vec<(FnId, Vec<Ty>)> {
    let mut seeds = Vec::new();
    if let Some(main) = m.fns.iter().find(|f| f.name == "main") {
        let n_params = main.block(main.entry).params.len();
        let any = t.any();
        seeds.push((main.id, t.repeat(any, n_params)));
    }
    seeds
}

#[cfg(test)]
#[path = "callgraph_test.rs"]
mod callgraph_test;
