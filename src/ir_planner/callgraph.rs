//! Planner-private call-graph utilities over `fz_ir::Module`.
//!
//! Recursion-component discovery lives on `Module::recursive_fns` (shared with
//! type inference so both agree on "recursive fn"); this module owns the
//! planner's entry-seed selection.

use crate::fz_ir::{FnId, Module};
use crate::types::{Ty, Types};

/// Root set for planner discovery: `main` seeded with an any-keyed arg vector.
pub(super) fn entry_seeds<T: Types<Ty = Ty>>(t: &mut T, m: &Module) -> Vec<(FnId, Vec<Ty>)> {
    let mut seeds = Vec::new();
    if let Some(main) = m.fns.iter().find(|f| f.name == "main") {
        let n_params = main.block(main.entry).params.len();
        let any = t.any();
        seeds.push((main.id, t.repeat(any, n_params)));
    }
    seeds
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{FnBuilder, FnId, Module, Term, Var};

    fn finish(builders: Vec<FnBuilder>) -> Module {
        let mut m = Module::new();
        for (idx, b) in builders.into_iter().enumerate() {
            let f = b.build();
            m.fn_idx.insert(f.id, idx);
            m.fns.push(f);
        }
        m
    }

    fn fn_halting(id: u32, name: &str) -> FnBuilder {
        let mut b = FnBuilder::new(FnId(id), name);
        let _unused = b.fresh_var();
        let entry = b.block(vec![]);
        b.set_terminator(entry, Term::Halt(Var(0)));
        b
    }

    #[test]
    fn entry_seeds_main_with_any_inputs() {
        let mut t = crate::types::ConcreteTypes;
        let mut main = FnBuilder::new(FnId(0), "main");
        let a = main.fresh_var();
        let b = main.fresh_var();
        let entry = main.block(vec![a, b]);
        main.set_terminator(entry, Term::Halt(a));
        let m = finish(vec![main]);
        let seeds = entry_seeds(&mut t, &m);
        assert_eq!(seeds.len(), 1);
        assert_eq!(seeds[0].0, FnId(0));
        assert_eq!(seeds[0].1.len(), 2);
    }

    #[test]
    fn entry_seeds_is_empty_without_main() {
        let mut t = crate::types::ConcreteTypes;
        let m = finish(vec![fn_halting(0, "not_main")]);
        assert!(entry_seeds(&mut t, &m).is_empty());
    }
}
