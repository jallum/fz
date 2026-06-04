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
    let mut t = crate::types::new();
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
    let mut t = crate::types::new();
    let m = finish(vec![fn_halting(0, "not_main")]);
    assert!(entry_seeds(&mut t, &m).is_empty());
}
