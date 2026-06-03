use super::brand_erase::erase_brands;
use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, FnIr, Module, ModuleBuilder, Prim, Stmt, Term};

fn build_module(fns: Vec<FnIr>) -> Module {
    let mut mb = ModuleBuilder::new();
    for f in fns {
        mb.add_fn(f);
    }
    mb.build()
}

#[test]
fn erase_replaces_brand_with_source_in_terminator() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let bs = b.let_(entry, Prim::ConstBitstring(vec![104], 8));
    let branded = b.let_(entry, Prim::Brand(bs, "utf8".to_string()));
    b.set_terminator(entry, Term::Halt(branded));
    let mut m = build_module(vec![b.build()]);
    let n = erase_brands(&mut m);
    assert_eq!(n, 1, "one brand stmt should be removed");
    let f = &m.fns[0];
    let term = &f.block(entry).terminator;
    match term {
        Term::Halt(v) => assert_eq!(*v, bs, "Halt should now refer to source bs"),
        _ => panic!("expected Halt"),
    }
    assert_eq!(f.block(entry).stmts.len(), 1);
}

#[test]
fn erase_chases_through_brand_chains() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let a = b.let_(entry, Prim::Const(Const::Int(42)));
    let mid = b.let_(entry, Prim::Brand(a, "X".to_string()));
    let last = b.let_(entry, Prim::Brand(mid, "Y".to_string()));
    b.set_terminator(entry, Term::Halt(last));
    let mut m = build_module(vec![b.build()]);
    let n = erase_brands(&mut m);
    assert_eq!(n, 2);
    let f = &m.fns[0];
    match &f.block(entry).terminator {
        Term::Halt(v) => assert_eq!(*v, a),
        _ => panic!("expected Halt"),
    }
    assert_eq!(f.block(entry).stmts.len(), 1);
}

#[test]
fn erase_is_noop_when_no_brands() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let c = b.let_(entry, Prim::Const(Const::Int(7)));
    b.set_terminator(entry, Term::Halt(c));
    let mut m = build_module(vec![b.build()]);
    let n = erase_brands(&mut m);
    assert_eq!(n, 0);
    assert_eq!(m.fns[0].block(entry).stmts.len(), 1);
}

#[test]
fn erase_rewrites_prim_operands_too() {
    let mut b = FnBuilder::new(FnId(0), "main");
    let entry = b.block(vec![]);
    let a = b.let_(entry, Prim::Const(Const::Int(1)));
    let branded = b.let_(entry, Prim::Brand(a, "X".to_string()));
    let sum = b.let_(entry, Prim::BinOp(BinOp::Add, a, branded));
    b.set_terminator(entry, Term::Halt(sum));
    let mut m = build_module(vec![b.build()]);
    let n = erase_brands(&mut m);
    assert_eq!(n, 1);
    let f = &m.fns[0];
    let stmts = &f.block(entry).stmts;
    assert_eq!(stmts.len(), 2);
    match &stmts[1] {
        Stmt::Let(_, Prim::BinOp(_, l, r)) => {
            assert_eq!(*l, a);
            assert_eq!(*r, a, "branded operand rewritten to source");
        }
        _ => panic!("expected BinOp stmt"),
    }
}
