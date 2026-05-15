//! fz-ul4.dce.3 — BinOp singleton fold pass.
//!
//! After type_module proves a BinOp result is a singleton int, replace the
//! BinOp stmt with Const(Int(n)) in-place. This makes the operand Const stmts
//! dead, which ir_dce then removes.

use crate::fz_ir::{Const, FnIr, Module, Prim, Stmt};
use crate::ir_typer::ModuleTypes;

pub fn fold_module(m: &mut Module, types: &ModuleTypes) {
    for f in &mut m.fns {
        fold_fn(f, types);
    }
}

fn fold_fn(f: &mut FnIr, types: &ModuleTypes) {
    let Some(fn_types) = types.any_key_spec(f.id) else {
        return;
    };
    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(dest, Prim::BinOp(..)) = stmt else {
                continue;
            };
            let d = fn_types
                .vars
                .get(dest)
                .cloned()
                .unwrap_or_else(crate::types::Descr::any);
            if let Some(n) = d.as_int_singleton() {
                *stmt = Stmt::Let(*dest, Prim::Const(Const::Int(n)));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    /// Test 1: BinOp with singleton result type gets folded to Const.
    ///
    /// Build: entry block with const(41), const(1), BinOp(Add, v1, v2).
    /// The typer proves the BinOp result :: {42}, so fold_module should
    /// rewrite it to Const(Int(42)).
    #[test]
    fn binop_singleton_folded_to_const() {
        // Name "main" so entry_seeds picks it up.
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c41 = b.let_(entry, Prim::Const(Const::Int(41)));
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, c41, c1));
        b.set_terminator(entry, Term::Return(sum));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        let types = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &types);

        let block = m.fns[0].block(m.fns[0].entry);
        // The BinOp stmt (index 2) should now be Const(Int(42)).
        match &block.stmts[2] {
            Stmt::Let(_, Prim::Const(Const::Int(42))) => {}
            other => panic!("expected Const(Int(42)), got {:?}", other),
        }
    }

    /// Test 2: BinOp with non-singleton result type is unchanged.
    ///
    /// Build: entry has a param (any int), const(1), BinOp(Add, param, 1).
    /// The result is any-int (non-singleton) — fold must leave it as BinOp.
    #[test]
    fn binop_non_singleton_unchanged() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let param = b.fresh_var();
        let entry = b.block(vec![param]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, param, c1));
        b.set_terminator(entry, Term::Return(sum));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        let types = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &types);

        let block = m.fns[0].block(m.fns[0].entry);
        // The BinOp stmt (index 1) must still be BinOp.
        match &block.stmts[1] {
            Stmt::Let(_, Prim::BinOp(..)) => {}
            other => panic!("expected BinOp unchanged, got {:?}", other),
        }
    }

    /// Test 3: Non-BinOp stmts are unchanged.
    ///
    /// Build: entry has const(41) only. Fold must leave it as Const.
    #[test]
    fn non_binop_unchanged() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c41 = b.let_(entry, Prim::Const(Const::Int(41)));
        b.set_terminator(entry, Term::Return(c41));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        let types = crate::ir_typer::type_module(&m);
        fold_module(&mut m, &types);

        let block = m.fns[0].block(m.fns[0].entry);
        match &block.stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(41))) => {}
            other => panic!("expected Const(Int(41)) unchanged, got {:?}", other),
        }
    }
}
