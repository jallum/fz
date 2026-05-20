//! fz-axu.6 (K5) — brand erasure pass.
//!
//! Runs between the typer (which produced and consulted Brand-tagged
//! types) and codegen (which has no concept of brands). The pass walks
//! every `FnIr` in a `Module` and rewrites every
//! `Stmt::Let(dest, Prim::Brand(src, _))` into a substitution
//! `dest → src`. The `Brand` stmt is then dropped, and references to
//! `dest` in subsequent statements and block terminators are rewritten
//! to `src`.
//!
//! Why a separate pass: the lattice carries brands so the typer can
//! enforce K4's subtype rule. Codegen treats `Prim::Brand` as
//! pass-through, but the value-numbering / DCE / register-allocation
//! downstream is cleaner when the IR contains no zero-cost wrappers.
//! Erasing here also frees the `Prim::Brand` arm from later passes
//! that would otherwise need to thread a no-op through.
//!
//! Substitutions chase transitively: a chain
//! `b = Brand(a, _); c = Brand(b, _);` collapses to `c → a`.

use crate::fz_ir::{Module, Prim, Stmt, Var};
use std::collections::HashMap;

/// Erase `Prim::Brand` from every fn in `module`. Returns the number of
/// brand stmts removed (for diagnostics / tests).
pub fn erase_brands(module: &mut Module) -> usize {
    let mut removed = 0;
    for f in &mut module.fns {
        removed += erase_in_fn(f);
    }
    removed
}

fn erase_in_fn(f: &mut crate::fz_ir::FnIr) -> usize {
    // Two-pass within the fn:
    // 1. Walk all blocks, building the substitution map. Drop the Brand
    //    stmts in place.
    // 2. Apply substitution to every remaining stmt's Prim operands
    //    and to every terminator.
    let mut subst: HashMap<Var, Var> = HashMap::new();
    let mut removed = 0;

    for block in &mut f.blocks {
        block.stmts.retain(|stmt| {
            let Stmt::Let(dest, prim) = stmt;
            if let Prim::Brand(src, _) = prim {
                // Chase through any prior brands so the chain collapses
                // to a single hop.
                let final_src = *subst.get(src).unwrap_or(src);
                subst.insert(*dest, final_src);
                removed += 1;
                false
            } else {
                true
            }
        });
    }

    if subst.is_empty() {
        return 0;
    }

    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(_, prim) = stmt;
            *prim = crate::ir_fuse::subst_prim(prim, &subst);
        }
        block.terminator = crate::ir_fuse::subst_term(&block.terminator, &subst);
    }

    removed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
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
        // The Halt terminator now references the source bitstring var,
        // not the (erased) branded var.
        let f = &m.fns[0];
        let term = &f.block(entry).terminator;
        match term {
            Term::Halt(v) => assert_eq!(*v, bs, "Halt should now refer to source bs"),
            _ => panic!("expected Halt"),
        }
        // The Brand stmt is gone.
        assert_eq!(f.block(entry).stmts.len(), 1);
    }

    #[test]
    fn erase_chases_through_brand_chains() {
        // a = const; b = Brand(a, "X"); c = Brand(b, "Y"); Halt(c).
        // After erasure: c → a, b gone, Halt(a).
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
        // Only the Const stmt remains.
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
        // a = const 1; b = Brand(a, "X"); c = a + b; Halt(c).
        // After erasure: c = a + a; Halt(c).
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(1)));
        let _branded = b.let_(entry, Prim::Brand(a, "X".to_string()));
        // Build BinOp referring to the brand
        let sum = b.let_(entry, Prim::BinOp(crate::fz_ir::BinOp::Add, a, _branded));
        b.set_terminator(entry, Term::Halt(sum));
        let mut m = build_module(vec![b.build()]);
        let n = erase_brands(&mut m);
        assert_eq!(n, 1);
        // Sum stmt's BinOp now uses (a, a) instead of (a, branded).
        let f = &m.fns[0];
        let stmts = &f.block(entry).stmts;
        // Two stmts left: Const, BinOp. Brand dropped.
        assert_eq!(stmts.len(), 2);
        match &stmts[1] {
            Stmt::Let(_, Prim::BinOp(_, l, r)) => {
                assert_eq!(*l, a);
                assert_eq!(*r, a, "branded operand rewritten to source");
            }
            _ => panic!("expected BinOp stmt"),
        }
    }
}
