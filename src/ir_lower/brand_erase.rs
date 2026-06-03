//! fz-axu.6 (K5) — brand erasure pass.
//!
//! Runs in lowering after brand-aware checks are complete and before the
//! lowered `Module` leaves `ir_lower`. The pass walks every `FnIr` in a
//! `Module` and rewrites every `Stmt::Let(dest, Prim::Brand(src, _))` into a
//! substitution `dest -> src`. The `Brand` stmt is then dropped, and
//! references to `dest` in subsequent statements and block terminators are
//! rewritten to `src`.
//!
//! Why a separate pass: the lattice carries brands so lowering-time checks can
//! still inspect them, but downstream IR passes and runtime backends treat
//! brands as zero-cost wrappers. Erasing them here keeps later stages free of
//! no-op `Prim::Brand` plumbing.
//!
//! Substitutions chase transitively: a chain `b = Brand(a, _); c = Brand(b,
//! _);` collapses to `c -> a`.

use crate::fz_ir::{FnIr, Module, Prim, Stmt, Var};
use crate::ir_fuse::{subst_prim, subst_term};
use std::collections::HashMap;

/// Erase `Prim::Brand` from every fn in `module`. Returns the number of
/// brand stmts removed for tests.
pub(super) fn erase_brands(module: &mut Module) -> usize {
    let mut removed = 0;
    for f in &mut module.fns {
        removed += erase_in_fn(f);
    }
    removed
}

fn erase_in_fn(f: &mut FnIr) -> usize {
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
            *prim = subst_prim(prim, &subst);
        }
        block.terminator = subst_term(&block.terminator, &subst);
    }

    removed
}
