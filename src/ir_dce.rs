//! fz-ul4.dce.4 — Dead stmt elimination, dead block elimination, block fusion.
//!
//! Dead stmts: removes pure stmts whose dest var is not used anywhere in the fn.
//! Fixed-point loop handles chains of dead stmts.
//!
//! Dead blocks: after stmt DCE, prunes blocks unreachable from the entry block.
//! Only Goto and If create intra-function block edges; all other terminators
//! exit to a separate FnIr or terminate execution.
//!
//! Block fusion: merges a block that ends with a parameterless Goto into its
//! single-predecessor target. Runs after dead block elimination so that only
//! reachable blocks remain. Fixed-point loop handles chains.

use crate::fz_ir::{BlockId, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::HashMap;
use std::collections::HashSet;

pub fn dce_module(m: &mut Module) {
    for f in &mut m.fns {
        dce_fn(f);
        fuse_fn(f);
    }
}

fn dce_fn(f: &mut FnIr) {
    loop {
        let used = collect_used(f);
        let mut changed = false;
        for block in &mut f.blocks {
            let before = block.stmts.len();
            block.stmts.retain(|s| {
                let Stmt::Let(dest, prim) = s;
                used.contains(dest) || is_impure(prim)
            });
            changed |= block.stmts.len() != before;
        }
        if !changed {
            break;
        }
    }

    // Dead block elimination: compute reachable set BEFORE retaining so that
    // f.block(id) — which panics on unknown id — is still safe to call.
    let reachable = reachable_from_entry(f);
    f.blocks.retain(|b| reachable.contains(&b.id));
}

fn reachable_from_entry(f: &FnIr) -> HashSet<BlockId> {
    let mut seen = HashSet::new();
    let mut work = vec![f.entry];
    while let Some(bid) = work.pop() {
        if !seen.insert(bid) {
            continue;
        }
        match &f.block(bid).terminator {
            Term::Goto(t, _) => work.push(*t),
            Term::If(_, t, e) => {
                work.push(*t);
                work.push(*e);
            }
            _ => {}
        }
    }
    seen
}

fn collect_used(f: &FnIr) -> HashSet<Var> {
    let mut used = HashSet::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            collect_prim_vars(prim, &mut used);
        }
        collect_term_vars(&block.terminator, &mut used);
    }
    used
}

fn collect_prim_vars(p: &Prim, used: &mut HashSet<Var>) {
    match p {
        Prim::Const(_) => {}
        Prim::BinOp(_, a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::UnOp(_, a) => {
            used.insert(*a);
        }
        Prim::AllocStruct(_, args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Prim::Builtin(_, args) | Prim::Extern(_, args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Prim::ListCons(a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::ListHead(a) | Prim::ListTail(a) | Prim::ListIsNil(a) => {
            used.insert(*a);
        }
        Prim::MakeTuple(args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Prim::TupleField(a, _) => {
            used.insert(*a);
        }
        Prim::MakeList(els, tail) => {
            for v in els {
                used.insert(*v);
            }
            if let Some(t) = tail {
                used.insert(*t);
            }
        }
        Prim::MakeClosure(_, caps) => {
            for v in caps {
                used.insert(*v);
            }
        }
        Prim::MakeMap(entries) => {
            for (k, v) in entries {
                used.insert(*k);
                used.insert(*v);
            }
        }
        Prim::MapUpdate(base, entries) => {
            used.insert(*base);
            for (k, v) in entries {
                used.insert(*k);
                used.insert(*v);
            }
        }
        Prim::MapGet(a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::MakeVec(_, els) => {
            for v in els {
                used.insert(*v);
            }
        }
        Prim::MakeBitstring(fields) => {
            use crate::fz_ir::BitSizeIr;
            for f in fields {
                used.insert(f.value);
                if let Some(BitSizeIr::Var(sv)) = &f.size {
                    used.insert(*sv);
                }
            }
        }
        Prim::ConstBitstring(_, _) => {}
        Prim::BitReaderInit(a) => {
            used.insert(*a);
        }
        Prim::BitReaderDone(a) => {
            used.insert(*a);
        }
        Prim::BitReadField { reader, size, .. } => {
            used.insert(*reader);
            if let Some(crate::fz_ir::BitSizeIr::Var(sv)) = size {
                used.insert(*sv);
            }
        }
        Prim::TypeTest(v, _) => {
            used.insert(*v);
        }
    }
}

fn collect_term_vars(t: &Term, used: &mut HashSet<Var>) {
    match t {
        Term::Goto(_, args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::If(cond, _, _) => {
            used.insert(*cond);
        }
        Term::Call {
            args, continuation, ..
        } => {
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCall { args, .. } => {
            for v in args {
                used.insert(*v);
            }
        }
        Term::CallClosure {
            closure,
            args,
            continuation,
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        Term::TailCallClosure { closure, args } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
        }
        Term::Return(a) | Term::Halt(a) => {
            used.insert(*a);
        }
        Term::Receive { continuation } => {
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
    }
}

fn is_impure(p: &Prim) -> bool {
    matches!(
        p,
        Prim::Builtin(..)
            | Prim::Extern(..)
            | Prim::BitReaderInit(_)
            | Prim::BitReadField { .. }
            | Prim::BitReaderDone(_)
    )
}

/// Merge a block that ends with a parameterless Goto into its single-predecessor
/// target. Repeat until no more fusions are possible.
fn fuse_fn(f: &mut FnIr) {
    loop {
        let mut in_degree: HashMap<BlockId, usize> = f.blocks.iter().map(|b| (b.id, 0)).collect();
        for block in &f.blocks {
            match &block.terminator {
                Term::Goto(t, _) => *in_degree.entry(*t).or_insert(0) += 1,
                Term::If(_, t, e) => {
                    *in_degree.entry(*t).or_insert(0) += 1;
                    *in_degree.entry(*e).or_insert(0) += 1;
                }
                _ => {}
            }
        }

        let fuseable = f.blocks.iter().find_map(|block| {
            if let Term::Goto(target, args) = &block.terminator
                && args.is_empty()
            {
                let tb = f.blocks.iter().find(|b| b.id == *target)?;
                if tb.params.is_empty() && in_degree.get(target) == Some(&1) {
                    return Some((block.id, *target));
                }
            }
            None
        });

        let Some((src_id, target_id)) = fuseable else {
            break;
        };

        let target_pos = f.blocks.iter().position(|b| b.id == target_id).unwrap();
        let target_block = f.blocks.remove(target_pos);
        let src_block = f.blocks.iter_mut().find(|b| b.id == src_id).unwrap();
        src_block.stmts.extend(target_block.stmts);
        src_block.terminator = target_block.terminator;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, Cont, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    /// Test 1: Dead Const removed; live Const (used by a Call arg) kept.
    ///
    /// Build: entry has const(99) (dead), const(42) (used in Return).
    /// After DCE, const(99) should be gone.
    #[test]
    fn dead_const_removed_live_kept() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let _dead = b.let_(entry, Prim::Const(Const::Int(99))); // never used
        let live = b.let_(entry, Prim::Const(Const::Int(42))); // used in Return
        b.set_terminator(entry, Term::Return(live));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        dce_module(&mut m);

        let block = m.fns[0].block(m.fns[0].entry);
        assert_eq!(block.stmts.len(), 1, "dead const should be removed");
        match &block.stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(42))) => {}
            other => panic!("expected live Const(42), got {:?}", other),
        }
    }

    /// Test 2: Builtin with unused dest kept (impure).
    ///
    /// Build: entry has Builtin(Print, []) whose dest is never used.
    /// DCE must keep it because Builtin is impure.
    #[test]
    fn impure_builtin_kept_even_if_unused() {
        use crate::fz_ir::BuiltinId;
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let nil_v = b.let_(entry, Prim::Const(Const::Nil)); // arg for print
        // Builtin(Print) with nil as arg — dest is never used.
        let _print_result = b.let_(entry, Prim::Builtin(BuiltinId(0), vec![nil_v]));
        b.set_terminator(entry, Term::Return(nil_v));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        dce_module(&mut m);

        let block = m.fns[0].block(m.fns[0].entry);
        // The Builtin stmt must remain (impure). nil_v is used by both Builtin and Return.
        assert_eq!(
            block.stmts.len(),
            2,
            "impure Builtin must be kept; stmts: {:?}",
            block.stmts
        );
        assert!(
            matches!(&block.stmts[1], Stmt::Let(_, Prim::Builtin(..))),
            "second stmt should be Builtin, got {:?}",
            block.stmts[1]
        );
    }

    /// Test 3: Chain — dead BinOp of two dead Consts — all three gone
    /// after fixed-point iteration.
    ///
    /// Build: c1=const(1), c2=const(2), dead=BinOp(Add,c1,c2) — none used.
    /// After fixed-point DCE all three stmts should be removed.
    #[test]
    fn dead_chain_eliminated_fixed_point() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let c2 = b.let_(entry, Prim::Const(Const::Int(2)));
        let _dead = b.let_(entry, Prim::BinOp(BinOp::Add, c1, c2));
        // Return a fresh nil, not any of the above.
        let nil_v = b.let_(entry, Prim::Const(Const::Nil));
        b.set_terminator(entry, Term::Return(nil_v));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        dce_module(&mut m);

        let block = m.fns[0].block(m.fns[0].entry);
        // Only nil_v should remain.
        assert_eq!(
            block.stmts.len(),
            1,
            "dead chain (const+const+binop) should all be removed; stmts: {:?}",
            block.stmts
        );
    }

    /// Test 4: Mixed block — only dead stmts removed, live stmts kept.
    ///
    /// Build: dead=const(7), live=const(42). Return live.
    /// dead should be gone; live kept.
    #[test]
    fn mixed_block_dead_removed_live_kept() {
        let cont_fn = FnId(1);
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let _dead = b.let_(entry, Prim::Const(Const::Int(7)));
        let live = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(
            entry,
            Term::Call {
                callee: cont_fn,
                args: vec![live],
                continuation: Cont {
                    fn_id: cont_fn,
                    captured: vec![],
                },
            },
        );
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        dce_module(&mut m);

        let block = m.fns[0].block(m.fns[0].entry);
        assert_eq!(
            block.stmts.len(),
            1,
            "dead const(7) should be removed; stmts: {:?}",
            block.stmts
        );
        match &block.stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(42))) => {}
            other => panic!("expected live Const(42), got {:?}", other),
        }
    }

    // ── Dead block elimination ────────────────────────────────────────────────

    #[test]
    fn unreachable_block_removed() {
        // entry → Return(nil); orphan block exists but is never jumped to.
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let orphan = b.block(vec![]);
        let nil_e = b.let_(entry, Prim::Const(Const::Nil));
        b.set_terminator(entry, Term::Return(nil_e));
        let nil_o = b.let_(orphan, Prim::Const(Const::Nil));
        b.set_terminator(orphan, Term::Return(nil_o));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();

        assert_eq!(m.fns[0].blocks.len(), 2, "should start with 2 blocks");
        dce_module(&mut m);
        assert_eq!(m.fns[0].blocks.len(), 1, "orphan block should be removed");
        assert_eq!(m.fns[0].blocks[0].id, entry);
    }

    #[test]
    fn entry_always_retained() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let nil = b.let_(entry, Prim::Const(Const::Nil));
        b.set_terminator(entry, Term::Return(nil));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        dce_module(&mut m);
        assert_eq!(m.fns[0].blocks.len(), 1);
        assert_eq!(m.fns[0].blocks[0].id, entry);
    }

    #[test]
    fn both_if_branches_kept() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let cond_v = b.fresh_var();
        let entry = b.block(vec![cond_v]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(cond_v, then_b, else_b));
        let n1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(n1));
        let n2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(n2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        dce_module(&mut m);
        assert_eq!(m.fns[0].blocks.len(), 3, "both If branches must be kept");
    }

    #[test]
    fn dead_branch_removed_after_goto() {
        // entry → Goto(then_b); else_b exists but is unreferenced.
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::Goto(then_b, vec![]));
        let n1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(n1));
        let n2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(n2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();

        assert_eq!(m.fns[0].blocks.len(), 3, "should start with 3 blocks");
        dce_module(&mut m);
        // else_b removed by dead block elimination; entry fused with then_b.
        assert_eq!(
            m.fns[0].blocks.len(),
            1,
            "else_b removed and entry+then_b fused"
        );
        assert_eq!(m.fns[0].blocks[0].id, entry);
        assert!(matches!(m.fns[0].blocks[0].terminator, Term::Return(_)));
    }
}
