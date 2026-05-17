//! fz-ul4.fus.2 — Block fusion pass.
//!
//! After the inliner fuses callee blocks into the caller via `Goto`,
//! linear chains of single-predecessor blocks remain. This pass merges
//! each single-predecessor block into its sole predecessor, eliminating
//! block params and Goto edges until a fixed point.
//!
//! Algorithm (fixed-point over each `FnIr`):
//!   1. Build predecessor-count map by scanning all block terminators.
//!      Only `Term::Goto` and `Term::If` create fz-IR block-to-block edges.
//!   2. For each non-entry block B where pred_count[B] == 1:
//!      - Find P, the sole predecessor. Verify P ends with `Goto(B, args)`.
//!      - Build substitution map: B.params[i] → args[i].
//!      - Apply substitution to B's stmts and terminator.
//!      - Append B's stmts to P, set P's terminator to B's (substituted) terminator.
//!      - Mark B for deletion.
//!   3. Remove marked blocks.
//!   4. Repeat until no blocks were removed.

use crate::fz_ir::{BitSizeIr, BlockId, Cont, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::HashMap;

/// Apply `fuse_blocks` to every fn in the module in-place.
pub fn fuse_blocks(module: &mut Module) {
    for f in &mut module.fns {
        fuse_fn(f);
    }
}

pub fn fuse_fn(f: &mut FnIr) {
    loop {
        let removed = fuse_one_pass(f);
        if !removed {
            break;
        }
    }
}

/// One pass: scan for single-predecessor Goto-targeted blocks, fuse them.
/// Returns true if at least one block was fused (caller should loop again).
fn fuse_one_pass(f: &mut FnIr) -> bool {
    // Build predecessor count for every block.
    let mut pred_count: HashMap<BlockId, usize> = HashMap::new();
    for b in &f.blocks {
        pred_count.entry(b.id).or_insert(0);
        match &b.terminator {
            Term::Goto(target, _) => {
                *pred_count.entry(*target).or_insert(0) += 1;
            }
            Term::If(_, t, e) => {
                *pred_count.entry(*t).or_insert(0) += 1;
                *pred_count.entry(*e).or_insert(0) += 1;
            }
            // All other terminators are external handoffs (Call, TailCall,
            // Return, Halt, Receive, CallClosure, TailCallClosure) — they
            // do not name fz-IR blocks as successors.
            _ => {}
        }
    }

    // Find a candidate block to fuse: non-entry, exactly one predecessor,
    // and that predecessor ends with Goto (not If).
    let entry = f.entry;
    let mut fuse_target: Option<BlockId> = None;

    'outer: for b in &f.blocks {
        if b.id == entry {
            continue;
        }
        let pc = *pred_count.get(&b.id).unwrap_or(&0);
        if pc != 1 {
            continue;
        }
        // Find the predecessor — it must end with Goto(b.id, _).
        for pred in &f.blocks {
            if let Term::Goto(target, _) = &pred.terminator
                && *target == b.id
            {
                fuse_target = Some(b.id);
                break 'outer;
            }
        }
    }

    let Some(target_id) = fuse_target else {
        return false;
    };

    // Find the target block's params and locate its predecessor.
    // We need to work around borrow rules by extracting what we need first.

    // Step 1: collect the target block's params.
    let target_params: Vec<Var> = f
        .blocks
        .iter()
        .find(|b| b.id == target_id)
        .map(|b| b.params.clone())
        .expect("target block exists");

    // Step 2: find the predecessor block id and extract its Goto args.
    let (pred_id, goto_args): (BlockId, Vec<Var>) = f
        .blocks
        .iter()
        .find_map(|b| {
            if let Term::Goto(tid, args) = &b.terminator
                && *tid == target_id
            {
                return Some((b.id, args.clone()));
            }
            None
        })
        .expect("predecessor with Goto exists");

    // Step 3: build substitution map: target_params[i] → goto_args[i].
    let mut subst: HashMap<Var, Var> = HashMap::new();
    for (param, arg) in target_params.iter().zip(goto_args.iter()) {
        subst.insert(*param, *arg);
    }

    // Step 4: extract the target block's stmts and terminator, applying subst.
    let (target_stmts, target_term) = {
        let target = f
            .blocks
            .iter()
            .find(|b| b.id == target_id)
            .expect("target block exists");
        let stmts: Vec<Stmt> = target.stmts.iter().map(|s| subst_stmt(s, &subst)).collect();
        let term = subst_term(&target.terminator, &subst);
        (stmts, term)
    };

    // Step 5: apply the substitution to ALL remaining blocks (except the
    // target itself, which we're about to merge). This is necessary because
    // the inliner can produce code where a block's param (e.g. bb4's v8) is
    // referenced in downstream blocks' Goto args (e.g. bb5's Goto to bb7
    // passes v8 as an argument). Those references must also be renamed.
    for blk in f.blocks.iter_mut() {
        if blk.id == target_id || blk.id == pred_id {
            continue;
        }
        blk.stmts = blk.stmts.iter().map(|s| subst_stmt(s, &subst)).collect();
        blk.terminator = subst_term(&blk.terminator, &subst);
    }

    // Step 6: merge into the predecessor.
    let pred = f
        .blocks
        .iter_mut()
        .find(|b| b.id == pred_id)
        .expect("predecessor block exists");
    pred.stmts.extend(target_stmts);
    pred.terminator = target_term;

    // Step 7: remove the target block.
    f.blocks.retain(|b| b.id != target_id);

    true
}

fn subst_var(v: Var, subst: &HashMap<Var, Var>) -> Var {
    *subst.get(&v).unwrap_or(&v)
}

fn subst_prim(p: &Prim, subst: &HashMap<Var, Var>) -> Prim {
    let sv = |v: Var| subst_var(v, subst);
    match p {
        Prim::Const(c) => Prim::Const(c.clone()),
        Prim::BinOp(op, a, b) => Prim::BinOp(*op, sv(*a), sv(*b)),
        Prim::UnOp(op, a) => Prim::UnOp(*op, sv(*a)),
        Prim::AllocStruct(sid, args) => {
            Prim::AllocStruct(*sid, args.iter().map(|x| sv(*x)).collect())
        }
        Prim::Extern(eid, args) => Prim::Extern(*eid, args.iter().map(|x| sv(*x)).collect()),
        Prim::ListCons(a, b) => Prim::ListCons(sv(*a), sv(*b)),
        Prim::ListHead(a) => Prim::ListHead(sv(*a)),
        Prim::ListTail(a) => Prim::ListTail(sv(*a)),
        Prim::ListIsNil(a) => Prim::ListIsNil(sv(*a)),
        Prim::MakeTuple(args) => Prim::MakeTuple(args.iter().map(|x| sv(*x)).collect()),
        Prim::TupleField(a, i) => Prim::TupleField(sv(*a), *i),
        Prim::MakeList(els, tail) => {
            Prim::MakeList(els.iter().map(|x| sv(*x)).collect(), tail.map(sv))
        }
        Prim::MakeClosure(fid, caps, sid) => {
            Prim::MakeClosure(*fid, caps.iter().map(|x| sv(*x)).collect(), *sid)
        }
        Prim::MakeMap(entries) => {
            Prim::MakeMap(entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect())
        }
        Prim::MapUpdate(base, entries) => Prim::MapUpdate(
            sv(*base),
            entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect(),
        ),
        Prim::MapGet(a, b) => Prim::MapGet(sv(*a), sv(*b)),
        Prim::MakeVec(kind, els) => Prim::MakeVec(*kind, els.iter().map(|x| sv(*x)).collect()),
        Prim::ConstBitstring(bytes, bit_len) => Prim::ConstBitstring(bytes.clone(), *bit_len),
        Prim::MakeBitstring(fields) => Prim::MakeBitstring(
            fields
                .iter()
                .map(|f| crate::fz_ir::BitFieldIr {
                    value: sv(f.value),
                    ty: f.ty,
                    size: f.size.as_ref().map(|s| match s {
                        BitSizeIr::Literal(n) => BitSizeIr::Literal(*n),
                        BitSizeIr::Var(v) => BitSizeIr::Var(sv(*v)),
                    }),
                    endian: f.endian,
                    signed: f.signed,
                    unit: f.unit,
                })
                .collect(),
        ),
        Prim::BitReaderInit(a) => Prim::BitReaderInit(sv(*a)),
        Prim::BitReaderDone(a) => Prim::BitReaderDone(sv(*a)),
        Prim::BitReadField {
            reader,
            ty,
            size,
            endian,
            signed,
            unit,
            is_last,
        } => Prim::BitReadField {
            reader: sv(*reader),
            ty: *ty,
            size: size.as_ref().map(|s| match s {
                BitSizeIr::Literal(n) => BitSizeIr::Literal(*n),
                BitSizeIr::Var(v) => BitSizeIr::Var(sv(*v)),
            }),
            endian: *endian,
            signed: *signed,
            unit: *unit,
            is_last: *is_last,
        },
        Prim::TypeTest(a, d) => Prim::TypeTest(sv(*a), d.clone()),
    }
}

fn subst_cont(c: &Cont, subst: &HashMap<Var, Var>) -> Cont {
    Cont {
        fn_id: c.fn_id,
        captured: c.captured.iter().map(|x| subst_var(*x, subst)).collect(),
        sid: None,
    }
}

pub(crate) fn subst_term(t: &Term, subst: &HashMap<Var, Var>) -> Term {
    let sv = |v: Var| subst_var(v, subst);
    match t {
        // BlockId targets are NOT substituted — only Var args are.
        Term::Goto(b, args) => Term::Goto(*b, args.iter().map(|x| sv(*x)).collect()),
        Term::If(cond, then_b, else_b) => Term::If(sv(*cond), *then_b, *else_b),
        Term::Call {
            callee,
            args,
            continuation,
            ..
        } => Term::Call {
            callee: *callee,
            args: args.iter().map(|x| sv(*x)).collect(),
            continuation: subst_cont(continuation, subst),
            callsite_sid: None,
        },
        Term::TailCall {
            callee,
            args,
            is_back_edge,
            ..
        } => Term::TailCall {
            callee: *callee,
            args: args.iter().map(|x| sv(*x)).collect(),
            is_back_edge: *is_back_edge,
            callsite_sid: None,
        },
        Term::CallClosure {
            closure,
            args,
            continuation,
            ..
        } => Term::CallClosure {
            closure: sv(*closure),
            args: args.iter().map(|x| sv(*x)).collect(),
            continuation: subst_cont(continuation, subst),
            resolved_sid: None,
        },
        Term::TailCallClosure { closure, args, .. } => Term::TailCallClosure {
            closure: sv(*closure),
            args: args.iter().map(|x| sv(*x)).collect(),
            resolved_sid: None,
        },
        Term::Return(a) => Term::Return(sv(*a)),
        Term::Halt(a) => Term::Halt(sv(*a)),
        Term::Receive { continuation, .. } => Term::Receive {
            continuation: subst_cont(continuation, subst),
        },
    }
}

pub(crate) fn subst_stmt(s: &Stmt, subst: &HashMap<Var, Var>) -> Stmt {
    let Stmt::Let(v, p) = s;
    // The bound variable `v` is never substituted — it's a definition site,
    // not a use. Only Vars that appear as operands in `p` are substituted.
    Stmt::Let(*v, subst_prim(p, subst))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, Prim, Term};

    /// Build helper: single-entry fn A → B (A ends with Goto(B, [x])).
    /// B has one param `p`, one stmt `let r = p + const(1)`, returns r.
    fn build_a_to_b() -> FnIr {
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var(); // v0 — entry param
        let entry = b.block(vec![x]); // A = block0
        let const41 = b.let_(entry, Prim::Const(Const::Int(41))); // v1

        let p = b.fresh_var(); // v2 — B's param
        let succ = b.block(vec![p]); // B = block1

        // A → B with arg = v1 (the 41 constant)
        b.set_terminator(entry, Term::Goto(succ, vec![const41]));

        // B: let r = p + const(1); return r
        let one = b.let_(succ, Prim::Const(Const::Int(1))); // v3
        let r = b.let_(succ, Prim::BinOp(BinOp::Add, p, one)); // v4
        b.set_terminator(succ, Term::Return(r));
        b.build()
    }

    #[test]
    fn fuse_single_predecessor_block() {
        let mut f = build_a_to_b();
        assert_eq!(f.blocks.len(), 2);
        fuse_fn(&mut f);
        assert_eq!(f.blocks.len(), 1, "B should be fused into A");
        let entry = f.block(f.entry);
        // A should have A's original stmt (const 41) + B's stmts (const 1, add)
        assert_eq!(entry.stmts.len(), 3, "merged block should have 3 stmts");
    }

    #[test]
    fn no_fuse_multi_predecessor() {
        // A → C and B → C: C has two predecessors, must not be fused.
        let mut fb = FnBuilder::new(FnId(0), "f");
        let x = fb.fresh_var(); // v0
        let entry = fb.block(vec![x]); // A
        let b_blk = fb.block(vec![]); // B
        let p = fb.fresh_var(); // v1 — C's param
        let c_blk = fb.block(vec![p]); // C

        let v = fb.let_(entry, Prim::Const(Const::Int(1))); // v2
        fb.set_terminator(entry, Term::Goto(c_blk, vec![v]));

        // B's own stmt and Goto to C
        let w = fb.let_(b_blk, Prim::Const(Const::Int(2))); // v3
        fb.set_terminator(b_blk, Term::Goto(c_blk, vec![w]));

        fb.set_terminator(c_blk, Term::Return(p));
        let mut f = fb.build();

        // We need A to jump to B first so B is reachable — but actually for
        // this test A is entry and A → C; B → C; but B is unreachable from A.
        // The predecessor count is what matters. B still contributes a pred
        // edge to C via its terminator. Let's keep as-is: 3 blocks, C has 2 preds.
        assert_eq!(f.blocks.len(), 3);
        fuse_fn(&mut f);
        // C has 2 preds → must NOT be fused. B has 0 preds from A, but the
        // algorithm counts raw terminator edges, so B remains.
        assert_eq!(f.blocks.len(), 3, "C must not be fused (2 predecessors)");
    }

    #[test]
    fn no_fuse_if_target() {
        // A ends with If(cond, B, C). B and C each have one pred but A's
        // terminator is If, not Goto, so neither is fused.
        let mut fb = FnBuilder::new(FnId(0), "f");
        let x = fb.fresh_var(); // v0
        let entry = fb.block(vec![x]); // A
        let then_b = fb.block(vec![]); // B
        let else_b = fb.block(vec![]); // C

        let zero = fb.let_(entry, Prim::Const(Const::Int(0))); // v1
        let cond = fb.let_(entry, Prim::BinOp(BinOp::Eq, x, zero)); // v2
        fb.set_terminator(entry, Term::If(cond, then_b, else_b));

        let t = fb.let_(then_b, Prim::Const(Const::Int(1))); // v3
        fb.set_terminator(then_b, Term::Return(t));

        let fl = fb.let_(else_b, Prim::Const(Const::Int(0))); // v4
        fb.set_terminator(else_b, Term::Return(fl));

        let mut f = fb.build();
        assert_eq!(f.blocks.len(), 3);
        fuse_fn(&mut f);
        assert_eq!(f.blocks.len(), 3, "If-targeted blocks must not be fused");
    }

    #[test]
    fn fuse_chain_abc() {
        // A → B → C — linear chain. After fusion, everything in A.
        let mut fb = FnBuilder::new(FnId(0), "f");
        let x = fb.fresh_var(); // v0
        let entry = fb.block(vec![x]); // A

        let p1 = fb.fresh_var(); // v1
        let b_blk = fb.block(vec![p1]); // B

        let p2 = fb.fresh_var(); // v2
        let c_blk = fb.block(vec![p2]); // C

        let v1 = fb.let_(entry, Prim::Const(Const::Int(1))); // v3
        fb.set_terminator(entry, Term::Goto(b_blk, vec![v1]));

        let v2 = fb.let_(b_blk, Prim::Const(Const::Int(2))); // v4
        fb.set_terminator(b_blk, Term::Goto(c_blk, vec![v2]));

        fb.set_terminator(c_blk, Term::Return(p2));

        let mut f = fb.build();
        assert_eq!(f.blocks.len(), 3);
        fuse_fn(&mut f);
        assert_eq!(f.blocks.len(), 1, "A→B→C chain should fuse to 1 block");
    }

    #[test]
    fn fuse_substitutes_params() {
        // A: let c = const(41); goto B(c)
        // B(p): let r = p; return r
        // After fuse: A: let c = const(41); let r = c; return r
        let mut fb = FnBuilder::new(FnId(0), "f");
        let entry = fb.block(vec![]); // A

        let p = fb.fresh_var(); // v0 — B's param
        let b_blk = fb.block(vec![p]); // B

        let c = fb.let_(entry, Prim::Const(Const::Int(41))); // v1
        fb.set_terminator(entry, Term::Goto(b_blk, vec![c]));

        // B uses p directly
        fb.set_terminator(b_blk, Term::Return(p));

        let mut f = fb.build();
        fuse_fn(&mut f);
        assert_eq!(f.blocks.len(), 1);
        let entry_blk = f.block(f.entry);
        // Return terminator should reference c (v1), not p (v0)
        match &entry_blk.terminator {
            Term::Return(v) => assert_eq!(*v, c, "param p should be substituted with c"),
            other => panic!("expected Return, got {:?}", other),
        }
    }

    #[test]
    fn entry_absorbs_successor() {
        // Entry A ends with Goto(B, args); B has one pred → B fused INTO A.
        let mut fb = FnBuilder::new(FnId(0), "f");
        let x = fb.fresh_var(); // v0
        let entry = fb.block(vec![x]); // A — entry

        let p = fb.fresh_var(); // v1 — B's param
        let b_blk = fb.block(vec![p]); // B

        fb.set_terminator(entry, Term::Goto(b_blk, vec![x]));

        let one = fb.let_(b_blk, Prim::Const(Const::Int(1))); // v2
        let r = fb.let_(b_blk, Prim::BinOp(BinOp::Add, p, one)); // v3
        fb.set_terminator(b_blk, Term::Return(r));

        let mut f = fb.build();
        assert_eq!(f.blocks.len(), 2);
        fuse_fn(&mut f);
        assert_eq!(f.blocks.len(), 1, "B should be absorbed into entry A");
        // Entry block should now contain B's stmts (const 1, add).
        let entry_blk = f.block(f.entry);
        assert_eq!(entry_blk.stmts.len(), 2);
        // The add should use x (v0) because p (v1) was substituted by x (v0).
        match &entry_blk.stmts[1] {
            Stmt::Let(_, Prim::BinOp(BinOp::Add, lhs, _)) => {
                assert_eq!(*lhs, x, "p should be substituted with x");
            }
            other => panic!("expected BinOp::Add, got {:?}", other),
        }
    }
}
