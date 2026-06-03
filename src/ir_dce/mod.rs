//! Function-local liveness helpers and DCE.
//!
//! Dead stmts: removes pure stmts whose dest var is not used anywhere in the fn.
//! Fixed-point loop handles chains of dead stmts.
//!
//! Dead blocks: after stmt DCE, prunes blocks unreachable from the entry block.
//! Only Goto and If create intra-function block edges; all other terminators
//! exit to a separate FnIr or terminate execution.
//!
//! The module does not own module-level reachability. Planner/materialization
//! produce reachable executable bodies; this module only answers local liveness
//! questions and removes local dead IR.

use crate::fz_ir::{BitSizeIr, BlockId, FnIr, PhysicalCapability, Prim, Stmt, Term, Var};
use crate::telemetry::Telemetry;
use std::collections::HashSet;

pub fn dce_fn_with_telemetry(module_path: &str, f: &mut FnIr, tel: &dyn Telemetry) {
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
    prune_dead_owned_cons_capabilities(f);

    // Dead block elimination: compute reachable set BEFORE retaining so that
    // f.block(id) — which panics on unknown id — is still safe to call.
    let reachable = reachable_from_entry(f);
    for block in &f.blocks {
        if !reachable.contains(&block.id) {
            tel.execute(
                &["fz", "ir", "dce", "block_pruned"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    block_id: block.id.0 as u64,
                },
                &crate::metadata! {
                    module_path: module_path.to_owned(),
                    fn_name: f.name.clone(),
                    reason: "unreachable",
                },
            );
        }
    }
    f.blocks.retain(|b| reachable.contains(&b.id));
    prune_dead_owned_cons_capabilities(f);
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
            Term::If { then_b, else_b, .. } => {
                work.push(*then_b);
                work.push(*else_b);
            }
            _ => {}
        }
    }
    seen
}

/// Returns `(if_only_conds, all_used)` in a single pass.
///
/// `if_only_conds`: vars used exclusively as Term::If conditions — no prim
/// arg, no other terminator use. Boolean-producing prims whose dest is in
/// this set can skip emitting a tagged form entirely (fz-cg2.3).
///
/// `all_used`: every var referenced in any prim arg or terminator arg;
/// equivalent to the previous `collect_used` return value.
pub fn classify_var_uses(f: &FnIr) -> (HashSet<Var>, HashSet<Var>) {
    let mut if_conds: HashSet<Var> = HashSet::new();
    let mut other_uses: HashSet<Var> = HashSet::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            collect_prim_vars(prim, &mut other_uses);
        }
        match &block.terminator {
            Term::If { cond, .. } => {
                if_conds.insert(*cond);
            }
            t => collect_term_vars(t, &mut other_uses),
        }
    }
    let mut all_used = other_uses.clone();
    all_used.extend(if_conds.iter().cloned());
    let if_only_conds: HashSet<Var> = if_conds.into_iter().filter(|v| !other_uses.contains(v)).collect();
    (if_only_conds, all_used)
}

pub fn collect_used(f: &FnIr) -> HashSet<Var> {
    let semantic_used = classify_var_uses(f).1;
    let mut used = semantic_used.clone();
    for fact in &f.physical_capabilities {
        match fact.capability {
            PhysicalCapability::OwnedConsReuse { head } if semantic_used.contains(&head) => {
                used.insert(fact.source);
            }
            _ => {}
        }
    }
    used
}

fn prune_dead_owned_cons_capabilities(f: &mut FnIr) {
    let semantic_used = classify_var_uses(f).1;
    f.physical_capabilities.retain(|fact| match fact.capability {
        PhysicalCapability::OwnedConsReuse { head } => semantic_used.contains(&head),
    });
    let live_sources: HashSet<Var> = f.physical_capabilities.iter().map(|fact| fact.source).collect();
    let entry_params: HashSet<Var> = f.block(f.entry).params.iter().copied().collect();
    f.physical_entry_params
        .retain(|param| entry_params.contains(param) && live_sources.contains(param));
    f.dedup_physical_facts();
}

fn collect_prim_vars(p: &Prim, used: &mut HashSet<Var>) {
    match p {
        Prim::Const(_) | Prim::MakeFnRef(_, _) => {}
        Prim::BinOp(_, a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::UnOp(_, a) => {
            used.insert(*a);
        }
        Prim::Extern(_, _, args) => {
            for arg in args {
                used.insert(arg.var);
            }
        }
        Prim::ListHead(a) | Prim::ListTail(a) | Prim::IsEmptyList(a) | Prim::IsListCons(a) => {
            used.insert(*a);
        }
        Prim::MakeTuple(args) => {
            for v in args {
                used.insert(*v);
            }
        }
        Prim::MakeStruct { fields, .. } => {
            for (_, v) in fields {
                used.insert(*v);
            }
        }
        Prim::DestTupleBegin { .. } => {}
        Prim::DestTupleSet { dest, value, .. } => {
            used.insert(*dest);
            used.insert(*value);
        }
        Prim::DestFreeze { dest, .. } => {
            used.insert(*dest);
        }
        Prim::DestListBegin { .. } => {}
        Prim::DestListCons { head, tail, .. } => {
            used.insert(*head);
            if let Some(tail) = tail {
                used.insert(*tail);
            }
        }
        Prim::DestListFreeze { list, .. } => {
            used.insert(*list);
        }
        Prim::TupleField(a, _) | Prim::StructField(a, _) => {
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
        Prim::MakeClosure(_, _, caps) => {
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
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                used.insert(*base);
            }
        }
        Prim::DestMapPut { map, key, value, .. } => {
            used.insert(*map);
            used.insert(*key);
            used.insert(*value);
        }
        Prim::DestMapFreeze { map, .. } => {
            used.insert(*map);
        }
        Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
            used.insert(*a);
            used.insert(*b);
        }
        Prim::IsMatcherMapMiss(v) => {
            used.insert(*v);
        }
        Prim::MakeBitstring(fields) => {
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
            if let Some(BitSizeIr::Var(sv)) = size {
                used.insert(*sv);
            }
        }
        Prim::TypeTest(v, _) => {
            used.insert(*v);
        }
        Prim::Brand(_, _) => {
            unreachable!("Prim::Brand reached DCE — erasure should run inside lower_program_full")
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
        Term::If { cond, .. } => {
            used.insert(*cond);
        }
        Term::Call {
            ident: _,
            args,
            continuation,
            ..
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
            ident: _,
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
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            used.insert(*closure);
            for v in args {
                used.insert(*v);
            }
        }
        Term::Return(a) | Term::Halt(a) => {
            used.insert(*a);
        }
        Term::Receive { continuation, ident: _ } => {
            for v in &continuation.captured {
                used.insert(*v);
            }
        }
        // fz-yxs — Vars referenced by ReceiveMatched: pinned and captures
        // are live (passed to matcher / clause-body fns), as is the
        // computed timeout Var if there's an after clause.
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            for (_, v) in pinned {
                used.insert(*v);
            }
            for v in captures {
                used.insert(*v);
            }
            if let Some(a) = after {
                used.insert(a.timeout);
            }
        }
    }
}

fn is_impure(p: &Prim) -> bool {
    matches!(
        p,
        Prim::Extern(..)
            | Prim::DestTupleBegin { .. }
            | Prim::DestTupleSet { .. }
            | Prim::DestFreeze { .. }
            | Prim::DestListBegin { .. }
            | Prim::DestListCons { .. }
            | Prim::DestListFreeze { .. }
            | Prim::DestMapBegin { .. }
            | Prim::DestMapPut { .. }
            | Prim::DestMapFreeze { .. }
            | Prim::BitReaderInit(_)
            | Prim::BitReadField { .. }
            | Prim::BitReaderDone(_)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{
        BinOp, CallsiteIdent, Const, Cont, ExternArg, ExternId, ExternTy, FnBuilder, FnId, ModuleBuilder, Prim, Term,
    };
    use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value};
    use crate::types::{ConcreteTypes, Types};

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

        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);

        let block = m.fns[0].block(m.fns[0].entry);
        assert_eq!(block.stmts.len(), 1, "dead const should be removed");
        match &block.stmts[0] {
            Stmt::Let(_, Prim::Const(Const::Int(42))) => {}
            other => panic!("expected live Const(42), got {:?}", other),
        }
    }

    /// Test 2: Extern with unused dest kept (impure).
    ///
    /// Build: entry has Extern(0, []) whose dest is never used.
    /// DCE must keep it because Extern is impure.
    #[test]
    fn impure_extern_kept_even_if_unused() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let nil_v = b.let_(entry, Prim::Const(Const::Nil)); // arg for extern call
        // Extern(0) with nil as arg — dest is never used.
        let _extern_result = b.let_(
            entry,
            Prim::Extern(
                CallsiteIdent::synthetic(),
                ExternId(0),
                vec![ExternArg::fixed(nil_v, ExternTy::Any)],
            ),
        );
        b.set_terminator(entry, Term::Return(nil_v));
        let f = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);

        let block = m.fns[0].block(m.fns[0].entry);
        // The Extern stmt must remain (impure). nil_v is used by both Extern and Return.
        assert_eq!(
            block.stmts.len(),
            2,
            "impure Extern must be kept; stmts: {:?}",
            block.stmts
        );
        assert!(
            matches!(&block.stmts[1], Stmt::Let(_, Prim::Extern(..))),
            "second stmt should be Extern, got {:?}",
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

        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);

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
                ident: CallsiteIdent::synthetic(),
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

        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);

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
        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);
        assert_eq!(m.fns[0].blocks.len(), 1, "orphan block should be removed");
        assert_eq!(m.fns[0].blocks[0].id, entry);
    }

    #[test]
    fn unreachable_capability_use_does_not_keep_physical_facts() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let source = b.fresh_var();
        let entry = b.block(vec![source]);
        let orphan = b.block(vec![]);

        let nil = b.let_(entry, Prim::MakeList(vec![], None));
        b.set_terminator(entry, Term::Return(nil));

        let head = b.let_(orphan, Prim::ListHead(source));
        b.record_owned_cons_reuse_capability(head, source);
        let tail = b.let_(orphan, Prim::MakeList(vec![], None));
        let result = b.let_(orphan, Prim::MakeList(vec![head], Some(tail)));
        b.set_terminator(orphan, Term::Return(result));

        let mut f = b.build();
        assert_eq!(f.physical_entry_params, vec![source]);
        assert_eq!(f.physical_capabilities.len(), 1);

        dce_fn_with_telemetry("", &mut f, &NullTelemetry);

        assert_eq!(f.blocks.len(), 1, "orphan block should be removed");
        assert!(f.physical_entry_params.is_empty());
        assert!(f.physical_capabilities.is_empty());
    }

    #[test]
    fn telemetry_reports_pruned_block_identity() {
        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());

        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let orphan = b.block(vec![]);
        let nil_e = b.let_(entry, Prim::Const(Const::Nil));
        b.set_terminator(entry, Term::Return(nil_e));
        let nil_o = b.let_(orphan, Prim::Const(Const::Nil));
        b.set_terminator(orphan, Term::Return(nil_o));

        let mut mb = ModuleBuilder::new().with_module_path("Sort");
        mb.add_fn(b.build());
        let mut m = mb.build();

        dce_fn_with_telemetry("Sort", &mut m.fns[0], &tel);

        let ev = cap
            .last(&["fz", "ir", "dce", "block_pruned"])
            .expect("block_pruned event");
        assert!(matches!(ev.measurements.get("fn_id"), Some(Value::U64(0))));
        assert!(matches!(
            ev.measurements.get("block_id"),
            Some(Value::U64(id)) if *id == orphan.0 as u64
        ));
        assert!(matches!(
            ev.metadata.get("module_path"),
            Some(Value::Str(s)) if s.as_ref() == "Sort"
        ));
        assert!(matches!(
            ev.metadata.get("fn_name"),
            Some(Value::Str(s)) if s.as_ref() == "main"
        ));
        assert!(matches!(
            ev.metadata.get("reason"),
            Some(Value::Str(s)) if s.as_ref() == "unreachable"
        ));
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
        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);
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
        b.set_terminator(entry, Term::if_user(cond_v, then_b, else_b));
        let n1 = b.let_(then_b, Prim::Const(Const::Nil));
        b.set_terminator(then_b, Term::Return(n1));
        let n2 = b.let_(else_b, Prim::Const(Const::Nil));
        b.set_terminator(else_b, Term::Return(n2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);
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
        dce_fn_with_telemetry("", &mut m.fns[0], &NullTelemetry);
        assert_eq!(m.fns[0].blocks.len(), 2, "else_b removed by dead block elimination");
        assert_eq!(m.fns[0].blocks[0].id, entry);
        assert!(matches!(m.fns[0].blocks[0].terminator, Term::Goto(target, _) if target == then_b));
    }

    /// fz-jv2 — classify_var_uses correctness.
    ///
    /// Builds a function with:
    ///   block0: let c = TypeTest(x); Term::if_user(c, b_t, b_f)
    ///   block0 has no other use of c → c ∈ if_only_conds
    ///
    /// And a second function where c also appears in a prim arg:
    ///   block0: let c = TypeTest(x); let _ = BinOp(And, c, c); Term::if_user(c, b_t, b_f)
    ///   c ∈ all_used but c ∉ if_only_conds (dual-use)
    #[test]
    fn classify_var_uses_separates_pure_branch_from_dual_use() {
        let mut ct = ConcreteTypes;
        let int_ty = Types::int(&mut ct);
        // --- pure-branch case ---
        let mut bm = FnBuilder::new(FnId(0), "pure");
        let x = bm.fresh_var();
        let entry = bm.block(vec![x]);
        let c = bm.let_(entry, Prim::TypeTest(x, Box::new(int_ty.clone())));
        let t_blk = bm.block(vec![]);
        let f_blk = bm.block(vec![]);
        bm.set_terminator(entry, Term::if_user(c, t_blk, f_blk));
        let nil = bm.let_(t_blk, Prim::Const(Const::Nil));
        bm.set_terminator(t_blk, Term::Return(nil));
        let nil2 = bm.let_(f_blk, Prim::Const(Const::Nil));
        bm.set_terminator(f_blk, Term::Return(nil2));
        let pure_fn = bm.build();

        let (if_only, all_used) = classify_var_uses(&pure_fn);
        assert!(if_only.contains(&c), "pure-branch condition should be in if_only_conds");
        assert!(
            all_used.contains(&c),
            "pure-branch condition should still be in all_used"
        );
        assert!(all_used.contains(&x), "TypeTest operand x should be in all_used");

        // --- dual-use case ---
        let mut bm2 = FnBuilder::new(FnId(1), "dual");
        let x2 = bm2.fresh_var();
        let e2 = bm2.block(vec![x2]);
        let c2 = bm2.let_(e2, Prim::TypeTest(x2, Box::new(int_ty)));
        // c2 used as prim arg → dual-use
        let _ = bm2.let_(e2, Prim::BinOp(BinOp::And, c2, c2));
        let t2 = bm2.block(vec![]);
        let f2 = bm2.block(vec![]);
        bm2.set_terminator(e2, Term::if_user(c2, t2, f2));
        let n2 = bm2.let_(t2, Prim::Const(Const::Nil));
        bm2.set_terminator(t2, Term::Return(n2));
        let n3 = bm2.let_(f2, Prim::Const(Const::Nil));
        bm2.set_terminator(f2, Term::Return(n3));
        let dual_fn = bm2.build();

        let (if_only2, _) = classify_var_uses(&dual_fn);
        assert!(
            !if_only2.contains(&c2),
            "dual-use condition must NOT be in if_only_conds"
        );
    }

    #[test]
    fn owned_cons_source_is_live_only_when_capability_head_is_used() {
        let mut b = FnBuilder::new(FnId(0), "live_capability");
        let source = b.fresh_var();
        let entry = b.block(vec![source]);
        let head = b.let_(entry, Prim::ListHead(source));
        b.record_owned_cons_reuse_capability(head, source);
        let tail = b.let_(entry, Prim::MakeList(vec![], None));
        let result = b.let_(entry, Prim::MakeList(vec![head], Some(tail)));
        b.set_terminator(entry, Term::Return(result));
        let mut f = b.build();

        dce_fn_with_telemetry("", &mut f, &NullTelemetry);

        assert_eq!(f.physical_entry_params.len(), 1);
        assert_eq!(f.physical_capabilities.len(), 1);
        assert!(
            f.block(f.entry)
                .stmts
                .iter()
                .any(|Stmt::Let(_, prim)| matches!(prim, Prim::ListHead(v) if *v == source)),
            "live capability head should keep its source projection alive"
        );

        let mut b = FnBuilder::new(FnId(1), "dead_capability");
        let source = b.fresh_var();
        let entry = b.block(vec![source]);
        let head = b.let_(entry, Prim::ListHead(source));
        b.record_owned_cons_reuse_capability(head, source);
        let nil = b.let_(entry, Prim::MakeList(vec![], None));
        b.set_terminator(entry, Term::Return(nil));
        let mut f = b.build();

        dce_fn_with_telemetry("", &mut f, &NullTelemetry);

        assert!(f.physical_entry_params.is_empty());
        assert!(f.physical_capabilities.is_empty());
        assert!(
            f.block(f.entry)
                .stmts
                .iter()
                .all(|Stmt::Let(_, prim)| !matches!(prim, Prim::ListHead(_))),
            "dead capability head should not keep source projection alive"
        );
    }
}
