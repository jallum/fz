use super::*;
use crate::fz_ir::{
    BinOp, CallsiteIdent, Const, Cont, ExternArg, ExternId, ExternTy, FnBuilder, FnId, ModuleBuilder, Prim, Term,
};
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value};
use crate::types::Types;

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
    let mut ct = crate::types::new();
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
