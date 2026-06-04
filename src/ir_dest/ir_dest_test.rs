use super::*;
use crate::fz_ir::{Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

fn module_with(stmts: impl IntoIterator<Item = Prim>) -> Module {
    let mut b = FnBuilder::new(FnId(0), "dp_test");
    let entry = b.block(vec![]);
    let mut last = None;
    for prim in stmts {
        last = Some(b.let_(entry, prim));
    }
    b.set_terminator(entry, Term::Halt(last.unwrap_or(Var(0))));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    mb.build()
}

fn const_i(value: i64) -> Prim {
    Prim::Const(Const::Int(value))
}

#[test]
fn lowers_make_tuple_to_destination_skeleton() {
    let mut b = FnBuilder::new(FnId(0), "tuple_dp");
    let entry = b.block(vec![]);
    let a = b.let_(entry, const_i(1));
    let b_value = b.let_(entry, const_i(2));
    let tuple = b.let_(entry, Prim::MakeTuple(vec![a, b_value]));
    b.set_terminator(entry, Term::Halt(tuple));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let mut m = mb.build();

    lower_tuple_destinations(&mut m);
    verify_module(&m).expect("lowered tuple DP must verify");
    let body = m.to_string();
    assert!(body.contains("dest_tuple_begin(arity=2, token=tok0)"));
    assert!(body.contains("dest_tuple_set(v3, tok0, field=0, value=v0, next=tok1)"));
    assert!(body.contains("dest_tuple_set(v3, tok1, field=1, value=v1, next=tok2)"));
    assert!(body.contains("let v2 = dest_freeze(v3, tok2)"));
}

#[test]
fn lowers_make_list_to_destination_cons_chain() {
    let mut b = FnBuilder::new(FnId(0), "list_dp");
    let entry = b.block(vec![]);
    let a = b.let_(entry, const_i(1));
    let b_value = b.let_(entry, const_i(2));
    let list = b.let_(entry, Prim::MakeList(vec![a, b_value], None));
    b.set_terminator(entry, Term::Halt(list));
    let mut mb = ModuleBuilder::new();
    mb.add_fn(b.build());
    let mut m = mb.build();

    lower_list_destinations(&mut m);
    verify_module(&m).expect("lowered list DP must verify");
    let body = m.to_string();
    assert!(body.contains("dest_list_begin(token=tok0)"));
    assert!(body.contains("dest_list_cons(tok0, head=v1, tail=[], next=tok1)"));
    assert!(body.contains("dest_list_cons(tok1, head=v0, tail=v4, next=tok2)"));
    assert!(body.contains("let v2 = dest_list_freeze(v5, tok2)"));
}

#[test]
fn accepts_legal_tuple_skeleton() {
    let m = module_with([
        Prim::DestTupleBegin {
            token: InitTokenId(0),
            arity: 2,
        },
        const_i(10),
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(0),
            index: 0,
            value: Var(1),
            next: InitTokenId(1),
        },
        const_i(20),
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(1),
            index: 1,
            value: Var(3),
            next: InitTokenId(2),
        },
        Prim::DestFreeze {
            dest: Var(0),
            token: InitTokenId(2),
        },
    ]);
    assert_eq!(verify_module(&m), Ok(()));
}

#[test]
fn rejects_duplicate_field_write() {
    let m = module_with([
        Prim::DestTupleBegin {
            token: InitTokenId(0),
            arity: 1,
        },
        const_i(10),
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(0),
            index: 0,
            value: Var(1),
            next: InitTokenId(1),
        },
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(1),
            index: 0,
            value: Var(1),
            next: InitTokenId(2),
        },
        Prim::DestFreeze {
            dest: Var(0),
            token: InitTokenId(2),
        },
    ]);
    let errs = verify_module(&m).expect_err("duplicate field write should fail");
    assert!(errs.iter().any(|e| matches!(
        e.kind,
        DestVerifyErrorKind::DuplicateFieldWrite { dest: Var(0), index: 0 }
    )));
}

#[test]
fn rejects_missing_field_before_freeze() {
    let m = module_with([
        Prim::DestTupleBegin {
            token: InitTokenId(0),
            arity: 2,
        },
        const_i(10),
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(0),
            index: 0,
            value: Var(1),
            next: InitTokenId(1),
        },
        Prim::DestFreeze {
            dest: Var(0),
            token: InitTokenId(1),
        },
    ]);
    let errs = verify_module(&m).expect_err("incomplete freeze should fail");
    assert!(errs.iter().any(|e| matches!(
        &e.kind,
        DestVerifyErrorKind::FreezeIncomplete { dest: Var(0), missing } if missing == &vec![1]
    )));
}

#[test]
fn rejects_token_reuse() {
    let m = module_with([
        Prim::DestTupleBegin {
            token: InitTokenId(0),
            arity: 1,
        },
        const_i(10),
        Prim::DestTupleSet {
            dest: Var(0),
            token: InitTokenId(0),
            index: 0,
            value: Var(1),
            next: InitTokenId(1),
        },
        Prim::DestFreeze {
            dest: Var(0),
            token: InitTokenId(0),
        },
    ]);
    let errs = verify_module(&m).expect_err("token reuse should fail");
    assert!(
        errs.iter()
            .any(|e| matches!(e.kind, DestVerifyErrorKind::TokenReuse(InitTokenId(0))))
    );
}
