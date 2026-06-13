use super::*;
use crate::fz_ir::{BlockId, CallsiteIdent, Cont, DirectCallTarget, FnId, Term, Var};
use crate::types::{ClosureTypes, Types};

fn empty_env() -> HashMap<Var, Ty> {
    HashMap::new()
}
fn empty_fc() -> HashMap<Var, FnId> {
    HashMap::new()
}

#[test]
fn empty_for_non_call_terms() {
    let mut t = crate::types::new();
    let env = empty_env();
    let fc = empty_fc();
    assert!(block_callsites(&mut t, &Term::Goto(BlockId(0), vec![]), &env, &fc).is_empty());
    assert!(block_callsites(&mut t, &Term::if_user(Var(0), BlockId(0), BlockId(1)), &env, &fc).is_empty());
    assert!(block_callsites(&mut t, &Term::Return(Var(0)), &env, &fc).is_empty());
    assert!(block_callsites(&mut t, &Term::Halt(Var(0)), &env, &fc).is_empty());
}

#[test]
fn tail_call_yields_direct_only() {
    let mut ct = crate::types::new();
    let t = Term::TailCall {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::Local(FnId(7)),
        args: vec![Var(1), Var(2)],
        is_back_edge: false,
    };
    let env = empty_env();
    let fc = empty_fc();
    let cs = block_callsites(&mut ct, &t, &env, &fc);
    assert_eq!(cs.len(), 1);
    assert!(matches!(cs[0].slot, EmitSlot::Direct));
    match &cs[0].kind {
        CallsiteKind::Direct { callee, args } => {
            assert_eq!(callee.local_fn_id(), Some(FnId(7)));
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected Direct"),
    }
}

#[test]
fn call_yields_direct_then_cont() {
    let mut tct = crate::types::new();
    let t = Term::Call {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::Local(FnId(5)),
        args: vec![Var(1)],
        continuation: Cont {
            fn_id: FnId(9),
            captured: vec![Var(2)],
        },
    };
    let env = empty_env();
    let fc = empty_fc();
    let cs = block_callsites(&mut tct, &t, &env, &fc);
    assert_eq!(cs.len(), 2);
    assert!(matches!(cs[0].slot, EmitSlot::Direct));
    assert!(matches!(cs[1].slot, EmitSlot::Cont));
    match &cs[1].kind {
        CallsiteKind::Cont {
            cont,
            source: ContSource::Call { callee, .. },
        } => {
            assert_eq!(cont.fn_id.0, 9);
            assert_eq!(callee.local_fn_id(), Some(FnId(5)));
        }
        _ => panic!("expected Cont/Call source"),
    }
}

#[test]
fn tail_call_closure_unresolved_yields_nothing() {
    let mut ct = crate::types::new();
    let term = Term::TailCallClosure {
        ident: CallsiteIdent::synthetic(),
        closure: Var(3),
        args: vec![Var(1)],
        direct_target: None,
    };
    let env = empty_env();
    let fc = empty_fc();
    let cs = block_callsites(&mut ct, &term, &env, &fc);
    assert!(cs.is_empty());
}

#[test]
fn tail_call_closure_known_fns_yields_known() {
    let mut ct = crate::types::new();
    let term = Term::TailCallClosure {
        ident: CallsiteIdent::synthetic(),
        closure: Var(3),
        args: vec![Var(1)],
        direct_target: None,
    };
    let env = empty_env();
    let mut fc = empty_fc();
    fc.insert(Var(3), FnId(11));
    let cs = block_callsites(&mut ct, &term, &env, &fc);
    assert_eq!(cs.len(), 1);
    assert!(matches!(cs[0].slot, EmitSlot::ClosureCall));
}

#[test]
fn tail_call_closure_closure_lit_yields_lit_callsite() {
    let mut ct = crate::types::new();
    let term = Term::TailCallClosure {
        ident: CallsiteIdent::synthetic(),
        closure: Var(3),
        args: vec![Var(1)],
        direct_target: None,
    };
    let mut env = empty_env();
    let cap = ct.int_lit(7);
    env.insert(Var(3), ct.closure_lit(FnId(11).into(), vec![cap], 1));
    let fc = empty_fc();
    let cs = block_callsites(&mut ct, &term, &env, &fc);
    assert_eq!(cs.len(), 1);
    match &cs[0].kind {
        CallsiteKind::ClosureLit { fn_id, captures, args } => {
            assert_eq!(fn_id.0, 11);
            assert_eq!(captures.len(), 1);
            assert_eq!(args.len(), 1);
        }
        _ => panic!("expected ClosureLit"),
    }
}

#[test]
fn call_closure_yields_cont_when_closure_unresolved() {
    let mut tct = crate::types::new();
    let t = Term::CallClosure {
        ident: CallsiteIdent::synthetic(),
        closure: Var(3),
        args: vec![Var(1)],
        continuation: Cont {
            fn_id: FnId(9),
            captured: vec![],
        },
        direct_target: None,
    };
    let env = empty_env();
    let fc = empty_fc();
    let cs = block_callsites(&mut tct, &t, &env, &fc);
    assert_eq!(cs.len(), 1);
    assert!(matches!(cs[0].slot, EmitSlot::Cont));
}
