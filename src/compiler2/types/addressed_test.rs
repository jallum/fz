use super::super::conj::Conj;
use super::super::sigs::{ArrowSig, ClosureLit};
use super::super::{CallableValueKind, ClosureTarget};
use super::AddrStep::{Elem, Field, Param, VarSlot, Variant};
use super::*;
use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};
use crate::compiler2::semantic::SemanticOrd;

fn var(t: &mut Types, id: u32) -> Ty {
    t.type_var(TypeVarId(id))
}

#[test]
fn distinct_params_do_not_conflate_with_repeated_params() {
    // The defect this dissolves: (a, b) must not collapse to (a, a).
    let mut t = Types::new();
    let x = var(&mut t, 100);
    let y = var(&mut t, 101);
    let int = t.int();
    let ab = t.address_arrow(&[x, y], int);
    let aa = t.address_arrow(&[x, x], int);
    assert_ne!(ab, aa, "(a, b) and (a, a) must be distinct interned arrows");
}

#[test]
fn repeated_name_unifies_to_the_first_occurrence_address() {
    // flibble(t, t) :: t  -->  (a0, a0) -> a0
    let mut t = Types::new();
    let tv = var(&mut t, 5);
    let arrow = t.address_arrow(&[tv, tv], tv);
    let a0 = t.param_alpha(0);
    let expected = t.arrow(&[a0, a0], a0);
    assert_eq!(arrow, expected);
}

#[test]
fn nested_components_address_by_path() {
    // foo(a, {b, c}, d)  -->  (a0, {a1_0, a1_1}, a2) -> r0
    let mut t = Types::new();
    let a = var(&mut t, 10);
    let b = var(&mut t, 11);
    let c = var(&mut t, 12);
    let d = var(&mut t, 13);
    let r = var(&mut t, 14); // unnamed result
    let tup = t.tuple(&[b, c]);
    let foo = t.address_arrow(&[a, tup, d], r);

    let a0 = t.param_alpha(0);
    let a1_0 = t.address_var(&[Param(1), Field(0)]);
    let a1_1 = t.address_var(&[Param(1), Field(1)]);
    let a2 = t.param_alpha(2);
    let r0 = t.result_alpha();
    let etup = t.tuple(&[a1_0, a1_1]);
    let expected = t.arrow(&[a0, etup, a2], r0);
    assert_eq!(foo, expected);
}

#[test]
fn input_to_result_identity_is_preserved() {
    // (a, b) -> b stays (a, b) -> b, never (a, b) -> a.
    let mut t = Types::new();
    let x = var(&mut t, 20);
    let y = var(&mut t, 21);
    let arrow = t.address_arrow(&[x, y], y);
    let a0 = t.param_alpha(0);
    let a1 = t.param_alpha(1);
    let right = t.arrow(&[a0, a1], a1);
    let wrong = t.arrow(&[a0, a1], a0);
    assert_eq!(arrow, right, "result must reuse the second parameter's address");
    assert_ne!(arrow, wrong, "result must not collapse onto the first parameter");
}

#[test]
fn parameter_address_is_independent_of_sibling_arity() {
    // d is a2 whether the second parameter's tuple has two fields or three.
    let mut t = Types::new();
    let a = var(&mut t, 30);
    let b = var(&mut t, 31);
    let c = var(&mut t, 32);
    let e = var(&mut t, 33);
    let d = var(&mut t, 34);
    let r2 = var(&mut t, 35);
    let r3 = var(&mut t, 36);
    let tup2 = t.tuple(&[b, c]);
    let foo2 = t.address_arrow(&[a, tup2, d], r2);
    let tup3 = t.tuple(&[b, c, e]);
    let foo3 = t.address_arrow(&[a, tup3, d], r3);

    let a2 = t.param_alpha(2);
    let arg2_of_foo2 = t.callable_clauses(&foo2).unwrap()[0].args[2];
    let arg2_of_foo3 = t.callable_clauses(&foo3).unwrap()[0].args[2];
    assert_eq!(arg2_of_foo2, a2);
    assert_eq!(arg2_of_foo3, a2, "growing the sibling tuple must not renumber d");
}

#[test]
fn shared_name_crosses_depth() {
    // g(t, {t, u})  -->  (a0, {a0, a1_1}) -> r0
    let mut t = Types::new();
    let tv = var(&mut t, 40);
    let u = var(&mut t, 41);
    let r = var(&mut t, 42);
    let tup = t.tuple(&[tv, u]);
    let g = t.address_arrow(&[tv, tup], r);

    let a0 = t.param_alpha(0);
    let a1_1 = t.address_var(&[Param(1), Field(1)]);
    let etup = t.tuple(&[a0, a1_1]);
    let r0 = t.result_alpha();
    let expected = t.arrow(&[a0, etup], r0);
    assert_eq!(g, expected, "t reuses a0 inside the tuple; u addresses to a1_1");
}

#[test]
fn tagged_union_payload_variables_are_addressed_per_variant() {
    // {:cont, b} | {:halt, c} keeps b and c independent even though both
    // payloads occupy tuple field 1. Repeated b in another arm still reuses
    // b's first address through the original-variable map.
    let mut t = Types::new();
    let b = var(&mut t, 50);
    let c = var(&mut t, 51);
    let cont = {
        let tag = t.atom_lit("cont");
        t.tuple(&[tag, b])
    };
    let halt = {
        let tag = t.atom_lit("halt");
        t.tuple(&[tag, c])
    };
    let suspend = {
        let tag = t.atom_lit("suspend");
        t.tuple(&[tag, b])
    };
    let cont_or_halt = t.union(cont, halt);
    let state = t.union(cont_or_halt, suspend);
    let addressed = t.address_inputs(&[state])[0];

    let b_addr = t.address_var(&[Param(0), Variant(0), Field(1)]);
    let c_addr = t.address_var(&[Param(0), Variant(1), Field(1)]);
    assert_ne!(b_addr, c_addr, "different tagged arms must not conflate b and c");

    let cont = {
        let tag = t.atom_lit("cont");
        t.tuple(&[tag, b_addr])
    };
    let halt = {
        let tag = t.atom_lit("halt");
        t.tuple(&[tag, c_addr])
    };
    let suspend = {
        let tag = t.atom_lit("suspend");
        t.tuple(&[tag, b_addr])
    };
    let expected = {
        let two = t.union(cont, halt);
        t.union(two, suspend)
    };
    assert_eq!(addressed, expected);
}

#[test]
fn address_inputs_is_idempotent_for_existing_element_addresses() {
    let mut t = Types::new();
    let head_a = t.address_var(&[Param(1), Elem]);
    let head_b = t.address_var(&[Param(1), Elem, VarSlot(0)]);
    let head = t.union(head_a, head_b);
    let list = t.non_empty_list(head);
    let scalar = t.param_alpha(0);
    let once = t.address_inputs(&[scalar, list]);
    let twice = t.address_inputs(&once);

    assert_eq!(
        twice, once,
        "re-addressing canonical list evidence must not append fresh VarSlot components"
    );
}

#[test]
fn captured_values_and_nested_callable_binders_keep_scoped_correlations() {
    let mut t = Types::new();
    let shared_address = t.param_alpha(0);
    let nested = t.intern(Descr {
        funcs: vec![Conj::pos_of(ArrowSig {
            args: vec![shared_address],
            ret: shared_address,
            lit: Some(ClosureLit {
                kind: CallableValueKind::Closure,
                fn_id: Some(ClosureTarget(7).into()),
                captures: vec![shared_address, shared_address],
            }),
        })],
        ..Descr::unbranded()
    });
    let closure = t.closure_lit(ClosureTarget(8), vec![shared_address, nested], 1);

    t.define_test_callable(ClosureTarget(7), "nested", 1);
    t.define_test_callable(ClosureTarget(8), "outer", 1);
    let root = RootId::for_test(1);
    let function = FunctionId::from_coordinate(2);
    let key = ActivationKey::from_inputs(root, function, &[closure], &mut t);
    let once = key.inputs(&t);
    let outer_captures = t
        .closure_lit_parts(&once[0])
        .expect("addressed closure literal")
        .captures;
    assert_eq!(
        t.display(&outer_captures[0]),
        "a0_c0",
        "the prior value-surface address must be re-owned by the outer capture"
    );
    let nested_clause = t.callable_clauses(&outer_captures[1]).expect("nested callable")[0].clone();
    let nested_captures = t
        .closure_lit_parts(&outer_captures[1])
        .expect("nested closure literal")
        .captures;
    assert_eq!(
        nested_clause.args[0], shared_address,
        "the independent nested callable binder must preserve its own established address"
    );
    assert_eq!(
        nested_clause.args[0], nested_clause.ret,
        "the nested callable's arg/result correlation must survive"
    );
    assert_eq!(
        nested_captures,
        vec![nested_clause.args[0], nested_clause.args[0]],
        "repeated captures in the nested binder must reuse its callable occurrence"
    );
    assert_ne!(
        outer_captures[0], nested_clause.args[0],
        "identically spelled addresses from independent value and callable scopes must not alias"
    );

    let repeated = ActivationKey::from_inputs(root, function, &once, &mut t);
    assert_eq!(
        repeated.arrow, key.arrow,
        "re-addressing an activation key must preserve every scoped correlation exactly"
    );
}

#[test]
fn generic_named_closure_capture_is_structural_and_stable_across_worlds() {
    fn relative_order(target: ClosureTarget, reverse_mint: bool) -> std::cmp::Ordering {
        let mut t = Types::new();
        if reverse_mint {
            let _ = t.float();
            let _ = t.int();
        } else {
            let _ = t.int();
            let _ = t.float();
        }
        let generic = var(&mut t, 91);
        t.define_test_callable(target, "pkg::map", 1);
        let closure = t.closure_lit(target, vec![generic], 1);
        let activation =
            ActivationKey::from_inputs(RootId::for_test(3), FunctionId::from_coordinate(4), &[closure], &mut t);
        let input = activation.inputs(&t)[0];
        let capture = t.closure_lit_parts(&input).expect("named closure literal").captures[0];

        assert_eq!(t.display(&capture), "a0_c0");
        assert!(
            t.free_var_ids(&activation.arrow)
                .iter()
                .all(|id| address_path(&t.address_paths, *id).is_some()),
            "the complete named-closure activation must contain structural addresses only"
        );
        let int = t.int();
        let ground = ActivationKey::from_inputs(RootId::for_test(3), FunctionId::from_coordinate(4), &[int], &mut t);
        activation.semantic_cmp(&ground, &t)
    }

    assert_eq!(
        relative_order(ClosureTarget(17), false),
        relative_order(ClosureTarget(29), true),
        "typed callable identities and structural capture addresses, not local mint ids, own the order"
    );
}

#[test]
fn capture_only_generic_is_reowned_beneath_its_literal() {
    let mut t = Types::new();
    let shared = var(&mut t, 93);
    let target = ClosureTarget(18);
    let closure = t.closure_lit(target, vec![shared], 1);

    let addressed = t.address_inputs(&[shared, closure]);
    let capture = t
        .closure_lit_parts(&addressed[1])
        .expect("addressed closure literal")
        .captures[0];

    assert_eq!(t.display(&addressed[0]), "a0");
    assert_eq!(t.display(&capture), "a1_c0");
    assert_ne!(
        addressed[0], capture,
        "a capture may share an arrow binder only through that binder's args or result"
    );
    assert_eq!(
        t.address_inputs(&addressed),
        addressed,
        "capture re-ownership must remain idempotent"
    );
}

#[test]
fn sibling_and_nested_callable_binders_push_and_pop_independently() {
    fn literal_sig(types: &Types, ty: Ty, target: ClosureTarget) -> ArrowSig {
        let fn_id = target.into();
        types
            .descr(&ty)
            .funcs
            .iter()
            .flat_map(|conj| conj.pos.iter().chain(&conj.neg))
            .find(|sig| sig.lit.as_ref().is_some_and(|lit| lit.fn_id == Some(fn_id)))
            .cloned()
            .expect("literal callable clause")
    }

    let mut t = Types::new();
    let shared = var(&mut t, 92);
    let captured = t.address_var(&[Param(5)]);
    let nested_address = t.param_alpha(0);
    let nested_target = ClosureTarget(30);
    let first_target = ClosureTarget(31);
    let second_target = ClosureTarget(32);
    let nested = t.intern(Descr {
        funcs: vec![Conj::pos_of(ArrowSig {
            args: vec![nested_address],
            ret: nested_address,
            lit: Some(ClosureLit {
                kind: CallableValueKind::Closure,
                fn_id: Some(nested_target.into()),
                captures: vec![nested_address],
            }),
        })],
        ..Descr::unbranded()
    });
    let concrete = t.int();
    let siblings = t.intern(Descr {
        funcs: vec![
            Conj::pos_of(ArrowSig {
                args: vec![shared],
                ret: shared,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: Some(first_target.into()),
                    captures: vec![captured, shared, nested],
                }),
            }),
            Conj::pos_of(ArrowSig {
                args: vec![concrete, shared],
                ret: shared,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: Some(second_target.into()),
                    captures: vec![concrete, shared, captured],
                }),
            }),
        ],
        ..Descr::unbranded()
    });

    let addressed = t.address_inputs(&[siblings])[0];
    let first = literal_sig(&t, addressed, first_target);
    let second = literal_sig(&t, addressed, second_target);
    let first_lit = first.lit.as_ref().expect("first literal");
    let second_lit = second.lit.as_ref().expect("second literal");
    let nested = literal_sig(&t, first_lit.captures[2], nested_target);

    assert_eq!(first.args[0], first.ret);
    assert_eq!(first.args[0], first_lit.captures[1]);
    assert_eq!(nested.args[0], nested.ret);
    assert_eq!(nested.args[0], nested.lit.as_ref().expect("nested literal").captures[0]);
    assert_eq!(second.args[1], second.ret);
    assert_eq!(second.args[1], second_lit.captures[1]);
    assert_ne!(
        first_lit.captures[0], second_lit.captures[2],
        "an established captured value must be re-owned inside each sibling binder"
    );
    assert_ne!(
        first.args[0], nested.args[0],
        "a nested binder must shadow its parent binder"
    );
    assert_eq!(
        first.args[0], second.args[1],
        "one unaddressed source generic intentionally shared across siblings must stay correlated"
    );
    assert_ne!(
        nested.args[0], second.args[1],
        "popping the nested binder must restore sibling isolation"
    );

    let repeated = t.address_inputs(&[addressed])[0];
    assert_eq!(repeated, addressed, "scoped addressing must be idempotent");
}

#[test]
fn addresses_display_structurally_and_free_vars_stay_alpha() {
    // The legibility intent (fz-hwn.27.13): a canonical address renders by
    // its structural slot, while a free var renders as the bare `αN` — so
    // "is this canonical?" is answerable from the rendering alone.
    let mut t = Types::new();
    let a0 = t.param_alpha(0);
    let r0 = t.result_alpha();
    let a1_0 = t.address_var(&[Param(1), Field(0)]);
    assert_eq!(t.display(&a0), "a0");
    assert_eq!(t.display(&r0), "r0");
    assert_eq!(t.display(&a1_0), "a1_0", "a nested address renders by its path");

    let free = var(&mut t, 7);
    assert_eq!(t.display(&free), "α7", "a free var keeps the bare αN rendering");
}

#[test]
fn closure_surface_vars_render_as_free_not_addresses() {
    // A closure-surface var shares the low id range with addresses
    // (`closure_var_id(fn, 0)` can equal the first address's raw index), so
    // it MUST be distinguishable: the address tag keeps it rendering `αN`,
    // never a misleading `a0` that would read as canonical.
    let mut t = Types::new();
    // Mint an address first so the low dense slot 0 is claimed by `a0`.
    let _a0 = t.param_alpha(0);
    let closure = t.fn_ref_lit(ClosureTarget(0), 1);
    let shown = t.display(&closure);
    assert!(
        shown.contains('α'),
        "closure-surface vars render as free αN, not as addresses: {shown}",
    );
    assert!(
        !shown.contains("a0"),
        "a closure-surface var must not be mistaken for the address a0: {shown}",
    );
}

#[test]
fn address_tag_is_transparent_to_interning() {
    // Tagging an address id changes only its NUMBER; structurally identical
    // arrows must still fold to one interned identity, and (a, b) must still
    // differ from (a, a). The calculator reads vars by identity, never by
    // magnitude, so the tag cannot perturb equality.
    let mut t = Types::new();
    let x = var(&mut t, 100);
    let y = var(&mut t, 101);
    let int = t.int();
    let one = t.address_arrow(&[x, y], int);
    let two = t.address_arrow(&[y, x], int);
    assert_eq!(one, two, "alpha-equivalent arrows fold to one identity under tagging");
    let aa = t.address_arrow(&[x, x], int);
    assert_ne!(one, aa, "distinct params stay distinct under tagging");
}
