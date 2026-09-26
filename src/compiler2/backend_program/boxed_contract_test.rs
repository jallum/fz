use std::rc::Rc;

use super::tests::{caller, wrapper};
use super::{BoxedApplyRequirement, BoxedContracts};
use crate::compiler2::artifact::{
    AbiValueRepr, BackendBody, BackendCallArg, BackendCallableReturn, BackendEntry, BackendEntryOrigin,
    BackendExecutable, BackendReturnFlow, BackendReturnLayout, BackendTail, BackendValueLayout, ClosureCallEdge,
};
use crate::compiler2::body::ControlDestination;
use crate::compiler2::identity::{ExecutableKey, RootId};
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{LaneId, ShapeDescr};
use crate::compiler2::{CallSiteId, ControlEntryId, ValueId, World};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;

/// One caller body holding a single boxed closure call: no target is named
/// and `callee` publishes a word, so the call goes through the apply seam.
fn boxed_caller_body(
    world: &mut World,
    key: &ExecutableKey,
    return_flow: BackendReturnFlow,
    caller_return_reprs: Vec<AbiValueRepr>,
) -> BackendExecutable {
    let int = world.types_mut().int();
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let layout = |reprs: Vec<AbiValueRepr>| BackendValueLayout {
        structural: nothing,
        carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
        tys: Box::default(),
        reprs: reprs.into_boxed_slice(),
    };
    let callee = ValueId::from_u32(1);
    let mut executable = BackendExecutable::for_test(key.clone(), int, nothing);
    let abi = Rc::make_mut(&mut executable.abi);
    abi.value_layouts.insert(callee, layout(vec![AbiValueRepr::ValueRef]));
    abi.return_layout = BackendReturnLayout {
        layout: layout(caller_return_reprs),
        diverges: false,
    };
    executable.body = BackendBody::Clauses {
        clauses: Vec::new(),
        generated: Vec::new(),
        entries: vec![BackendEntry {
            span: Span::DUMMY,
            origin: BackendEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: Vec::new(),
            tail: BackendTail::ClosureCall {
                value: ValueId::from_u32(2),
                callsite: CallSiteId::from_u32(0),
                callee,
                edge: ClosureCallEdge::Seam,
                args: vec![BackendCallArg {
                    value: ValueId::from_u32(3),
                    ownership: crate::fz_ir::OwnershipMode::Share,
                }],
                dest: ControlDestination::Return,
                return_flow: Some(return_flow),
            },
        }],
    };
    executable
}

/// A tail call through the seam returns the seam's word to this body's own
/// caller, so this body's return form IS the convention under test. Leaving
/// it unrecorded leaves the one call shape that cannot adapt the result
/// unchecked.
#[test]
fn a_tail_call_through_the_seam_records_its_own_return_as_the_requirement() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let executable = boxed_caller_body(&mut world, &key, BackendReturnFlow::Tail, vec![AbiValueRepr::RawInt]);

    let requirements = BoxedApplyRequirement::for_body(&executable.body, &executable.abi);

    let [requirement] = requirements.as_ref() else {
        panic!("a tail boxed call states what its caller will read back, not nothing: {requirements:?}")
    };
    assert_eq!(
        requirement.delivered.as_ref(),
        [AbiValueRepr::RawInt],
        "what a tail call reads back is this body's own return form"
    );
}

/// Lane COUNT is not the convention. A caller reading one raw integer and a
/// wrapper handing back one boxed word agree on width and disagree on
/// everything else; the caller prints the pointer.
#[test]
fn one_raw_lane_does_not_satisfy_a_wrapper_that_hands_back_a_boxed_word() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let executable = boxed_caller_body(
        &mut world,
        &key,
        BackendReturnFlow::Deliver {
            source: Box::new(BackendReturnLayout {
                layout: BackendValueLayout {
                    structural: nothing,
                    carrier: TransportCarrier::Absent,
                    tys: Box::default(),
                    reprs: Box::new([AbiValueRepr::RawInt]),
                },
                diverges: false,
            }),
            entry: ControlEntryId::from_u32(0),
        },
        vec![AbiValueRepr::RawInt],
    );
    let requirements = BoxedApplyRequirement::for_body(&executable.body, &executable.abi);
    let returning = wrapper(&key, 1, BackendCallableReturn::ValueRef);

    let tel = ConfiguredTelemetry::new();
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &requirements, world.types());
    contracts.replace_wrapper(None, Some(&returning), world.types());

    assert!(
        contracts.validate(&tel, RootId::for_test(0)).is_err(),
        "a raw-integer destination cannot accept the seam's boxed word"
    );
}

#[test]
fn replacement_and_withdrawal_preserve_mismatch_rejection_and_agreement() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let zero = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::default(),
    }];
    let one = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::new([AbiValueRepr::ValueRef]),
    }];
    let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
    let returning = wrapper(&key, 1, BackendCallableReturn::ValueRef);
    let divergent = wrapper(&key, 1, BackendCallableReturn::Diverges);
    let tel = ConfiguredTelemetry::new();
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &one, world.types());
    contracts.replace_wrapper(None, Some(&absent), world.types());
    assert!(
        contracts.validate(&tel, RootId::for_test(0)).is_err(),
        "one delivered lane cannot accept an absent wrapper"
    );
    let invalid_snapshot = contracts.clone();
    contracts.replace_wrapper(Some(&absent), Some(&returning), world.types());
    assert!(contracts.validate(&tel, RootId::for_test(0)).is_ok());
    assert!(
        invalid_snapshot.validate(&tel, RootId::for_test(0)).is_err(),
        "an old snapshot retains its original contract"
    );
    contracts.replace_caller(&key, &one, &zero, world.types());
    assert!(
        contracts.validate(&tel, RootId::for_test(0)).is_err(),
        "replacing caller demand must recheck the same arity"
    );
    contracts.replace_wrapper(Some(&returning), Some(&divergent), world.types());
    assert!(
        contracts.validate(&tel, RootId::for_test(0)).is_ok(),
        "a divergent wrapper is not a returning party"
    );
    contracts.replace_wrapper(Some(&divergent), Some(&absent), world.types());
    assert!(
        contracts.validate(&tel, RootId::for_test(0)).is_ok(),
        "zero-lane agreement remains valid"
    );
    contracts.replace_caller(&key, &zero, &[], world.types());
    contracts.replace_wrapper(Some(&absent), None, world.types());
    assert!(contracts.arities.is_empty());
    assert!(
        contracts.mismatches.is_empty(),
        "withdrawal removes the obsolete invariant witness"
    );
}

#[test]
fn matching_first_lane_does_not_hide_another_conflicting_caller_or_wrapper() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let other = caller(&mut world, "other");
    let requirements = [
        BoxedApplyRequirement {
            arity: 1,
            delivered: Box::default(),
        },
        BoxedApplyRequirement {
            arity: 1,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        },
    ];
    let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
    let returning = wrapper(&other, 1, BackendCallableReturn::ValueRef);
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &requirements, world.types());
    contracts.replace_wrapper(None, Some(&absent), world.types());
    assert_eq!(
        contracts
            .mismatches
            .first()
            .expect("second caller lane differs")
            .delivered
            .as_ref(),
        [AbiValueRepr::ValueRef]
    );
    contracts.replace_caller(&key, &requirements, &requirements[..1], world.types());
    assert!(contracts.mismatches.is_empty());
    contracts.replace_wrapper(None, Some(&returning), world.types());
    assert_eq!(
        contracts
            .mismatches
            .first()
            .expect("second wrapper lane differs")
            .published
            .as_ref(),
        [AbiValueRepr::ValueRef]
    );
    contracts.replace_wrapper(Some(&returning), None, world.types());
    assert!(contracts.mismatches.is_empty());
}

#[test]
fn wrapper_arity_replacement_checks_only_callers_of_its_current_arity() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let one = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::new([AbiValueRepr::ValueRef]),
    }];
    let binary = wrapper(&key, 2, BackendCallableReturn::Absent);
    let unary = wrapper(&key, 1, BackendCallableReturn::Absent);
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &one, world.types());
    contracts.replace_wrapper(None, Some(&binary), world.types());
    assert!(
        contracts.mismatches.is_empty(),
        "the existing invariant relates only matching call arities"
    );
    contracts.replace_wrapper(Some(&binary), Some(&unary), world.types());
    assert!(contracts.mismatches.lookup(&1, &usize::cmp).is_some());
    assert!(
        contracts.arities.lookup(&2, &usize::cmp).is_none(),
        "replacement withdraws the old publication bucket"
    );
    contracts.replace_wrapper(Some(&unary), Some(&binary), world.types());
    assert!(
        contracts.mismatches.is_empty(),
        "moving the wrapper back removes its old disagreement"
    );
}

#[test]
fn equal_contributions_do_no_work_and_changes_retain_unrelated_arity_allocations() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let other = caller(&mut world, "other");
    let one = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::new([AbiValueRepr::ValueRef]),
    }];
    let two = [BoxedApplyRequirement {
        arity: 2,
        delivered: Box::new([AbiValueRepr::ValueRef]),
    }];
    let changed = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::default(),
    }];
    let returning = wrapper(&key, 1, BackendCallableReturn::ValueRef);
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &one, world.types());
    contracts.replace_caller(&other, &[], &two, world.types());
    contracts.replace_wrapper(None, Some(&returning), world.types());
    let before = contracts.clone();
    contracts.replace_caller(&key, &one, &one, world.types());
    contracts.replace_wrapper(Some(&returning), Some(&returning), world.types());
    for arity in [1, 2] {
        assert!(
            Rc::ptr_eq(
                before.arities.lookup(&arity, &usize::cmp).unwrap(),
                contracts.arities.lookup(&arity, &usize::cmp).unwrap()
            ),
            "equal caller and wrapper contributions retain the existing arity allocation"
        );
    }
    contracts.replace_caller(&key, &one, &changed, world.types());
    assert!(!Rc::ptr_eq(
        before.arities.lookup(&1, &usize::cmp).unwrap(),
        contracts.arities.lookup(&1, &usize::cmp).unwrap()
    ));
    assert!(
        Rc::ptr_eq(
            before.arities.lookup(&2, &usize::cmp).unwrap(),
            contracts.arities.lookup(&2, &usize::cmp).unwrap()
        ),
        "a changed contract never rebuilds an unrelated arity's owners"
    );
    assert!(contracts.mismatches.lookup(&1, &usize::cmp).is_some());
    assert!(before.mismatches.is_empty());
}

#[test]
fn withdrawing_one_owner_keeps_other_owners_and_their_mismatch() {
    let mut world = World::new();
    let key = caller(&mut world, "caller");
    let other = caller(&mut world, "other");
    let one = [BoxedApplyRequirement {
        arity: 1,
        delivered: Box::new([AbiValueRepr::ValueRef]),
    }];
    let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
    let other_absent = wrapper(&other, 1, BackendCallableReturn::Absent);
    let mut contracts = BoxedContracts::default();
    contracts.replace_caller(&key, &[], &one, world.types());
    contracts.replace_caller(&other, &[], &one, world.types());
    contracts.replace_wrapper(None, Some(&absent), world.types());
    contracts.replace_wrapper(None, Some(&other_absent), world.types());
    contracts.replace_caller(&key, &one, &[], world.types());
    contracts.replace_wrapper(Some(&absent), None, world.types());
    let mismatch = contracts
        .mismatches
        .first()
        .expect("other contributions still disagree");
    assert_eq!(mismatch.caller, other);
    assert_eq!(mismatch.wrapper.as_ref(), &other_absent.identity);
    contracts.replace_caller(&other, &one, &[], world.types());
    assert!(
        contracts.mismatches.is_empty(),
        "no caller remains to disagree with the wrapper"
    );
}
