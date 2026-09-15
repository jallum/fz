use std::rc::Rc;

use super::boxed_contract::tests::{caller, wrapper};
use super::boxed_contract::{BoxedApplyRequirement, BoxedContracts};
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
