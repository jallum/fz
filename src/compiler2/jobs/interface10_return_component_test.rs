//! Recovered solver contracts for evidence that ordinary source cannot create
//! reliably: an admitted equation, a missing producer, and strict projections.
//! These are kernel tests, not evidence of normal-path inference replacement.

use super::*;
use crate::compiler2::{FunctionId, RootId};
use crate::telemetry::sink::NullTelemetry;

/// A source/cell-shaped frame has no activation key or embedded input vector.
/// The equation kernel receives its complete formal arity alongside it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SourceFrame(u8);

fn member(types: &mut Types) -> ActivationKey {
    ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[], types)
}

fn answer(member: &ActivationKey, bindings: &Bindings, types: &mut Types) -> Option<Ty> {
    let members = [(member.clone(), 0)];
    solve(&members, bindings, types, &NullTelemetry, member)
        .returns
        .get(member)
        .copied()
}

#[test]
fn closed_alias_cycle_proves_none_while_an_absent_equation_stays_unknown() {
    let mut types = Types::new();
    let member = member(&mut types);
    let closed = Bindings {
        returns: HashMap::from([(member.clone(), vec![Term::Return(member.clone())])]),
        ..Bindings::default()
    };
    let observed = [
        answer(&member, &closed, &mut types),
        answer(&member, &Bindings::default(), &mut types),
    ];
    assert_eq!(
        observed,
        [Some(types.none()), None],
        "a registered closed R = R proves none; missing evidence remains unanswered"
    );
}

#[test]
fn a_dead_tuple_port_overrides_an_unknown_sibling_in_either_order() {
    let mut types = Types::new();
    let member = member(&mut types);
    let none = types.none();
    let int = types.int();
    let ok = types.atom_lit("ok");
    let expected_tuple = types.tuple(&[int, ok]);
    let left = CallSiteId::from_u32(0);
    let right = CallSiteId::from_u32(1);
    let mut bindings = Bindings {
        returns: HashMap::from([(
            member.clone(),
            vec![Term::Shape(
                member.clone(),
                Skeleton::Tuple(vec![
                    Skeleton::Result {
                        callsite: left,
                        value: ValueId::from_u32(0),
                    },
                    Skeleton::Result {
                        callsite: right,
                        value: ValueId::from_u32(1),
                    },
                ]),
            )],
        )]),
        ..Bindings::default()
    };
    let observed = [
        (
            Term::Settled(none),
            Term::Shape(member.clone(), Skeleton::Ground(ValueId::from_u32(99))),
        ),
        (
            Term::Shape(member.clone(), Skeleton::Ground(ValueId::from_u32(99))),
            Term::Settled(none),
        ),
        (
            Term::Settled(int),
            Term::Shape(member.clone(), Skeleton::Ground(ValueId::from_u32(99))),
        ),
        (Term::Settled(int), Term::Settled(ok)),
    ]
    .map(|(a, b)| {
        bindings.results.insert((member.clone(), left), vec![a]);
        bindings.results.insert((member.clone(), right), vec![b]);
        answer(&member, &bindings, &mut types)
    });
    assert_eq!(
        observed,
        [Some(none), Some(none), None, Some(expected_tuple)],
        "dead dominates pending only inside that strict tuple; a live tuple still needs both ports"
    );
}

#[test]
fn explicit_and_simplified_projection_keep_dead_and_unknown_siblings() {
    let mut types = Types::new();
    let member = member(&mut types);
    let none = types.none();
    let int = types.int();
    let tag_ty = types.atom_lit("tag");
    let tag = ValueId::from_u32(1);
    let port = CallSiteId::from_u32(0);
    let observed = [false, true].map(|simplified| {
        [
            Term::Settled(none),
            Term::Shape(member.clone(), Skeleton::Ground(ValueId::from_u32(99))),
            Term::Settled(int),
        ]
        .map(|sibling| {
            let tuple = Skeleton::Tuple(vec![
                Skeleton::Result {
                    callsite: port,
                    value: ValueId::from_u32(0),
                },
                Skeleton::Ground(tag),
            ]);
            let projected = if simplified {
                Skeleton::project(tuple, ProjectStep::TupleField(1))
            } else {
                Skeleton::Project {
                    of: Box::new(tuple),
                    step: ProjectStep::TupleField(1),
                }
            };
            let bindings = Bindings {
                value_types: HashMap::from([(member.clone(), HashMap::from([(tag, tag_ty)]))]),
                returns: HashMap::from([(member.clone(), vec![Term::Shape(member.clone(), projected)])]),
                results: HashMap::from([((member.clone(), port), vec![sibling])]),
                ..Bindings::default()
            };
            answer(&member, &bindings, &mut types)
        })
    });
    assert_eq!(
        observed,
        [[Some(none), None, Some(tag_ty)]; 2],
        "both projection paths preserve the original tuple's execution requirements"
    );
}

#[test]
fn projecting_a_union_drops_dead_branches_but_preserves_unknown_alternatives() {
    let mut types = Types::new();
    let member = member(&mut types);
    let none = types.none();
    let int = types.int();
    let dead = types.atom_lit("dead");
    let live = types.atom_lit("live");
    let left = CallSiteId::from_u32(0);
    let right = CallSiteId::from_u32(1);
    let left_tag = ValueId::from_u32(2);
    let right_tag = ValueId::from_u32(3);
    let projected = Skeleton::Project {
        of: Box::new(Skeleton::Union(vec![
            Skeleton::Tuple(vec![
                Skeleton::Result {
                    callsite: left,
                    value: ValueId::from_u32(0),
                },
                Skeleton::Ground(left_tag),
            ]),
            Skeleton::Tuple(vec![
                Skeleton::Result {
                    callsite: right,
                    value: ValueId::from_u32(1),
                },
                Skeleton::Ground(right_tag),
            ]),
        ])),
        step: ProjectStep::TupleField(1),
    };
    let mut bindings = Bindings {
        value_types: HashMap::from([(member.clone(), HashMap::from([(left_tag, dead), (right_tag, live)]))]),
        returns: HashMap::from([(member.clone(), vec![Term::Shape(member.clone(), projected)])]),
        results: HashMap::from([((member.clone(), right), vec![Term::Settled(int)])]),
        ..Bindings::default()
    };
    let observed = [
        Term::Settled(none),
        Term::Shape(member.clone(), Skeleton::Ground(ValueId::from_u32(99))),
    ]
    .map(|left_result| {
        bindings.results.insert((member.clone(), left), vec![left_result]);
        answer(&member, &bindings, &mut types)
    });
    assert_eq!(
        observed,
        [Some(live), None],
        "an impossible source tuple contributes no tag; an unknown alternative keeps the union pending"
    );
}

#[test]
fn an_argument_equation_keeps_fixed_ports_outside_its_return_dependencies() {
    let mut types = Types::new();
    let int = types.int();
    let seed = types.atom_lit("seed");
    let member = ActivationKey::from_inputs(
        RootId::for_test(0),
        FunctionId::from_coordinate(0),
        &[int, seed],
        &mut types,
    );
    // loop(n, acc) returns acc or calls loop(n-1, {acc}). The first
    // input is fixed, but no return/constructor edge happens to visit it.
    let mut bindings = Bindings {
        returns: HashMap::from([(member.clone(), vec![Term::Slot(member.clone(), 1)])]),
        slots: HashMap::from([
            ((member.clone(), 0), vec![Term::Settled(int)]),
            (
                (member.clone(), 1),
                vec![
                    Term::Settled(seed),
                    Term::Shape(member.clone(), Skeleton::Tuple(vec![Skeleton::Input(1)])),
                ],
            ),
        ]),
        ..Bindings::default()
    };
    let solved = solve(&[(member.clone(), 2)], &bindings, &mut types, &NullTelemetry, &member);
    assert_eq!(
        solved.slots.get(&(member.clone(), 0)).map(ActivationInput::ty),
        Some(int),
        "a component's input row includes fixed formal ports, not only result dependencies"
    );
    let expected = types.intern_regular_component(1, |nodes| {
        vec![union_regular_bodies(
            &DescrOf::atom_lit("seed"),
            &DescrOf::tuple_of(vec![nodes[0]]),
        )]
    })[0];
    assert_eq!(solved.slots[&(member.clone(), 1)].ty(), expected);
    assert_eq!(solved.returns[&member], expected);

    bindings.slots.remove(&(member.clone(), 0));
    let missing = solve(&[(member.clone(), 2)], &bindings, &mut types, &NullTelemetry, &member);
    assert!(
        !missing.slots.contains_key(&(member.clone(), 0)),
        "a formal port without an equation cannot borrow the activation key's type"
    );
    assert_eq!(missing.returns[&member], expected);
}

#[test]
fn a_source_frame_uses_declared_formal_arity_for_recursive_ports() {
    let mut types = Types::new();
    let seed = types.atom_lit("seed");
    let frame = SourceFrame(0);
    let bindings = Bindings::<SourceFrame> {
        returns: HashMap::from([(frame.clone(), vec![Term::Slot(frame.clone(), 0)])]),
        slots: HashMap::from([(
            (frame.clone(), 0),
            vec![
                Term::Settled(seed),
                Term::Shape(frame.clone(), Skeleton::Tuple(vec![Skeleton::Input(0)])),
            ],
        )]),
        ..Bindings::default()
    };

    let solved = solve(&[(frame.clone(), 1)], &bindings, &mut types, &NullTelemetry, &frame);
    let expected = types.intern_regular_component(1, |nodes| {
        vec![union_regular_bodies(
            &DescrOf::atom_lit("seed"),
            &DescrOf::tuple_of(vec![nodes[0]]),
        )]
    })[0];
    assert_eq!(solved.slots[&(frame.clone(), 0)].ty(), expected);
    assert_eq!(solved.returns[&frame], expected);
}

#[test]
fn missing_observations_keep_their_source_port_addresses() {
    let frame = SourceFrame(0);
    let outside = SourceFrame(1);
    let bindings = Bindings::default();
    let equations = Equations::new(&[(frame.clone(), 0)], &bindings);
    let missing = [
        Term::Shape(frame.clone(), Skeleton::Ground(ValueId::from_u32(10))),
        Term::Shape(frame.clone(), Skeleton::Ground(ValueId::from_u32(11))),
        Term::Shape(
            frame,
            Skeleton::Result {
                callsite: CallSiteId::from_u32(2),
                value: ValueId::from_u32(12),
            },
        ),
        Term::Evidence(outside.clone(), 0),
        Term::Return(outside.clone()),
    ];
    for source in missing {
        assert_eq!(
            equations.bind(&source),
            source,
            "missing evidence must retain the port whose publisher can answer it"
        );
    }
    assert_eq!(
        equations.bind(&Term::Slot(outside.clone(), 0)),
        Term::Evidence(outside, 0),
        "an external input remains a named evidence port while absent"
    );
}

#[test]
fn named_missing_sources_survive_projection_and_answer_when_their_publisher_arrives() {
    let mut types = Types::new();
    let frame = SourceFrame(0);
    let outside = SourceFrame(1);
    let bridge = CallSiteId::from_u32(0);
    let missing_call = CallSiteId::from_u32(1);
    let value = ValueId::from_u32(10);
    let sources = [
        Term::Shape(frame.clone(), Skeleton::Ground(value)),
        Term::Shape(
            frame.clone(),
            Skeleton::Result {
                callsite: missing_call,
                value,
            },
        ),
        Term::Evidence(outside.clone(), 0),
        Term::Return(outside),
    ];
    let int = types.int();
    let tuple = types.tuple(&[int]);
    let members = [(frame.clone(), 0)];
    for source in sources {
        let projected = Term::Shape(
            frame.clone(),
            Skeleton::Project {
                of: Box::new(Skeleton::Result {
                    callsite: bridge,
                    value,
                }),
                step: ProjectStep::TupleField(0),
            },
        );
        let mut bindings = Bindings {
            returns: HashMap::from([(frame.clone(), vec![projected])]),
            results: HashMap::from([((frame.clone(), bridge), vec![source.clone()])]),
            ..Bindings::default()
        };
        let mut equations = Equations::new(&members, &bindings);
        equations.build(vec![Unknown::Return(frame.clone())], &mut types, &NullTelemetry, &frame);
        let node = equations.index[&Unknown::Return(frame.clone())];
        assert_eq!(
            equations.branches[node],
            vec![source.clone()],
            "the pending projection must retain exactly the source its alias awaits"
        );
        assert!(
            !solve(&members, &bindings, &mut types, &NullTelemetry, &frame)
                .returns
                .contains_key(&frame),
            "a named pending dependency is still unanswered, never none or any"
        );

        match &source {
            Term::Shape(owner, Skeleton::Ground(value)) => {
                bindings
                    .value_types
                    .entry(owner.clone())
                    .or_default()
                    .insert(*value, tuple);
            }
            Term::Shape(owner, Skeleton::Result { callsite, .. }) => {
                bindings
                    .results
                    .insert((owner.clone(), *callsite), vec![Term::Settled(tuple)]);
            }
            Term::Evidence(owner, slot) => {
                bindings
                    .evidence
                    .insert((owner.clone(), *slot), ActivationInput::new(tuple));
            }
            Term::Return(owner) => {
                bindings.externals.insert(owner.clone(), tuple);
            }
            _ => unreachable!("the cases above are named source leaves"),
        }
        assert_eq!(
            solve(&members, &bindings, &mut types, &NullTelemetry, &frame).returns[&frame],
            int,
            "the same source equation projects its publisher's arriving tuple"
        );
    }
}

#[test]
fn empty_observations_are_distinct_from_missing_source_bindings() {
    let mut types = Types::new();
    let frame = SourceFrame(0);
    let outside = SourceFrame(1);
    let value = ValueId::from_u32(0);
    let callsite = CallSiteId::from_u32(0);
    let bindings = Bindings {
        value_types: HashMap::from([(frame.clone(), HashMap::from([(value, types.none())]))]),
        results: HashMap::from([((frame.clone(), callsite), Vec::new())]),
        evidence: HashMap::from([((outside.clone(), 0), ActivationInput::new(types.none()))]),
        externals: HashMap::from([(outside.clone(), types.none())]),
        ..Bindings::default()
    };
    let equations = Equations::new(&[(frame.clone(), 0)], &bindings);
    for source in [
        Term::Shape(frame.clone(), Skeleton::Ground(value)),
        Term::Shape(frame, Skeleton::Result { callsite, value }),
        Term::Evidence(outside.clone(), 0),
        Term::Return(outside),
    ] {
        assert!(
            !equations.is_unobserved(&source),
            "a publisher's empty answer is present; only absence is pending: {source:?}"
        );
    }
}
