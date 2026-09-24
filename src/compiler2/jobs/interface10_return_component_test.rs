//! Recovered solver contracts for evidence that ordinary source cannot create
//! reliably: an admitted equation, a missing producer, and strict projections.
//! These are kernel tests, not evidence of normal-path inference replacement.

use super::*;
use crate::compiler2::{FunctionId, RootId};
use crate::telemetry::sink::NullTelemetry;

fn member(types: &mut Types) -> ActivationKey {
    ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[], types)
}

fn answer(member: &ActivationKey, bindings: &Bindings, types: &mut Types) -> Option<Ty> {
    solve(
        std::slice::from_ref(member),
        &HashSet::from([member.clone()]),
        bindings,
        &[],
        types,
        &NullTelemetry,
        member,
    )
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
        (Term::Settled(none), Term::Unobserved),
        (Term::Unobserved, Term::Settled(none)),
        (Term::Settled(int), Term::Unobserved),
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
        [Term::Settled(none), Term::Unobserved, Term::Settled(int)].map(|sibling| {
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
    let observed = [Term::Settled(none), Term::Unobserved].map(|left_result| {
        bindings.results.insert((member.clone(), left), vec![left_result]);
        answer(&member, &bindings, &mut types)
    });
    assert_eq!(
        observed,
        [Some(live), None],
        "an impossible source tuple contributes no tag; an unknown alternative keeps the union pending"
    );
}
