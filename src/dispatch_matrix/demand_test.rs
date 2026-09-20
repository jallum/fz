use super::{DemandPathStep, DispatchDemand, demand_at_step};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringExtraction, BitstringFieldKind, BitstringFieldShape, ProjectionKind,
};
use crate::ground_value::GroundValue;

/// The lattice records only the kind of structure a dispatch question can
/// descend into. A tuple field and a list head each name their kind; every
/// other step is a value the lattice cannot describe, so the demand there is
/// the whole value. Which field, and what is asked beyond the step, are not
/// carried -- no reader of a demand tells one tuple field from another.
#[test]
fn a_demand_descends_through_tuple_fields_and_list_heads_and_stops_everywhere_else() {
    assert_eq!(
        demand_at_step(&DemandPathStep::TupleField(1)),
        DispatchDemand::TupleFields
    );
    assert_eq!(
        demand_at_step(&DemandPathStep::TupleField(0)),
        demand_at_step(&DemandPathStep::TupleField(1)),
        "the position within the tuple is not part of the demand"
    );
    assert_eq!(demand_at_step(&DemandPathStep::ListHead), DispatchDemand::ListShape);

    for collapsing in [
        DemandPathStep::StructField,
        DemandPathStep::ListTail,
        DemandPathStep::MapValue,
        DemandPathStep::BitstringField,
    ] {
        assert_eq!(demand_at_step(&collapsing), DispatchDemand::Whole);
    }
}

/// Joining two demands raises a slot to the least upper bound. Descending
/// through the same kind twice asks no more than descending once; descending
/// through two different kinds cannot be described by either, so it meets at
/// the whole value.
#[test]
fn a_join_of_two_descents_through_different_kinds_is_the_whole_value() {
    let mut same = DispatchDemand::TupleFields;
    same.join_assign(DispatchDemand::TupleFields);
    assert_eq!(same, DispatchDemand::TupleFields);

    let mut mixed = DispatchDemand::TupleFields;
    mixed.join_assign(DispatchDemand::ListShape);
    assert_eq!(mixed, DispatchDemand::Whole);

    let mut from_bottom = DispatchDemand::Ignore;
    from_bottom.join_assign(DispatchDemand::ListShape);
    assert_eq!(from_bottom, DispatchDemand::ListShape);

    let mut top = DispatchDemand::Whole;
    top.join_assign(DispatchDemand::TupleFields);
    assert_eq!(top, DispatchDemand::Whole);
}

/// A projection names the value it reads in full; the demand step keeps only
/// the kind of position it is, plus a tuple field's index. The names, keys and
/// bit layouts the other projections carry are not demand and fall away.
#[test]
fn a_projection_kind_names_its_demand_step() {
    let bitstring_field = ProjectionKind::BitstringField(BitstringExtraction {
        previous: None,
        spec: BitstringFieldShape {
            kind: BitstringFieldKind::Integer,
            size: None,
            endian: BitstringEndian::Big,
            signed: false,
            unit: None,
        },
        is_last: true,
    });
    let steps = [
        (ProjectionKind::TupleField(3), DemandPathStep::TupleField(3)),
        (
            ProjectionKind::StructField("name".to_string()),
            DemandPathStep::StructField,
        ),
        (ProjectionKind::ListHead, DemandPathStep::ListHead),
        (ProjectionKind::ListTail, DemandPathStep::ListTail),
        (
            ProjectionKind::MapValue {
                key: GroundValue::Atom("k".to_string()),
            },
            DemandPathStep::MapValue,
        ),
        (bitstring_field, DemandPathStep::BitstringField),
    ];
    for (kind, step) in &steps {
        assert_eq!(DemandPathStep::from(kind), *step);
    }
}
