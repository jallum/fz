use super::{DispatchDemand, demand_at_projection};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringExtraction, BitstringFieldKind, BitstringFieldShape, ProjectionKind,
};
use crate::ground_value::GroundValue;

/// The lattice records only the kind of structure a dispatch question can
/// descend into. A tuple field and a list head each name their kind; every
/// other projection reads a value the lattice cannot describe, so the demand
/// there is the whole value. What is asked beyond the step is not carried, and
/// neither is the detail the projection names: two different tuple fields ask
/// the same question of the tuple.
#[test]
fn a_demand_descends_through_tuple_fields_and_list_heads_and_stops_everywhere_else() {
    assert_eq!(
        demand_at_projection(&ProjectionKind::TupleField(0)),
        DispatchDemand::TupleFields
    );
    assert_eq!(
        demand_at_projection(&ProjectionKind::TupleField(3)),
        DispatchDemand::TupleFields
    );
    assert_eq!(
        demand_at_projection(&ProjectionKind::ListHead),
        DispatchDemand::ListShape
    );

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
    for collapsing in [
        ProjectionKind::StructField("name".to_string()),
        ProjectionKind::ListTail,
        ProjectionKind::MapValue {
            key: GroundValue::Atom("k".to_string()),
        },
        bitstring_field,
    ] {
        assert_eq!(demand_at_projection(&collapsing), DispatchDemand::Whole);
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
