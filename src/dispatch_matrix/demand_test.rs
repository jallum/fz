use super::{DemandPathStep, DispatchDemand, demand_at_path};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringExtraction, BitstringFieldKind, BitstringFieldShape, ProjectionKind,
};
use crate::ground_value::GroundValue;
use std::collections::BTreeMap;

/// The lattice records only the structure a dispatch question can descend
/// into. A tuple field and a list head keep their position; every other step
/// is a value the lattice cannot describe, so the demand there is the whole
/// value and the rest of the path stops mattering.
#[test]
fn a_demand_descends_through_tuple_fields_and_list_heads_and_stops_everywhere_else() {
    let mut second_field = BTreeMap::new();
    second_field.insert(1, DispatchDemand::Whole);
    assert_eq!(
        demand_at_path(&[DemandPathStep::TupleField(1)], DispatchDemand::Whole),
        DispatchDemand::TupleFields(second_field)
    );
    assert_eq!(
        demand_at_path(&[DemandPathStep::ListHead], DispatchDemand::Whole),
        DispatchDemand::ListShape(Box::new(DispatchDemand::Whole))
    );

    for collapsing in [
        DemandPathStep::StructField,
        DemandPathStep::ListTail,
        DemandPathStep::MapValue,
        DemandPathStep::BitstringField,
    ] {
        assert_eq!(
            demand_at_path(&[collapsing, DemandPathStep::TupleField(0)], DispatchDemand::Whole),
            DispatchDemand::Whole
        );
    }
}

/// A projection names the value it reads in full; the demand step keeps only
/// what the lattice can carry, which is the tuple position. The names, keys and
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
