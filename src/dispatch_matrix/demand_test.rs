use super::{DemandPathStep, DispatchDemand, demand_at_path, demand_within_path, demand_within_step};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringExtraction, BitstringFieldKind, BitstringFieldShape, ProjectionKind,
};
use crate::ground_value::GroundValue;
use std::collections::BTreeMap;

/// The lattice records only the structure a dispatch question can descend
/// into. A tuple field and a list head keep their position; a list tail or
/// bitstring field is a value the lattice cannot describe, so the demand there is the whole
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

    for collapsing in [DemandPathStep::ListTail, DemandPathStep::BitstringField] {
        assert_eq!(
            demand_at_path(&[collapsing, DemandPathStep::TupleField(0)], DispatchDemand::Whole),
            DispatchDemand::Whole
        );
    }
}

/// A map value or struct field is one of many values under a key the lattice
/// does not name: what is asked of its structure is asked of every value.
#[test]
fn a_question_about_the_structure_of_a_map_value_is_one_about_every_value() {
    let fields = DispatchDemand::TupleFields(BTreeMap::from([(0, DispatchDemand::Whole)]));
    let values = DispatchDemand::MapValues(Box::new(fields.clone()));
    for step in [DemandPathStep::MapValue, DemandPathStep::StructField] {
        assert_eq!(
            demand_at_path(&[step, DemandPathStep::TupleField(0)], DispatchDemand::Whole),
            values
        );
        assert_eq!(demand_within_step(&values, &step), fields);
        assert_eq!(demand_at_path(&[step], DispatchDemand::Whole), DispatchDemand::Whole);
        assert_eq!(demand_at_path(&[step], DispatchDemand::Class), DispatchDemand::Class);
    }
    let mut joined = values.clone();
    joined.join_assign(DispatchDemand::MapValues(Box::new(DispatchDemand::Class)));
    assert_eq!(joined, values);
    joined.join_assign(DispatchDemand::Whole);
    assert_eq!(joined, DispatchDemand::Whole);
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

/// `Class` sits between `Ignore` and every structural demand: it is raised by
/// anything that asks more and never lowers what is already asked.
#[test]
fn class_is_above_ignore_and_below_every_demand_that_names_structure() {
    let fields = DispatchDemand::TupleFields(BTreeMap::from([(0, DispatchDemand::Whole)]));
    let shape = DispatchDemand::ListShape(Box::new(DispatchDemand::Ignore));
    let join = |mut left: DispatchDemand, right: DispatchDemand| {
        left.join_assign(right);
        left
    };
    let ignore = || DispatchDemand::Ignore;
    let class = || DispatchDemand::Class;
    let whole = || DispatchDemand::Whole;

    assert_eq!(join(ignore(), class()), class());
    assert_eq!(join(class(), ignore()), class());
    assert_eq!(join(class(), class()), class());
    assert_eq!(join(class(), whole()), whole());
    assert_eq!(join(whole(), class()), whole());
    assert_eq!(join(class(), fields.clone()), fields);
    assert_eq!(join(fields.clone(), class()), fields);
    assert_eq!(join(class(), shape.clone()), shape);
    assert_eq!(join(shape.clone(), class()), shape);
    assert!(class().asks_anything(), "a literal-blind read is still a read");
}

/// Nothing asked, or nothing asked that tells literals apart, holds of a value
/// however deep the position sits; a question about structure the lattice
/// cannot name is a question about the whole value.
#[test]
fn a_literal_blind_read_survives_every_step_into_the_value() {
    for step in [
        DemandPathStep::StructField,
        DemandPathStep::ListTail,
        DemandPathStep::MapValue,
        DemandPathStep::BitstringField,
        DemandPathStep::TupleField(2),
        DemandPathStep::ListHead,
    ] {
        assert_eq!(demand_within_step(&DispatchDemand::Class, &step), DispatchDemand::Class);
        assert_eq!(
            demand_within_step(&DispatchDemand::Ignore, &step),
            DispatchDemand::Ignore
        );
    }
    for step in [
        DemandPathStep::StructField,
        DemandPathStep::MapValue,
        DemandPathStep::BitstringField,
    ] {
        assert_eq!(demand_at_path(&[step], DispatchDemand::Class), DispatchDemand::Class);
        assert_eq!(demand_at_path(&[step], DispatchDemand::Whole), DispatchDemand::Whole);
    }
}

/// A list's tail is a list of the same shape: what the recursion asks of its
/// elements it asks of the tail's.
#[test]
fn a_question_about_the_elements_of_a_tail_is_one_about_the_elements_of_the_list() {
    let shape = DispatchDemand::ListShape(Box::new(DispatchDemand::Whole));
    assert_eq!(demand_at_path(&[DemandPathStep::ListTail], shape.clone()), shape);
    assert_eq!(demand_within_step(&shape, &DemandPathStep::ListTail), shape);
    assert_eq!(
        demand_within_step(&shape, &DemandPathStep::ListHead),
        DispatchDemand::Whole
    );
}

/// Taking a demand inside a step undoes lifting it through that step.
#[test]
fn a_demand_taken_inside_a_path_is_the_one_lifted_through_it() {
    let path = [DemandPathStep::TupleField(1), DemandPathStep::ListHead];
    let lifted = demand_at_path(&path, DispatchDemand::Class);
    assert_eq!(demand_within_path(&lifted, &path), DispatchDemand::Class);
    assert_eq!(
        demand_within_path(&lifted, &[DemandPathStep::TupleField(0)]),
        DispatchDemand::Ignore,
        "a field the question does not name is not asked about"
    );
    assert_eq!(lifted.depth(), 2);
}
