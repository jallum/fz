//! `ReturnExpression::to_ty` must lower every constructor to exactly the
//! `Ty` the `Types` calculator would build directly for the same shape, and
//! an unmapped `Local` must refuse to guess.

use super::*;
use crate::compiler2::identity::{FunctionId, RootId};

fn test_activation_key(types: &mut Types, raw: u32) -> ActivationKey {
    let root = RootId::for_test(raw);
    let function = FunctionId::from_coordinate(raw);
    ActivationKey::from_inputs(root, function, &[], types)
}

#[test]
fn published_lowers_to_the_ty_it_carries() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let expression = ReturnExpression::Published(int);
    assert_eq!(Some(int), expression.to_ty(&mut types, &HashMap::new()));
}

#[test]
fn bottom_lowers_to_no_evidence() {
    let mut types = Types::new();
    let expression = ReturnExpression::Bottom;
    assert_eq!(None, expression.to_ty(&mut types, &HashMap::new()));
}

#[test]
fn union_with_bottom_is_the_other_member() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let expression = ReturnExpression::Union(vec![ReturnExpression::Bottom, ReturnExpression::Published(int)]);
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &int), "Bottom is the join identity");
}

#[test]
fn union_is_equivalent_regardless_of_member_order() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let atom = types.atom_lit("ok");
    let forward = ReturnExpression::Union(vec![
        ReturnExpression::Published(int),
        ReturnExpression::Published(atom),
    ]);
    let backward = ReturnExpression::Union(vec![
        ReturnExpression::Published(atom),
        ReturnExpression::Published(int),
    ]);
    let forward_ty = forward.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    let backward_ty = backward.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(
        types.is_equivalent(&forward_ty, &backward_ty),
        "a union does not depend on the order its members were observed in"
    );
}

#[test]
fn union_dedups_a_member_observed_twice() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let expression = ReturnExpression::Union(vec![ReturnExpression::Published(int), ReturnExpression::Published(int)]);
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(
        types.is_equivalent(&lowered, &int),
        "the same type observed twice is still just that type"
    );
}

#[test]
fn tuple_lowers_to_the_same_ty_the_calculator_builds_directly() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let atom = types.atom_lit("ok");
    let expected = types.tuple(&[int, atom]);
    let expression = ReturnExpression::Tuple(vec![
        ReturnExpression::Published(int),
        ReturnExpression::Published(atom),
    ]);
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &expected));
}

#[test]
fn list_lowers_to_the_same_ty_the_calculator_builds_directly() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let expected = types.list(int);
    let expression = ReturnExpression::List(Box::new(ReturnExpression::Published(int)));
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &expected));
}

#[test]
fn non_empty_list_lowers_to_the_same_ty_the_calculator_builds_directly() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let expected = types.non_empty_list(int);
    let expression = ReturnExpression::NonEmptyList(Box::new(ReturnExpression::Published(int)));
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &expected));
}

#[test]
fn map_lowers_to_the_same_ty_the_calculator_builds_directly() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let key = MapKey::Atom("count".to_string());
    let expected = types.map(&[(key.clone(), int)]);
    let expression = ReturnExpression::Map(vec![(key, ReturnExpression::Published(int))]);
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &expected));
}

#[test]
fn struct_lowers_to_the_same_ty_the_calculator_builds_directly() {
    let mut types = Types::new();
    let int = types.int_lit(1);
    let key = MapKey::Atom("count".to_string());
    let module = ModuleId::GLOBAL;
    let name = ModuleName::from_segments(vec!["Example".to_string()]);
    let expected = types.struct_map(module, name.clone(), &[(key.clone(), int)]);
    let expression = ReturnExpression::Struct(module, name, vec![(key, ReturnExpression::Published(int))]);
    let lowered = expression.to_ty(&mut types, &HashMap::new()).expect("some evidence");
    assert!(types.is_equivalent(&lowered, &expected));
}

#[test]
fn local_resolves_through_the_member_map() {
    let mut types = Types::new();
    let key = test_activation_key(&mut types, 0);
    let int = types.int_lit(1);
    let mut member_map = HashMap::new();
    member_map.insert(key.clone(), int);
    let expression = ReturnExpression::Local(key);
    assert_eq!(Some(int), expression.to_ty(&mut types, &member_map));
}

#[test]
#[should_panic(expected = "has no member_map entry")]
fn an_unmapped_local_panics_instead_of_guessing() {
    let mut types = Types::new();
    let key = test_activation_key(&mut types, 0);
    let expression = ReturnExpression::Local(key);
    let _ = expression.to_ty(&mut types, &HashMap::new());
}
