use super::schema::{Schema, SchemaIdentity, SchemaRegistry};

#[test]
fn a_new_registry_holds_no_schema() {
    let registry = SchemaRegistry::new();

    assert_eq!(registry.len(), 0);
}

#[test]
fn schemas_take_ids_in_registration_order() {
    let mut registry = SchemaRegistry::new();

    assert_eq!(registry.register(Schema::tuple_of_arity(3)), 0);
    assert_eq!(registry.register(Schema::tuple_of_arity(1)), 1);
    assert_eq!(registry.get(0).identity, SchemaIdentity::Tuple(3));
    assert_eq!(registry.get(1).identity, SchemaIdentity::Tuple(1));
}

#[test]
fn registering_one_identity_twice_answers_the_same_id() {
    let mut registry = SchemaRegistry::new();

    let first = registry.register(Schema::tuple_of_arity(2));

    assert_eq!(registry.register(Schema::tuple_of_arity(2)), first);
    assert_eq!(registry.len(), 1);
}
