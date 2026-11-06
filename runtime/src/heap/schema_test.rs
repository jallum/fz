use super::schema::{BITSTRING_READER_SCHEMA, BITSTRING_RESULT_SCHEMA, Schema, SchemaIdentity, SchemaRegistry};

#[test]
fn a_new_registry_starts_with_the_bitstring_readers_tuples_at_fixed_ids() {
    let registry = SchemaRegistry::new();

    assert_eq!(registry.len(), 2);
    assert_eq!(registry.get(BITSTRING_RESULT_SCHEMA).identity, SchemaIdentity::Tuple(1));
    assert_eq!(registry.get(BITSTRING_READER_SCHEMA).identity, SchemaIdentity::Tuple(3));
}

#[test]
fn a_users_one_and_three_tuples_share_the_bitstring_readers_ids() {
    let mut registry = SchemaRegistry::new();

    assert_eq!(registry.register(Schema::tuple_of_arity(1)), BITSTRING_RESULT_SCHEMA);
    assert_eq!(registry.register(Schema::tuple_of_arity(3)), BITSTRING_READER_SCHEMA);
    assert_eq!(registry.len(), 2);
}

#[test]
fn a_users_first_other_schema_follows_the_bitstring_readers_tuples() {
    let mut registry = SchemaRegistry::new();

    assert_eq!(registry.register(Schema::tuple_of_arity(2)), 2);
}
