use crate::compiler2::types::Types;

/// Deciding emptiness carries no path of descriptors under decision, which is
/// sound only while every descriptor names descriptors interned before it.
#[test]
fn a_descriptor_names_only_types_interned_before_it() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom_lit("a");
    let list = t.list(int);
    let pair = t.tuple(&[int, list]);
    let nested = t.tuple(&[pair, list]);
    let resource = t.resource(nested);
    let arrow = t.arrow(&[nested, atom], resource);
    let either = t.union(pair, atom);
    let meet = t.intersect(either, pair);
    let rest = t.difference(nested, pair);
    let spread = t.union(arrow, rest);
    let _ = (meet, spread);

    for ty in t.interned_tys() {
        let reachable = t.activation_reachable(ty, |_| {});
        assert!(
            reachable.iter().all(|named| named.as_u32() <= ty.as_u32()),
            "type {} names a type interned after it, so deciding its emptiness would not descend",
            ty.as_u32()
        );
    }
}
