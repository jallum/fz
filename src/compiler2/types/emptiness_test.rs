use super::{list_clause_empty, list_denotation};
use crate::compiler2::types::Types;
use crate::compiler2::types::conj::Conj;
use crate::compiler2::types::sigs::ListSig;

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

fn list_sigs(t: &mut Types) -> Vec<ListSig> {
    let int = t.int();
    let float = t.float();
    let number = t.union(int, float);
    let any = t.any();
    let ints = t.list(int);
    let anys = t.list(any);
    let elems = [
        None,
        Some(int),
        Some(float),
        Some(number),
        Some(any),
        Some(ints),
        Some(anys),
    ];
    elems
        .into_iter()
        .flat_map(|elem| [true, false].map(|empty| ListSig { empty, elem }))
        .collect()
}

/// Every choice of at most two signatures from the pool, in a fixed order.
fn at_most_two(sigs: &[ListSig]) -> Vec<Vec<ListSig>> {
    let mut choices = vec![Vec::new()];
    for (i, a) in sigs.iter().enumerate() {
        choices.push(vec![a.clone()]);
        for b in &sigs[i + 1..] {
            choices.push(vec![a.clone(), b.clone()]);
        }
    }
    choices
}

/// A list clause denotes nothing exactly when its denotation is absent, so the
/// emptiness decision and the denotation can never disagree.
#[test]
fn a_list_clause_is_empty_exactly_when_it_has_no_denotation() {
    let mut t = Types::new();
    let sigs = list_sigs(&mut t);
    let choices = at_most_two(&sigs);
    let cx = t.ctx();

    let (mut empty, mut inhabited) = (0usize, 0usize);
    for pos in &choices {
        for neg in &choices {
            let clause = Conj {
                pos: pos.clone(),
                neg: neg.clone(),
            };
            let decided = list_clause_empty(cx, &clause);
            assert_eq!(
                decided,
                list_denotation(cx, &clause).is_none(),
                "emptiness and denotation disagree on {clause:?}"
            );
            if decided {
                empty += 1;
            } else {
                inhabited += 1;
            }
        }
    }
    assert!(
        empty > 1000 && inhabited > 1000,
        "the clause set must exercise both answers: {empty} empty, {inhabited} inhabited"
    );
}
