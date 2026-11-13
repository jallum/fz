use super::{list_clause_empty, list_denotation, phi_tuple};
use crate::compiler2::types::conj::Conj;
use crate::compiler2::types::descr::Descr;
use crate::compiler2::types::sigs::ListSig;
use crate::compiler2::types::{Ty, Types};

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

/// Descriptors over every axis, in the shapes the kernel meets: finite and
/// cofinite scalars, brands, tuples of several arities, lists, maps, resources
/// and arrows, and the raw unions, complements and differences that leave
/// negative literals in a clause.
fn descriptor_pool(t: &mut Types) -> Vec<Descr> {
    let any = t.any();
    let none = t.none();
    let int = t.int();
    let float = t.float();
    let number = t.union(int, float);
    let binary = t.str_t();
    let atom = t.atom();
    let a = t.atom_lit("a");
    let b = t.atom_lit("b");
    let a_or_b = t.union(a, b);
    let nil = t.nil();
    let boolean = t.bool();
    let pid = t.builtin_opaque(crate::compiler2::types::BuiltinOpaque::Pid);
    let meters = t.mint_brand(int, "Meters");
    let feet = t.mint_brand(int, "Feet");
    let ints = t.list(int);
    let anys = t.list(any);
    let some_ints = t.non_empty_list(int);
    let no_list = t.empty_list();
    let unit = t.tuple(&[]);
    let one = t.tuple(&[int]);
    let pair = t.tuple(&[int, int]);
    let mixed = t.tuple(&[int, float]);
    let tagged = t.tuple(&[a, int]);
    let wide = t.tuple(&[any, any]);
    let nested = t.tuple(&[one, int]);
    let choice = t.tuple(&[number, a_or_b]);
    let triple = t.tuple(&[int, atom, number]);
    let tuple_top = t.tuple_top();
    let key = crate::ground_value::MapKey::Atom("k".to_string());
    let map_int = t.map(&[(key.clone(), int)]);
    let map_float = t.map(&[(key, float)]);
    let map_top = t.map_top();
    let res_int = t.resource(int);
    let res_any = t.resource(any);
    let to_int = t.arrow(&[int], int);
    let to_any = t.arrow(&[any], int);
    let binary_fn = t.arrow(&[int, int], int);
    let rest = t.difference(tuple_top, pair);
    let tagged_rest = t.difference(choice, tagged);
    let listy = t.union(ints, pair);

    let base: Vec<Ty> = vec![
        none,
        any,
        int,
        float,
        number,
        binary,
        atom,
        a,
        a_or_b,
        nil,
        boolean,
        pid,
        meters,
        feet,
        ints,
        anys,
        some_ints,
        no_list,
        unit,
        one,
        pair,
        mixed,
        tagged,
        wide,
        nested,
        choice,
        triple,
        tuple_top,
        map_int,
        map_float,
        map_top,
        res_int,
        res_any,
        to_int,
        to_any,
        binary_fn,
        rest,
        tagged_rest,
        listy,
    ];
    let cx = t.ctx();
    let bases: Vec<Descr> = base.iter().map(|ty| cx.descr(ty).clone()).collect();
    let mut pool = bases.clone();
    for (i, d) in bases.iter().enumerate() {
        pool.push(Descr::any().diff(d));
        pool.push(d.union(cx, &bases[(i + 1) % bases.len()]));
        pool.push(d.diff(&bases[(i + 3) % bases.len()]));
        pool.push(d.intersect(&Descr::any().diff(&bases[(i + 5) % bases.len()])));
    }
    pool
}

/// Disjointness is the emptiness of the meet, asked without building the meet,
/// on every pair of descriptors the pool offers.
#[test]
fn two_descriptors_are_disjoint_exactly_when_their_meet_is_empty() {
    let mut t = Types::new();
    let pool = descriptor_pool(&mut t);
    let cx = t.ctx();

    let (mut disjoint, mut overlapping) = (0usize, 0usize);
    for (i, a) in pool.iter().enumerate() {
        for (j, b) in pool.iter().enumerate() {
            let decided = a.is_disjoint(cx, b);
            assert_eq!(
                decided,
                a.intersect(b).is_empty(cx),
                "disjointness and the meet's emptiness disagree on pool entries {i} and {j}: {a:?} and {b:?}"
            );
            if decided {
                disjoint += 1;
            } else {
                overlapping += 1;
            }
        }
    }
    assert!(
        disjoint > 2000 && overlapping > 2000,
        "the pool must exercise both answers: {disjoint} disjoint, {overlapping} overlapping"
    );
}

/// The product-minus-union question as it was first answered: every split and
/// every disjointness probe builds its descriptors.
fn phi_tuple_by_building(cx: crate::compiler2::types::TyCtx<'_>, t: &[Descr], n: &[Vec<&Descr>]) -> bool {
    if t.iter().any(|d| d.is_empty(cx)) {
        return true;
    }
    let Some((head, rest)) = n.split_first() else {
        return false;
    };
    if head.iter().zip(t).any(|(h, ti)| ti.intersect(h).is_empty(cx)) {
        return phi_tuple_by_building(cx, t, rest);
    }
    (0..t.len()).all(|i| {
        let mut split = t.to_vec();
        for j in 0..i {
            split[j] = split[j].intersect(head[j]);
        }
        split[i] = split[i].diff(head[i]);
        phi_tuple_by_building(cx, &split, rest)
    })
}

fn every_row(coords: &[Descr], arity: usize) -> Vec<Vec<&Descr>> {
    (0..arity).fold(vec![Vec::new()], |rows, _| {
        rows.into_iter()
            .flat_map(|row| {
                coords.iter().map(move |c| {
                    let mut next = row.clone();
                    next.push(c);
                    next
                })
            })
            .collect()
    })
}

/// A product minus up to two products is empty exactly as the building
/// algorithm says, whichever coordinates are borrowed and whichever are met.
#[test]
fn a_product_minus_products_is_decided_as_when_every_step_builds_its_descriptors() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let number = t.union(int, float);
    let atom = t.atom();
    let a = t.atom_lit("a");
    let one = t.tuple(&[int]);
    let ints = t.list(int);
    let all = [int, float, number, atom, a, one, ints];
    let cx = t.ctx();
    let mut coords: Vec<Descr> = all.iter().map(|ty| cx.descr(ty).clone()).collect();
    coords.push(Descr::any().diff(&coords[0]));
    coords.push(Descr::none());

    let (mut empty, mut inhabited) = (0usize, 0usize);
    let mut check = |arity: usize, coords: &[Descr], max_negs: usize| {
        let rows = every_row(coords, arity);
        for product in &rows {
            let owned: Vec<Descr> = product.iter().map(|d| (*d).clone()).collect();
            let mut negations: Vec<Vec<&Vec<&Descr>>> = vec![Vec::new()];
            negations.extend(rows.iter().map(|r| vec![r]));
            if max_negs > 1 {
                negations.extend(rows.iter().flat_map(|r| rows.iter().map(move |s| vec![r, s])));
            }
            for negs in negations {
                let negs: Vec<Vec<&Descr>> = negs.into_iter().cloned().collect();
                let decided = phi_tuple(cx, product, &negs);
                assert_eq!(
                    decided,
                    phi_tuple_by_building(cx, &owned, &negs),
                    "phi_tuple disagrees on {product:?} minus {negs:?}"
                );
                if decided {
                    empty += 1;
                } else {
                    inhabited += 1;
                }
            }
        }
    };
    check(2, &coords, 2);
    check(3, &coords[..5], 1);
    assert!(
        empty > 1000 && inhabited > 1000,
        "the products must exercise both answers: {empty} empty, {inhabited} inhabited"
    );
}
