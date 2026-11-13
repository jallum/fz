use super::{Descr, Ty, TyCtx, Types, list_element_type, resource_payload_type, tuple_field_type, tuple_projections};

/// The projections as they were written when every coordinate was cloned out of
/// its interned descriptor before it was folded.
mod by_copying {
    use super::*;

    pub fn list_element_type(cx: TyCtx<'_>, d: &Descr) -> Descr {
        if d.lists.is_empty() {
            return Descr::any();
        }
        let mut elem = Descr::none();
        for conj in &d.lists {
            if conj.pos.iter().any(|sig| sig.elem.is_none()) {
                continue;
            }
            let mut clause_elem: Option<Descr> = None;
            for sig in &conj.pos {
                let sig_elem = cx.descr(&sig.elem.unwrap());
                clause_elem = Some(match clause_elem {
                    None => sig_elem.clone(),
                    Some(prev) => prev.intersect(sig_elem),
                });
            }
            elem = elem.union(cx, &clause_elem.unwrap_or_else(Descr::any));
        }
        elem
    }

    pub fn resource_payload_type(cx: TyCtx<'_>, d: &Descr) -> Option<Descr> {
        if d.resources.is_empty() {
            return None;
        }
        let mut acc = Descr::none();
        for conj in &d.resources {
            if !conj.neg.is_empty() || conj.pos.is_empty() {
                return Some(Descr::any());
            }
            let mut payload: Option<Descr> = None;
            for sig in &conj.pos {
                let sig_payload = cx.descr(&sig.payload);
                payload = Some(match payload {
                    Some(prev) => prev.intersect(sig_payload),
                    None => sig_payload.clone(),
                });
            }
            acc = acc.union(cx, &payload.unwrap_or_else(Descr::any));
        }
        Some(acc)
    }

    pub fn tuple_projections(cx: TyCtx<'_>, d: &Descr, arity: usize) -> Vec<Descr> {
        let mut comps = vec![Descr::none(); arity];
        let mut found = false;
        for conj in &d.tuples {
            let mut clause_comps: Option<Vec<Descr>> = None;
            for sig in &conj.pos {
                if sig.elems.len() != arity {
                    continue;
                }
                clause_comps = Some(match clause_comps {
                    None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                    Some(prev) => prev
                        .iter()
                        .zip(sig.elems.iter())
                        .map(|(p, s)| p.intersect(cx.descr(s)))
                        .collect(),
                });
            }
            if let Some(cs) = clause_comps {
                for i in 0..arity {
                    comps[i] = comps[i].union(cx, &cs[i]);
                }
                found = true;
            }
        }
        if found { comps } else { vec![Descr::any(); arity] }
    }

    pub fn tuple_field_type(cx: TyCtx<'_>, d: &Descr, index: usize) -> Descr {
        let mut out = Descr::none();
        let mut found = false;
        for conj in &d.tuples {
            if conj.pos.is_empty() {
                return Descr::any();
            }
            let mut arity = None;
            let mut clause_fields: Option<Vec<Descr>> = None;
            let mut feasible = true;
            for sig in &conj.pos {
                if index >= sig.elems.len() || arity.is_some_and(|arity| arity != sig.elems.len()) {
                    feasible = false;
                    break;
                }
                arity = Some(sig.elems.len());
                clause_fields = Some(match clause_fields {
                    None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                    Some(prev) => prev
                        .iter()
                        .zip(sig.elems.iter())
                        .map(|(p, s)| p.intersect(cx.descr(s)))
                        .collect(),
                });
            }
            let Some(fields) = clause_fields else {
                continue;
            };
            if !feasible || fields.iter().any(|field| field.is_empty(cx)) {
                continue;
            }
            out = out.union(cx, &fields[index]);
            found = true;
        }
        if found { out } else { Descr::none() }
    }
}

/// Descriptors whose list, resource and tuple axes hold one clause with one
/// positive, one clause with several positives (a structural meet), several
/// clauses (a join), negatives (a difference) and the unconstrained clause
/// (`any` and its complements).
fn pool(t: &mut Types) -> Vec<Descr> {
    let (any, none, int, float) = (t.any(), t.none(), t.int(), t.float());
    let number = t.union(int, float);
    let atom = t.atom();
    let a = t.atom_lit("a");
    let ints = t.list(int);
    let floats = t.list(float);
    let anys = t.list(any);
    let some_ints = t.non_empty_list(int);
    let no_list = t.empty_list();
    let unit = t.tuple(&[]);
    let one = t.tuple(&[int]);
    let pair = t.tuple(&[int, float]);
    let wide = t.tuple(&[number, atom]);
    let tagged = t.tuple(&[a, int]);
    let triple = t.tuple(&[int, atom, number]);
    let none_pair = t.tuple(&[int, none]);
    let tuple_top = t.tuple_top();
    let res_int = t.resource(int);
    let res_float = t.resource(float);
    let res_any = t.resource(any);
    let res_number = t.resource(number);
    let res_atom = t.resource(atom);
    let res_pair = t.resource(pair);
    let res_ints = t.resource(ints);
    let rest = t.difference(tuple_top, pair);
    let listy = t.union(ints, pair);
    let base: Vec<Ty> = vec![
        any, none, int, number, atom, ints, floats, anys, some_ints, no_list, unit, one, pair, wide, tagged, triple,
        none_pair, tuple_top, res_int, res_float, res_any, res_number, res_atom, res_pair, res_ints, rest, listy,
    ];
    let cx = t.ctx();
    let bases: Vec<Descr> = base.iter().map(|ty| cx.descr(ty).clone()).collect();
    let mut pool = bases.clone();
    for (i, d) in bases.iter().enumerate() {
        pool.push(Descr::any().diff(d));
        for other in &bases[i..] {
            pool.push(d.intersect(other));
            pool.push(d.union(cx, other));
            pool.push(d.diff(other));
        }
        pool.push(
            d.intersect(&bases[(i + 1) % bases.len()])
                .intersect(&bases[(i + 2) % bases.len()]),
        );
        pool.push(
            d.intersect(&bases[(i + 3) % bases.len()])
                .union(cx, &bases[(i + 5) % bases.len()]),
        );
    }
    pool
}

/// Reading a coordinate where it lives changes no answer: every projection
/// returns the descriptor the copying algorithm returned, on inputs that make
/// the borrowed single positive, the owned meet, the several-clause join, the
/// negatives and the unconstrained clause each occur many times.
#[test]
fn a_projection_reads_the_descriptors_it_unions_in_place_and_answers_as_before() {
    let mut t = Types::new();
    let pool = pool(&mut t);
    let cx = t.ctx();

    let (mut metlists, mut metresources, mut mettuples, mut singles) = (0usize, 0usize, 0usize, 0usize);
    let (mut no_axis, mut unconstrained) = (0usize, 0usize);
    for d in &pool {
        let list = by_copying::list_element_type(cx, d);
        assert_eq!(
            list_element_type(cx, d).unwrap_or_else(Descr::any),
            list,
            "list element of {d:?}"
        );
        let resource = by_copying::resource_payload_type(cx, d);
        assert_eq!(resource_payload_type(cx, d), resource, "resource payload of {d:?}");
        for arity in 0..4 {
            assert_eq!(
                tuple_projections(cx, d, arity),
                by_copying::tuple_projections(cx, d, arity),
                "tuple projections of {d:?} at arity {arity}"
            );
        }
        for index in 0..4 {
            assert_eq!(
                tuple_field_type(cx, d, index),
                by_copying::tuple_field_type(cx, d, index),
                "tuple field {index} of {d:?}"
            );
        }
        metlists += d.lists.iter().filter(|c| c.pos.len() > 1).count();
        metresources += d.resources.iter().filter(|c| c.pos.len() > 1).count();
        mettuples += d.tuples.iter().filter(|c| c.pos.len() > 1).count();
        singles +=
            d.lists.iter().filter(|c| c.pos.len() == 1).count() + d.tuples.iter().filter(|c| c.pos.len() == 1).count();
        no_axis += usize::from(d.lists.is_empty()) + usize::from(d.resources.is_empty());
        unconstrained += d.lists.iter().filter(|c| c.pos.is_empty()).count()
            + d.resources
                .iter()
                .filter(|c| c.pos.is_empty() || !c.neg.is_empty())
                .count();
    }
    for (what, count) in [
        ("list meets", metlists),
        ("resource meets", metresources),
        ("tuple meets", mettuples),
        ("single positives", singles),
        ("descriptors without the axis", no_axis),
        ("unconstrained clauses", unconstrained),
    ] {
        assert!(count > 10, "the pool must exercise {what}: {count}");
    }
}

/// The `Types` entry points answer the interned form of the same descriptors,
/// including the unconstrained answers they return without building `any`.
#[test]
fn the_projection_entry_points_intern_what_the_copying_algorithm_built() {
    let mut t = Types::new();
    let pool = pool(&mut t);
    let tys: Vec<Ty> = pool.iter().map(|d| t.intern(d.clone())).collect();
    for ty in tys {
        let cx = t.ctx();
        let d = cx.descr(&ty).clone();
        let elem = by_copying::list_element_type(cx, &d);
        let payload = by_copying::resource_payload_type(cx, &d);
        let fields: Vec<Descr> = (0..4).map(|i| by_copying::tuple_field_type(cx, &d, i)).collect();
        let elem = t.intern(elem);
        assert_eq!(t.list_element_type(&ty), elem);
        let payload = payload.map(|p| t.intern(p));
        assert_eq!(t.resource_payload_type(&ty), payload);
        for (index, field) in fields.into_iter().enumerate() {
            let field = t.intern(field);
            assert_eq!(t.tuple_field_type(&ty, index), field);
        }
    }
}
