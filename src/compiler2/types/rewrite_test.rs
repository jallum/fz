use super::{
    ClosureLit, ClosureTarget, Descr, FiniteSet, MapKey, RuntimeEnvelopePolarity, RuntimeEnvelopePurpose, Sigma, Ty,
    TypeVarId, Types, bound_variables_reading, callable_identity_clauses, has_vars, map_recursive_inputs,
    map_recursive_inputs_with, runtime_arrow_sig, runtime_list_sig, runtime_map_sig, runtime_resource_sig,
    runtime_structural_conj, runtime_tuple_sig,
};
use std::collections::BTreeSet;

/// Types over every axis, with closures that capture nothing, scalars, other
/// closures and structures holding closures, type variables at the top and
/// nested, and negatives, so each rewrite meets the types it changes and the
/// types it leaves alone many times.
fn pool(t: &mut Types) -> Vec<Ty> {
    let (any, none, int, float) = (t.any(), t.none(), t.int(), t.float());
    let atom = t.atom();
    let a = t.atom_lit("a");
    let (v0, v1) = (t.type_var(TypeVarId(0)), t.type_var(TypeVarId(1)));
    let v0_or_int = t.union(v0, int);
    let ints = t.list(int);
    let of_vars = t.list(v0);
    let pair = t.tuple(&[int, float]);
    let var_pair = t.tuple(&[v0, a]);
    let nested_pair = t.tuple(&[var_pair, v1]);
    let plain = t.closure_lit(ClosureTarget(66), vec![], 0);
    let over_int = t.closure_lit(ClosureTarget(67), vec![int], 1);
    let over_pair = t.closure_lit(ClosureTarget(68), vec![pair, ints], 1);
    let over_closure = t.closure_lit(ClosureTarget(69), vec![over_int, plain], 2);
    let over_var = t.closure_lit(ClosureTarget(70), vec![v0], 1);
    let fn_ref = t.fn_ref_lit(ClosureTarget(71), 1);
    let arrow = t.arrow(&[int], int);
    let var_arrow = t.arrow(&[v0], v1);
    let held = t.tuple(&[over_int, a]);
    let listed = t.list(over_closure);
    let resource = t.resource(over_pair);
    let var_resource = t.resource(v0);
    let key = MapKey::Atom("k".to_string());
    let mapped = t.map(&[(key.clone(), over_int)]);
    let var_mapped = t.map(&[(key, v1)]);
    let meters = t.mint_brand(int, "Meters");
    let either = t.union(over_int, pair);
    let rest = t.difference(either, over_int);
    let tuple_top = t.tuple_top();
    let not_pair = t.difference(tuple_top, pair);
    let wide = t.difference(any, over_var);
    let held_arrow = t.tuple(&[arrow, var_arrow]);
    vec![
        any,
        none,
        int,
        atom,
        v0,
        v0_or_int,
        ints,
        of_vars,
        pair,
        var_pair,
        nested_pair,
        plain,
        over_int,
        over_pair,
        over_closure,
        over_var,
        fn_ref,
        arrow,
        var_arrow,
        held,
        listed,
        resource,
        var_resource,
        mapped,
        var_mapped,
        meters,
        either,
        rest,
        not_pair,
        wide,
        held_arrow,
    ]
}

fn sigmas(t: &mut Types) -> Vec<Sigma<Ty>> {
    let (int, none) = (t.int(), t.none());
    let ints = t.list(int);
    let float = t.float();
    vec![
        Sigma::default(),
        Sigma::from_iter([(TypeVarId(0), int)]),
        Sigma::from_iter([(TypeVarId(0), none)]),
        Sigma::from_iter([(TypeVarId(0), ints), (TypeVarId(1), float)]),
        Sigma::from_iter([(TypeVarId(99), int)]),
    ]
}

/// Erasing closure identity as it was when every type was copied out of the
/// interner before it was rewritten.
fn erase_by_copying(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).clone();
    let mut erased = map_recursive_inputs(t, base, erase_by_copying);
    for conj in &mut erased.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            let Some(lit) = sig.lit.take() else {
                continue;
            };
            if lit.captures.is_empty() {
                continue;
            }
            let captures = lit
                .captures
                .iter()
                .map(|capture| {
                    let capture = erase_by_copying(t, *capture);
                    t.intern(capture)
                })
                .collect();
            sig.lit = Some(ClosureLit {
                kind: lit.kind,
                fn_id: None,
                captures,
            });
        }
    }
    erased
}

/// Instantiation as it was when the union with the substituted descriptors was
/// taken even where nothing was substituted.
fn instantiate_by_copying(t: &mut Types, a: Ty, sigma: &Sigma<Ty>) -> Descr {
    let mut base = t.descr(&a).clone();
    if !has_vars(t.ctx(), &base, false) {
        return base;
    }
    let mut substituted = Descr::none();
    if !base.vars.cofinite {
        let mut new_set = BTreeSet::new();
        for id in &base.vars.values {
            match sigma.get(id) {
                Some(replacement) => {
                    substituted = substituted.union(t.ctx(), t.descr(replacement));
                }
                None => {
                    new_set.insert(*id);
                }
            }
        }
        base.vars = FiniteSet::finite(new_set);
    }
    let walked = map_recursive_inputs_with(t, base, &mut |t, nested| t.instantiate(&nested, sigma));
    walked.union(t.ctx(), &substituted)
}

/// The runtime envelope as it was when every type was copied out of the
/// interner and rebuilt, whatever it held.
fn envelope_by_copying(
    types: &mut Types,
    ty: Ty,
    polarity: RuntimeEnvelopePolarity,
    purpose: RuntimeEnvelopePurpose,
    bounds: &Sigma<Ty>,
) -> Ty {
    if purpose == RuntimeEnvelopePurpose::ClauseDomain && !types.has_vars(&ty) {
        return ty;
    }
    let mut descr = types.descr(&ty).clone();
    if !descr.vars.values.is_empty() {
        match (polarity, descr.vars.cofinite) {
            (RuntimeEnvelopePolarity::Positive, _) => match bound_variables_reading(types, &descr, purpose, bounds) {
                Some(bound) => {
                    descr.vars = FiniteSet::none();
                    let cx = types.ctx();
                    descr = descr.union(cx, &bound);
                }
                None => return types.intern(Descr::any()),
            },
            (RuntimeEnvelopePolarity::Negative, true) => return types.intern(Descr::none()),
            (RuntimeEnvelopePolarity::Negative, false) => descr.vars = FiniteSet::none(),
        }
    }
    if purpose == RuntimeEnvelopePurpose::Predicate
        && polarity == RuntimeEnvelopePolarity::Positive
        && !descr.funcs.is_empty()
    {
        descr.funcs = callable_identity_clauses(types, &descr.funcs);
    }
    if purpose == RuntimeEnvelopePurpose::ClauseDomain {
        descr.funcs = descr
            .funcs
            .into_iter()
            .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, bounds, runtime_arrow_sig))
            .collect();
    }
    descr.tuples = descr
        .tuples
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, bounds, runtime_tuple_sig))
        .collect();
    descr.lists = descr
        .lists
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, bounds, runtime_list_sig))
        .collect();
    descr.resources = descr
        .resources
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, bounds, runtime_resource_sig))
        .collect();
    descr.maps = descr
        .maps
        .into_iter()
        .filter_map(|conj| runtime_structural_conj(types, conj, polarity, purpose, bounds, runtime_map_sig))
        .collect();
    types.intern(descr)
}

/// Both answers must occur many times for a comparison to say anything.
fn both_occur(what: &str, changed: usize, unchanged: usize) {
    assert!(
        changed > 10 && unchanged > 10,
        "{what}: the inputs must exercise both answers: {changed} changed, {unchanged} unchanged"
    );
}

#[test]
fn erasing_closure_identity_answers_as_when_every_type_is_copied() {
    let mut t = Types::new();
    let _ = pool(&mut t);
    let (mut changed, mut unchanged) = (0, 0);
    for ty in t.interned_tys() {
        let descr = erase_by_copying(&mut t, ty);
        let expected = t.intern(descr);
        assert_eq!(t.erase_closure_identity(&ty), expected, "type {}", ty.as_u32());
        if expected == ty {
            unchanged += 1;
        } else {
            changed += 1;
        }
    }
    both_occur("erase_closure_identity", changed, unchanged);
}

#[test]
fn instantiating_answers_as_when_every_type_is_copied() {
    let mut t = Types::new();
    let _ = pool(&mut t);
    let sigmas = sigmas(&mut t);
    let (mut changed, mut unchanged) = (0, 0);
    for ty in t.interned_tys() {
        for sigma in &sigmas {
            let expected = if sigma.is_empty() || !t.has_vars(&ty) {
                ty
            } else {
                let descr = instantiate_by_copying(&mut t, ty, sigma);
                t.intern(descr)
            };
            assert_eq!(t.instantiate(&ty, sigma), expected, "type {}", ty.as_u32());
            if expected == ty {
                unchanged += 1;
            } else {
                changed += 1;
            }
        }
    }
    both_occur("instantiate", changed, unchanged);
}

#[test]
fn the_runtime_envelope_answers_as_when_every_type_is_copied() {
    let mut t = Types::new();
    let _ = pool(&mut t);
    let int = t.int();
    let bounds = Sigma::from_iter([(TypeVarId(0), int)]);
    let (mut changed, mut unchanged) = (0, 0);
    for ty in t.interned_tys() {
        for polarity in [RuntimeEnvelopePolarity::Positive, RuntimeEnvelopePolarity::Negative] {
            for purpose in [
                RuntimeEnvelopePurpose::Projection,
                RuntimeEnvelopePurpose::Predicate,
                RuntimeEnvelopePurpose::ClauseDomain,
            ] {
                let expected = envelope_by_copying(&mut t, ty, polarity, purpose, &bounds);
                let actual = super::runtime_envelope(&mut t, ty, polarity, purpose, &bounds);
                assert_eq!(actual, expected, "type {} at {purpose:?}", ty.as_u32());
                if expected == ty {
                    unchanged += 1;
                } else {
                    changed += 1;
                }
            }
        }
    }
    both_occur("runtime_envelope", changed, unchanged);
}
