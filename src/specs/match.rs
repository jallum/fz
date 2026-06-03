use crate::types::{ClosureLitInfo, ClosureTarget, ClosureTypes, Sigma, TypeVarId, Types};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SchemeInstantiation<T> {
    Known(T),
    Underconstrained(T),
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SchemeMatch<T> {
    pub params: Vec<T>,
    pub result: T,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Witness {
    Known,
    Unknown,
    Invalid,
}

impl Witness {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Invalid, _) | (_, Self::Invalid) => Self::Invalid,
            (Self::Known, _) | (_, Self::Known) => Self::Known,
            (Self::Unknown, Self::Unknown) => Self::Unknown,
        }
    }
}

fn instantiate_result<T: ClosureTypes + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
    witnesses: &[T::Ty],
) -> SchemeInstantiation<T::Ty> {
    match instantiate_match(t, params, result, constraints, witnesses) {
        SchemeInstantiation::Known(matched) => SchemeInstantiation::Known(matched.result),
        SchemeInstantiation::Underconstrained(matched) => SchemeInstantiation::Underconstrained(matched.result),
        SchemeInstantiation::Invalid => SchemeInstantiation::Invalid,
    }
}

pub(crate) fn instantiate_match<T: ClosureTypes + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
    witnesses: &[T::Ty],
) -> SchemeInstantiation<SchemeMatch<T::Ty>> {
    let witness_slots: Vec<Option<&T::Ty>> = witnesses.iter().map(Some).collect();
    instantiate_match_slots(t, params, result, constraints, &witness_slots)
}

pub(super) fn instantiate_match_with_slots<T: ClosureTypes + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
    witnesses: &[Option<T::Ty>],
) -> SchemeInstantiation<SchemeMatch<T::Ty>> {
    let witness_slots: Vec<Option<&T::Ty>> = witnesses.iter().map(Option::as_ref).collect();
    instantiate_match_slots(t, params, result, constraints, &witness_slots)
}

pub(crate) fn resolve_closure_return<T: ClosureTypes + ?Sized>(
    t: &mut T,
    closure_ty: &T::Ty,
    effective_returns: &HashMap<(ClosureTarget, Vec<T::Ty>), T::Ty>,
    arg_tys: &[T::Ty],
) -> Option<T::Ty> {
    let Some(clauses) = t.callable_clauses(closure_ty) else {
        return Some(t.any());
    };
    let mut acc = t.none();
    for clause in clauses {
        match clause.closure {
            None => {
                let contrib = if t.has_vars(&clause.ret) || clause.args.iter().any(|arg| t.has_vars(arg)) {
                    let constraints = HashMap::new();
                    match instantiate_result(t, &clause.args, &clause.ret, &constraints, arg_tys) {
                        SchemeInstantiation::Known(ty) | SchemeInstantiation::Underconstrained(ty) => ty,
                        SchemeInstantiation::Invalid => return Some(t.any()),
                    }
                } else {
                    clause.ret
                };
                acc = t.union(acc, contrib);
            }
            Some(ClosureLitInfo { target, captures, .. }) => {
                if clause.args.len() != arg_tys.len() {
                    return Some(t.any());
                }
                let mut full_key = captures.clone();
                full_key.extend_from_slice(arg_tys);
                match effective_returns.get(&(target, full_key)) {
                    Some(r) => acc = t.union(acc, r.clone()),
                    None => return None,
                }
            }
        }
    }
    Some(acc)
}

fn instantiate_match_slots<T: ClosureTypes + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
    witnesses: &[Option<&T::Ty>],
) -> SchemeInstantiation<SchemeMatch<T::Ty>> {
    if params.len() != witnesses.len() {
        return SchemeInstantiation::Invalid;
    }

    let mut sigma: Sigma<T::Ty> = Sigma::new();
    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        let Some(witness) = witness else {
            continue;
        };
        if collect_structural_subst(t, pattern, witness, &mut sigma) == Witness::Invalid {
            return SchemeInstantiation::Invalid;
        }
    }

    for (var, bound) in constraints {
        let Some(actual) = sigma.get(var) else {
            return SchemeInstantiation::Underconstrained(instantiated_match(t, params, result, &sigma));
        };
        if !t.is_subtype(actual, bound) {
            return SchemeInstantiation::Invalid;
        }
    }

    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        let Some(witness) = witness else {
            continue;
        };
        let expected = t.instantiate(pattern, &sigma);
        if !t.has_vars(witness) && !t.is_subtype(witness, &expected) {
            return SchemeInstantiation::Invalid;
        }
    }

    let matched = instantiated_match(t, params, result, &sigma);
    if t.has_vars(&matched.result) {
        SchemeInstantiation::Underconstrained(matched)
    } else {
        SchemeInstantiation::Known(matched)
    }
}

fn instantiated_match<T: Types + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    sigma: &Sigma<T::Ty>,
) -> SchemeMatch<T::Ty> {
    let params = params
        .iter()
        .map(|param| t.instantiate(param, sigma))
        .collect::<Vec<_>>();
    let result = t.instantiate(result, sigma);
    SchemeMatch { params, result }
}

fn collect_structural_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    Witness::Unknown
        .merge(collect_direct_subst(t, pattern, witness, sigma))
        .merge(collect_tuple_subst(t, pattern, witness, sigma))
        .merge(collect_list_subst(t, pattern, witness, sigma))
        .merge(collect_resource_subst(t, pattern, witness, sigma))
        .merge(collect_map_subst(t, pattern, witness, sigma))
        .merge(collect_arrow_subst(t, pattern, witness, sigma))
}

fn collect_direct_subst<T: Types + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    let mut direct = Sigma::new();
    t.collect_instantiation_subst(pattern, witness, &mut direct);
    if direct.is_empty() {
        return Witness::Unknown;
    }
    merge_sigma(t, sigma, direct);
    Witness::Known
}

fn collect_tuple_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    let arity = t.max_tuple_arity(pattern);
    if arity == 0 {
        return Witness::Unknown;
    }
    let pattern_fields = t.tuple_projections(pattern, arity);
    if !pattern_fields.iter().any(|field| t.has_vars(field)) {
        return Witness::Unknown;
    }
    if t.max_tuple_arity(witness) < arity {
        return if t.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    }
    let witness_fields = t.tuple_projections(witness, arity);
    let mut outcome = Witness::Unknown;
    for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
        outcome = outcome.merge(collect_structural_subst(t, pattern_field, witness_field, sigma));
    }
    outcome
}

fn collect_list_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    if !t.has_list_shape(pattern) {
        return Witness::Unknown;
    }
    let pattern_elem = t.list_element_type(pattern);
    if !t.has_vars(&pattern_elem) {
        return Witness::Unknown;
    }
    if !t.has_list_shape(witness) {
        return if t.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    }
    let witness_elem = t.list_element_type(witness);
    collect_structural_subst(t, &pattern_elem, &witness_elem, sigma)
}

fn collect_resource_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    let Some(pattern_payload) = t.resource_payload_type(pattern) else {
        return Witness::Unknown;
    };
    if !t.has_vars(&pattern_payload) {
        return Witness::Unknown;
    }
    let Some(witness_payload) = t.resource_payload_type(witness) else {
        return if t.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    };
    collect_structural_subst(t, &pattern_payload, &witness_payload, sigma)
}

fn collect_map_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    let witness_keys = t.map_known_keys(witness);
    let mut outcome = Witness::Unknown;
    for key in t.map_known_keys(pattern) {
        let Some(pattern_field) = t.map_field_lookup(pattern, &key) else {
            continue;
        };
        if !t.has_vars(&pattern_field) {
            continue;
        }
        if !witness_keys.contains(&key) {
            if t.map_field_lookup(witness, &key).is_none() && !t.has_vars(witness) {
                outcome = outcome.merge(Witness::Invalid);
            }
            continue;
        }
        if let Some(witness_field) = t.map_field_lookup(witness, &key) {
            outcome = outcome.merge(collect_structural_subst(t, &pattern_field, &witness_field, sigma));
        }
    }
    outcome
}

fn collect_arrow_subst<T: ClosureTypes + ?Sized>(
    t: &mut T,
    pattern: &T::Ty,
    witness: &T::Ty,
    sigma: &mut Sigma<T::Ty>,
) -> Witness {
    let Some(pattern_clauses) = t.callable_clauses(pattern) else {
        return Witness::Unknown;
    };
    if !pattern_clauses.iter().any(|clause| t.has_vars(&clause.ret)) {
        return Witness::Unknown;
    }
    let Some(witness_clauses) = t.callable_clauses(witness) else {
        return if t.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    };

    let mut saw_compatible_arity = false;
    let mut outcome = Witness::Unknown;
    for pattern_clause in &pattern_clauses {
        for witness_clause in &witness_clauses {
            if pattern_clause.args.len() != witness_clause.args.len() {
                continue;
            }
            saw_compatible_arity = true;
            outcome = outcome.merge(collect_structural_subst(
                t,
                &pattern_clause.ret,
                &witness_clause.ret,
                sigma,
            ));
        }
    }
    if saw_compatible_arity {
        outcome
    } else {
        Witness::Invalid
    }
}

fn merge_sigma<T: Types + ?Sized>(t: &mut T, sigma: &mut Sigma<T::Ty>, direct: Sigma<T::Ty>) {
    for (var, witness) in direct {
        match sigma.remove(&var) {
            Some(existing) => {
                let joined = t.union(existing, witness);
                sigma.insert(var, joined);
            }
            None => {
                sigma.insert(var, witness);
            }
        }
    }
}
