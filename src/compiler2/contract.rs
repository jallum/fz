//! Compiler2's callee-owned function contract facts.
//!
//! A contract is the resolved type surface declared by source. Direct-call
//! resolution applies it to observed arguments before minting callee
//! activations or deriving callable-boundary demand.

use std::collections::{HashMap, HashSet};

use crate::type_expr::ResolvedSpecDecl;

use super::identity::FunctionId;
use super::types::{Sigma, Ty, TypeVarId, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractArrow {
    pub params: Vec<Ty>,
    pub result: Ty,
    pub constraints: HashMap<TypeVarId, Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionContract {
    pub arrows: Vec<ContractArrow>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedContractArrow {
    pub params: Vec<Ty>,
    pub result: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedFunctionContract {
    pub matched_arrows: Vec<AppliedContractArrow>,
    pub result: Option<Ty>,
}

#[derive(Debug, Default)]
pub struct FunctionContractMap {
    slots: Vec<Option<FunctionContract>>,
}

impl FunctionContract {
    pub fn from_resolved(arrows: Vec<ResolvedSpecDecl<Ty>>) -> Self {
        Self {
            arrows: arrows
                .into_iter()
                .map(|arrow| ContractArrow {
                    params: arrow.params,
                    result: arrow.result,
                    constraints: arrow.constraints,
                })
                .collect(),
        }
    }

    pub fn apply(&self, types: &mut Types, arg_tys: &[Ty]) -> AppliedFunctionContract {
        let mut matched_arrows = Vec::new();
        let mut result = None;
        for arrow in &self.arrows {
            let Some(matched) = instantiate_matching_arrow(types, arrow, arg_tys) else {
                continue;
            };
            match matched {
                SchemeInstantiation::Known(arrow) => {
                    result = Some(match result {
                        Some(current) => types.union(current, arrow.result),
                        None => arrow.result,
                    });
                    matched_arrows.push(arrow);
                }
                SchemeInstantiation::Underconstrained(arrow) => {
                    matched_arrows.push(arrow);
                }
                SchemeInstantiation::Invalid => {}
            }
        }
        AppliedFunctionContract { matched_arrows, result }
    }
}

impl FunctionContractMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, function: FunctionId, contract: FunctionContract) -> bool {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        let changed = slot.as_ref() != Some(&contract);
        *slot = Some(contract);
        changed
    }

    pub fn get(&self, function: FunctionId) -> Option<&FunctionContract> {
        self.slots.get(function.as_u32() as usize)?.as_ref()
    }

    fn ensure(&mut self, function: FunctionId) {
        let index = function.as_u32() as usize;
        if self.slots.len() <= index {
            self.slots.resize_with(index + 1, || None);
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SchemeInstantiation<T> {
    Known(T),
    Underconstrained(T),
    Invalid,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SchemeMatch<T> {
    params: Vec<T>,
    result: T,
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

fn instantiate_matching_arrow(
    types: &mut Types,
    arrow: &ContractArrow,
    arg_tys: &[Ty],
) -> Option<SchemeInstantiation<AppliedContractArrow>> {
    let witnesses = overlapping_witnesses(types, &arrow.params, arg_tys)?;
    match instantiate_match(types, &arrow.params, &arrow.result, &arrow.constraints, &witnesses) {
        SchemeInstantiation::Known(matched) => Some(SchemeInstantiation::Known(AppliedContractArrow {
            params: matched.params,
            result: matched.result,
        })),
        SchemeInstantiation::Underconstrained(matched) => {
            Some(SchemeInstantiation::Underconstrained(AppliedContractArrow {
                params: matched.params,
                result: matched.result,
            }))
        }
        SchemeInstantiation::Invalid => None,
    }
}

fn overlapping_witnesses(types: &mut Types, params: &[Ty], args: &[Ty]) -> Option<Vec<Ty>> {
    if params.len() != args.len() {
        return None;
    }
    let mut witnesses = Vec::with_capacity(params.len());
    for (param, arg) in params.iter().zip(args.iter().copied()) {
        let witness = contract_witness(types, *param, arg);
        if types.is_empty(&witness) {
            return None;
        }
        witnesses.push(witness);
    }
    Some(witnesses)
}

fn contract_witness(types: &mut Types, pattern: Ty, witness: Ty) -> Ty {
    let mut sigma = Sigma::new();
    collect_contract_subst(types, &pattern, &witness, &mut sigma);
    if sigma.is_empty() {
        return witness;
    }
    types.instantiate(&pattern, &sigma)
}

fn instantiate_match(
    types: &mut Types,
    params: &[Ty],
    result: &Ty,
    constraints: &HashMap<TypeVarId, Ty>,
    witnesses: &[Ty],
) -> SchemeInstantiation<SchemeMatch<Ty>> {
    if params.len() != witnesses.len() {
        return SchemeInstantiation::Invalid;
    }

    let mut sigma: Sigma<Ty> = Sigma::new();
    let mut ambiguous_vars = HashSet::new();
    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        if collect_contract_subst(types, pattern, witness, &mut sigma) == Witness::Invalid {
            return SchemeInstantiation::Invalid;
        }
        collect_ambiguous_empty_list_vars(types, pattern, witness, &mut ambiguous_vars);
    }

    for (var, bound) in constraints {
        let Some(actual) = sigma.get(var) else {
            return SchemeInstantiation::Underconstrained(instantiated_match(
                types,
                params,
                result,
                &surface_sigma(&sigma, &ambiguous_vars),
            ));
        };
        if !types.is_subtype(actual, bound) {
            return SchemeInstantiation::Invalid;
        }
    }

    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        let expected = types.instantiate(pattern, &sigma);
        if !types.has_vars(witness) && !types.is_subtype(witness, &expected) {
            return SchemeInstantiation::Invalid;
        }
    }

    let matched = instantiated_match(types, params, result, &surface_sigma(&sigma, &ambiguous_vars));
    if matched.params.iter().any(|param| types.has_vars(param)) || types.has_vars(&matched.result) {
        SchemeInstantiation::Underconstrained(matched)
    } else {
        SchemeInstantiation::Known(matched)
    }
}

fn instantiated_match(types: &mut Types, params: &[Ty], result: &Ty, sigma: &Sigma<Ty>) -> SchemeMatch<Ty> {
    SchemeMatch {
        params: params.iter().map(|param| types.instantiate(param, sigma)).collect(),
        result: types.instantiate(result, sigma),
    }
}

fn surface_sigma(sigma: &Sigma<Ty>, ambiguous_vars: &HashSet<TypeVarId>) -> Sigma<Ty> {
    sigma
        .iter()
        .filter(|(var, _)| !ambiguous_vars.contains(var))
        .map(|(var, ty)| (*var, *ty))
        .collect()
}

fn collect_contract_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    Witness::Unknown
        .merge(collect_var_subst(types, pattern, witness, sigma))
        .merge(collect_tuple_subst(types, pattern, witness, sigma))
        .merge(collect_list_subst(types, pattern, witness, sigma))
        .merge(collect_resource_subst(types, pattern, witness, sigma))
        .merge(collect_map_subst(types, pattern, witness, sigma))
        .merge(collect_arrow_subst(types, pattern, witness, sigma))
}

fn collect_var_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    if !types.has_vars(pattern) || types.has_vars(witness) {
        return Witness::Unknown;
    }
    let mut direct = Sigma::new();
    types.collect_instantiation_subst(pattern, witness, &mut direct);
    if direct.is_empty() {
        return Witness::Unknown;
    }
    merge_sigma(types, sigma, direct);
    Witness::Known
}

fn collect_tuple_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    let arity = types.max_tuple_arity(pattern);
    if arity == 0 {
        return Witness::Unknown;
    }
    let pattern_fields = types.tuple_projections(pattern, arity);
    if !pattern_fields.iter().any(|field| types.has_vars(field)) {
        return Witness::Unknown;
    }
    if types.max_tuple_arity(witness) < arity {
        return if types.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    }
    let witness_fields = types.tuple_projections(witness, arity);
    let mut outcome = Witness::Unknown;
    for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
        outcome = outcome.merge(collect_contract_subst(types, pattern_field, witness_field, sigma));
    }
    outcome
}

fn collect_list_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    if !types.has_list_shape(pattern) {
        return Witness::Unknown;
    }
    let pattern_elem = types.list_element_type(pattern);
    if !types.has_vars(&pattern_elem) {
        return Witness::Unknown;
    }
    if !types.has_list_shape(witness) {
        return if types.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    }
    let witness_elem = types.list_element_type(witness);
    collect_contract_subst(types, &pattern_elem, &witness_elem, sigma)
}

fn is_exact_empty_list(types: &mut Types, witness: &Ty) -> bool {
    if !types.has_list_shape(witness) {
        return false;
    }
    let empty = types.empty_list();
    types.is_equivalent(witness, &empty)
}

fn collect_ambiguous_empty_list_vars(
    types: &mut Types,
    pattern: &Ty,
    witness: &Ty,
    ambiguous_vars: &mut HashSet<TypeVarId>,
) {
    if is_exact_empty_list(types, witness) {
        let mut direct = Sigma::new();
        types.collect_instantiation_subst(pattern, witness, &mut direct);
        ambiguous_vars.extend(direct.into_keys());
        return;
    }

    let arity = types.max_tuple_arity(pattern);
    if arity != 0 && types.max_tuple_arity(witness) >= arity {
        let pattern_fields = types.tuple_projections(pattern, arity);
        let witness_fields = types.tuple_projections(witness, arity);
        for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
            collect_ambiguous_empty_list_vars(types, pattern_field, witness_field, ambiguous_vars);
        }
    }

    if types.has_list_shape(pattern) && types.has_list_shape(witness) {
        let pattern_elem = types.list_element_type(pattern);
        let witness_elem = types.list_element_type(witness);
        collect_ambiguous_empty_list_vars(types, &pattern_elem, &witness_elem, ambiguous_vars);
    }

    if let (Some(pattern_payload), Some(witness_payload)) = (
        types.resource_payload_type(pattern),
        types.resource_payload_type(witness),
    ) {
        collect_ambiguous_empty_list_vars(types, &pattern_payload, &witness_payload, ambiguous_vars);
    }

    let witness_keys = types.map_known_keys(witness);
    for key in types.map_known_keys(pattern) {
        let Some(pattern_field) = types.map_field_lookup(pattern, &key) else {
            continue;
        };
        if !witness_keys.contains(&key) {
            continue;
        }
        if let Some(witness_field) = types.map_field_lookup(witness, &key) {
            collect_ambiguous_empty_list_vars(types, &pattern_field, &witness_field, ambiguous_vars);
        }
    }

    let Some(pattern_clauses) = types.callable_clauses(pattern) else {
        return;
    };
    let Some(witness_clauses) = types.callable_clauses(witness) else {
        return;
    };
    for pattern_clause in &pattern_clauses {
        for witness_clause in &witness_clauses {
            if pattern_clause.args.len() != witness_clause.args.len() {
                continue;
            }
            for (pattern_arg, witness_arg) in pattern_clause.args.iter().zip(witness_clause.args.iter()) {
                collect_ambiguous_empty_list_vars(types, pattern_arg, witness_arg, ambiguous_vars);
            }
            collect_ambiguous_empty_list_vars(types, &pattern_clause.ret, &witness_clause.ret, ambiguous_vars);
        }
    }
}

fn collect_resource_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    let Some(pattern_payload) = types.resource_payload_type(pattern) else {
        return Witness::Unknown;
    };
    if !types.has_vars(&pattern_payload) {
        return Witness::Unknown;
    }
    let Some(witness_payload) = types.resource_payload_type(witness) else {
        return if types.has_vars(witness) {
            Witness::Unknown
        } else {
            Witness::Invalid
        };
    };
    collect_contract_subst(types, &pattern_payload, &witness_payload, sigma)
}

fn collect_map_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    let witness_keys = types.map_known_keys(witness);
    let mut outcome = Witness::Unknown;
    for key in types.map_known_keys(pattern) {
        let Some(pattern_field) = types.map_field_lookup(pattern, &key) else {
            continue;
        };
        if !types.has_vars(&pattern_field) {
            continue;
        }
        if !witness_keys.contains(&key) {
            if types.map_field_lookup(witness, &key).is_none() && !types.has_vars(witness) {
                outcome = outcome.merge(Witness::Invalid);
            }
            continue;
        }
        if let Some(witness_field) = types.map_field_lookup(witness, &key) {
            outcome = outcome.merge(collect_contract_subst(types, &pattern_field, &witness_field, sigma));
        }
    }
    outcome
}

fn collect_arrow_subst(types: &mut Types, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> Witness {
    let Some(pattern_clauses) = types.callable_clauses(pattern) else {
        return Witness::Unknown;
    };
    if !pattern_clauses
        .iter()
        .any(|clause| clause.args.iter().any(|arg| types.has_vars(arg)) || types.has_vars(&clause.ret))
    {
        return Witness::Unknown;
    }
    let Some(witness_clauses) = types.callable_clauses(witness) else {
        return if types.has_vars(witness) {
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
            for (pattern_arg, witness_arg) in pattern_clause.args.iter().zip(witness_clause.args.iter()) {
                outcome = outcome.merge(collect_contract_subst(types, pattern_arg, witness_arg, sigma));
            }
            outcome = outcome.merge(collect_contract_subst(
                types,
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

fn merge_sigma(types: &mut Types, sigma: &mut Sigma<Ty>, direct: Sigma<Ty>) {
    for (var, witness) in direct {
        match sigma.remove(&var) {
            Some(existing) => {
                let joined = types.union(existing, witness);
                sigma.insert(var, joined);
            }
            None => {
                sigma.insert(var, witness);
            }
        }
    }
}
