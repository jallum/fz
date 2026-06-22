//! Trichotomy arrow matching — the contract calculator.
//!
//! `match_arrow` decides whether a polymorphic signature (an arrow's parameter
//! patterns, result, and variable bounds) accepts an observed argument list,
//! and with what instantiation. It returns a three-way verdict:
//!
//!   * [`ArrowMatch::Known`] — every bound variable is grounded; the
//!     instantiated result is a runtime fact.
//!   * [`ArrowMatch::Underconstrained`] — the arguments fit, but some variable
//!     stayed free (a witness left an addressed leaf unbound); the instantiation
//!     is partial.
//!   * [`ArrowMatch::Invalid`] — a structural mismatch (arity, missing map key,
//!     incompatible arrow) or a bound violation rules the signature out.
//!
//! This is the authoritative calculator behind direct-call contract
//! application. It is the home — per "Types is the calculator" — of the
//! substitution/witness logic that previously lived hand-rolled in
//! `contract.rs`. Five behaviors the boolean subsumption surface
//! (`key_subsumes_with`) cannot express live here: the Known/Underconstrained/
//! Invalid trichotomy; union-on-rebind when one variable binds several
//! witnesses; structural-mismatch -> Invalid for arrow arity; the same for
//! map-key presence and tuple arity; and ambiguous empty-list variables.

use std::collections::{HashMap, HashSet};

use super::{Sigma, Ty, TypeVarId, Types};

/// The three-way verdict of matching a signature against an argument list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrowMatch {
    /// All bound variables grounded; `result` is a runtime fact.
    Known { params: Vec<Ty>, result: Ty },
    /// Arguments fit but some variable stayed free; the instantiation is partial.
    Underconstrained { params: Vec<Ty>, result: Ty },
    /// Structural mismatch or bound violation: the signature does not apply.
    Invalid,
}

/// Per-position witness outcome, merged across an argument list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MatchWitness {
    Known,
    Unknown,
    Invalid,
}

impl MatchWitness {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Invalid, _) | (_, Self::Invalid) => Self::Invalid,
            (Self::Known, _) | (_, Self::Known) => Self::Known,
            (Self::Unknown, Self::Unknown) => Self::Unknown,
        }
    }
}

impl Types {
    /// Match a signature `(params) -> result` with variable `bounds` against an
    /// observed argument list, returning the trichotomy verdict and the
    /// instantiated arrow.
    pub fn match_arrow(
        &mut self,
        params: &[Ty],
        result: &Ty,
        bounds: &HashMap<TypeVarId, Ty>,
        args: &[Ty],
    ) -> ArrowMatch {
        let Some(witnesses) = self.overlapping_witnesses(params, args) else {
            return ArrowMatch::Invalid;
        };
        self.instantiate_match(params, result, bounds, &witnesses)
    }

    /// Per-parameter overlap witnesses, or `None` when arity differs or any
    /// parameter is disjoint from its argument (an empty witness).
    fn overlapping_witnesses(&mut self, params: &[Ty], args: &[Ty]) -> Option<Vec<Ty>> {
        if params.len() != args.len() {
            return None;
        }
        let mut witnesses = Vec::with_capacity(params.len());
        for (param, arg) in params.iter().zip(args.iter().copied()) {
            let witness = self.match_witness(*param, arg);
            if self.is_empty(&witness) {
                return None;
            }
            witnesses.push(witness);
        }
        Some(witnesses)
    }

    /// The overlap of a parameter pattern with an argument: the pattern
    /// instantiated by whatever the argument pins, or the raw argument when the
    /// pattern is ground.
    fn match_witness(&mut self, pattern: Ty, witness: Ty) -> Ty {
        let mut sigma = Sigma::new();
        if self.collect_match_subst(&pattern, &witness, &mut sigma) == MatchWitness::Invalid {
            return self.none();
        }
        if sigma.is_empty() {
            return witness;
        }
        self.instantiate(&pattern, &sigma)
    }

    fn instantiate_match(
        &mut self,
        params: &[Ty],
        result: &Ty,
        bounds: &HashMap<TypeVarId, Ty>,
        witnesses: &[Ty],
    ) -> ArrowMatch {
        if params.len() != witnesses.len() {
            return ArrowMatch::Invalid;
        }

        let mut sigma: Sigma<Ty> = Sigma::new();
        let mut ambiguous_vars = HashSet::new();
        let mut ambiguous_seen = HashSet::new();
        for (pattern, witness) in params.iter().zip(witnesses.iter()) {
            if self.collect_match_subst(pattern, witness, &mut sigma) == MatchWitness::Invalid {
                return ArrowMatch::Invalid;
            }
            self.collect_ambiguous_empty_list_vars(pattern, witness, &mut ambiguous_vars, &mut ambiguous_seen);
        }

        for (var, bound) in bounds {
            let Some(actual) = sigma.get(var) else {
                let surface = surface_sigma(&sigma, &ambiguous_vars);
                let (params, result) = self.instantiated_match(params, result, &surface);
                return ArrowMatch::Underconstrained { params, result };
            };
            if !self.is_subtype(actual, bound) {
                return ArrowMatch::Invalid;
            }
        }

        for (pattern, witness) in params.iter().zip(witnesses.iter()) {
            let expected = self.instantiate(pattern, &sigma);
            if !self.has_vars(witness) && !self.has_vars(&expected) && !self.is_subtype(witness, &expected) {
                return ArrowMatch::Invalid;
            }
        }

        let surface = surface_sigma(&sigma, &ambiguous_vars);
        let (params, result) = self.instantiated_match(params, result, &surface);
        if params.iter().any(|param| self.has_vars(param)) || self.has_vars(&result) {
            ArrowMatch::Underconstrained { params, result }
        } else {
            ArrowMatch::Known { params, result }
        }
    }

    fn instantiated_match(&mut self, params: &[Ty], result: &Ty, sigma: &Sigma<Ty>) -> (Vec<Ty>, Ty) {
        let params = params.iter().map(|param| self.instantiate(param, sigma)).collect();
        let result = self.instantiate(result, sigma);
        (params, result)
    }

    fn collect_match_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        MatchWitness::Unknown
            .merge(self.collect_var_match(pattern, witness, sigma))
            .merge(self.collect_tuple_match(pattern, witness, sigma))
            .merge(self.collect_list_match(pattern, witness, sigma))
            .merge(self.collect_resource_match(pattern, witness, sigma))
            .merge(self.collect_map_match(pattern, witness, sigma))
            .merge(self.collect_arrow_match(pattern, witness, sigma))
    }

    fn collect_var_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        if !self.has_vars(pattern) || self.has_vars(witness) {
            return MatchWitness::Unknown;
        }
        let mut direct = Sigma::new();
        self.collect_instantiation_subst(pattern, witness, &mut direct);
        if direct.is_empty() {
            return MatchWitness::Unknown;
        }
        self.merge_subst_union(sigma, direct);
        MatchWitness::Known
    }

    fn collect_tuple_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        let arity = self.max_tuple_arity(pattern);
        if arity == 0 {
            return MatchWitness::Unknown;
        }
        if !self
            .tuple_projections(pattern, arity)
            .iter()
            .any(|field| self.has_vars(field))
        {
            return MatchWitness::Unknown;
        }
        if self.max_tuple_arity(witness) < arity {
            return if self.has_vars(witness) {
                MatchWitness::Unknown
            } else {
                MatchWitness::Invalid
            };
        }
        if let Some(outcome) = self.collect_correlated_tuple_match(pattern, witness, arity, sigma) {
            return outcome;
        }
        let pattern_fields = self.tuple_projections(pattern, arity);
        let witness_fields = self.tuple_projections(witness, arity);
        let mut outcome = MatchWitness::Unknown;
        for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
            outcome = outcome.merge(self.collect_match_subst(pattern_field, witness_field, sigma));
        }
        outcome
    }

    fn collect_correlated_tuple_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        arity: usize,
        sigma: &mut Sigma<Ty>,
    ) -> Option<MatchWitness> {
        let pattern_alternatives = self.tuple_positive_alternatives(pattern, arity)?;
        let witness_alternatives = self.tuple_positive_alternatives(witness, arity)?;
        let mut matched_any = false;
        let mut outcome = MatchWitness::Unknown;
        for pattern_fields in &pattern_alternatives {
            for witness_fields in &witness_alternatives {
                if !self.tuple_fields_overlap(pattern_fields, witness_fields) {
                    continue;
                }
                matched_any = true;
                let mut pair_sigma = Sigma::new();
                let mut pair_outcome = MatchWitness::Unknown;
                for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
                    pair_outcome =
                        pair_outcome.merge(self.collect_match_subst(pattern_field, witness_field, &mut pair_sigma));
                }
                if pair_outcome == MatchWitness::Invalid {
                    continue;
                }
                self.merge_subst_union(sigma, pair_sigma);
                outcome = outcome.merge(pair_outcome);
            }
        }
        if matched_any {
            Some(outcome)
        } else {
            Some(MatchWitness::Invalid)
        }
    }

    fn tuple_positive_alternatives(&mut self, ty: &Ty, arity: usize) -> Option<Vec<Vec<Ty>>> {
        let conjs = self.descr(ty).tuples.clone();
        if conjs.is_empty() {
            return None;
        }
        let mut alternatives = Vec::new();
        for conj in conjs {
            if !conj.neg.is_empty() || conj.pos.is_empty() {
                return None;
            }
            let mut fields: Option<Vec<Ty>> = None;
            for sig in conj.pos {
                if sig.elems.len() != arity {
                    continue;
                }
                fields = Some(match fields {
                    Some(current) => current
                        .iter()
                        .zip(sig.elems.iter())
                        .map(|(left, right)| self.intersect(*left, *right))
                        .collect(),
                    None => sig.elems,
                });
            }
            let Some(fields) = fields else {
                continue;
            };
            if fields.iter().all(|field| !self.is_empty(field)) {
                alternatives.push(fields);
            }
        }
        (!alternatives.is_empty()).then_some(alternatives)
    }

    fn tuple_fields_overlap(&mut self, pattern_fields: &[Ty], witness_fields: &[Ty]) -> bool {
        pattern_fields.len() == witness_fields.len()
            && pattern_fields
                .iter()
                .zip(witness_fields.iter())
                .all(|(pattern, witness)| {
                    if self.has_vars(pattern) || self.has_vars(witness) {
                        return true;
                    }
                    let overlap = self.intersect(*pattern, *witness);
                    !self.is_empty(&overlap)
                })
    }

    fn collect_list_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        if !self.has_list_shape(pattern) {
            return MatchWitness::Unknown;
        }
        let pattern_elem = self.list_element_type(pattern);
        if !self.has_vars(&pattern_elem) {
            return MatchWitness::Unknown;
        }
        if !self.has_list_shape(witness) {
            return if self.has_vars(witness) {
                MatchWitness::Unknown
            } else {
                MatchWitness::Invalid
            };
        }
        let witness_elem = self.list_element_type(witness);
        self.collect_match_subst(&pattern_elem, &witness_elem, sigma)
    }

    fn collect_resource_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        let Some(pattern_payload) = self.resource_payload_type(pattern) else {
            return MatchWitness::Unknown;
        };
        if !self.has_vars(&pattern_payload) {
            return MatchWitness::Unknown;
        }
        let Some(witness_payload) = self.resource_payload_type(witness) else {
            return if self.has_vars(witness) {
                MatchWitness::Unknown
            } else {
                MatchWitness::Invalid
            };
        };
        self.collect_match_subst(&pattern_payload, &witness_payload, sigma)
    }

    fn collect_map_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        let witness_keys = self.map_known_keys(witness);
        let mut outcome = MatchWitness::Unknown;
        for key in self.map_known_keys(pattern) {
            let Some(pattern_field) = self.map_field_lookup(pattern, &key) else {
                continue;
            };
            if !self.has_vars(&pattern_field) {
                continue;
            }
            if !witness_keys.contains(&key) {
                if !self.has_vars(witness) {
                    outcome = outcome.merge(MatchWitness::Invalid);
                }
                continue;
            }
            if let Some(witness_field) = self.map_field_lookup(witness, &key) {
                outcome = outcome.merge(self.collect_match_subst(&pattern_field, &witness_field, sigma));
            }
        }
        outcome
    }

    fn collect_arrow_match(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) -> MatchWitness {
        let Some(pattern_clauses) = self.callable_clauses(pattern) else {
            return MatchWitness::Unknown;
        };
        if !pattern_clauses
            .iter()
            .any(|clause| clause.args.iter().any(|arg| self.has_vars(arg)) || self.has_vars(&clause.ret))
        {
            return MatchWitness::Unknown;
        }
        let Some(witness_clauses) = self.callable_clauses(witness) else {
            return if self.has_vars(witness) {
                MatchWitness::Unknown
            } else {
                MatchWitness::Invalid
            };
        };

        let mut saw_compatible_arity = false;
        let mut outcome = MatchWitness::Unknown;
        for pattern_clause in &pattern_clauses {
            for witness_clause in &witness_clauses {
                if pattern_clause.args.len() != witness_clause.args.len() {
                    continue;
                }
                saw_compatible_arity = true;
                for (pattern_arg, witness_arg) in pattern_clause.args.iter().zip(witness_clause.args.iter()) {
                    outcome = outcome.merge(self.collect_match_subst(pattern_arg, witness_arg, sigma));
                }
                outcome = outcome.merge(self.collect_match_subst(&pattern_clause.ret, &witness_clause.ret, sigma));
            }
        }
        if saw_compatible_arity {
            outcome
        } else {
            MatchWitness::Invalid
        }
    }

    fn collect_ambiguous_empty_list_vars(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        ambiguous_vars: &mut HashSet<TypeVarId>,
        seen: &mut HashSet<(Ty, Ty)>,
    ) {
        if !self.has_vars(pattern) || !seen.insert((*pattern, *witness)) {
            return;
        }

        if self.is_exact_empty_list(witness) {
            let mut direct = Sigma::new();
            self.collect_instantiation_subst(pattern, witness, &mut direct);
            ambiguous_vars.extend(direct.into_keys());
            return;
        }

        let arity = self.max_tuple_arity(pattern);
        if arity != 0 && self.max_tuple_arity(witness) >= arity {
            let pattern_fields = self.tuple_projections(pattern, arity);
            let witness_fields = self.tuple_projections(witness, arity);
            for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
                self.collect_ambiguous_empty_list_vars(pattern_field, witness_field, ambiguous_vars, seen);
            }
        }

        if self.has_list_shape(pattern) && self.has_list_shape(witness) {
            let pattern_elem = self.list_element_type(pattern);
            let witness_elem = self.list_element_type(witness);
            self.collect_ambiguous_empty_list_vars(&pattern_elem, &witness_elem, ambiguous_vars, seen);
        }

        if let (Some(pattern_payload), Some(witness_payload)) =
            (self.resource_payload_type(pattern), self.resource_payload_type(witness))
        {
            self.collect_ambiguous_empty_list_vars(&pattern_payload, &witness_payload, ambiguous_vars, seen);
        }

        let witness_keys = self.map_known_keys(witness);
        for key in self.map_known_keys(pattern) {
            let Some(pattern_field) = self.map_field_lookup(pattern, &key) else {
                continue;
            };
            if !witness_keys.contains(&key) {
                continue;
            }
            if let Some(witness_field) = self.map_field_lookup(witness, &key) {
                self.collect_ambiguous_empty_list_vars(&pattern_field, &witness_field, ambiguous_vars, seen);
            }
        }

        let Some(pattern_clauses) = self.callable_clauses(pattern) else {
            return;
        };
        let Some(witness_clauses) = self.callable_clauses(witness) else {
            return;
        };
        for pattern_clause in &pattern_clauses {
            for witness_clause in &witness_clauses {
                if pattern_clause.args.len() != witness_clause.args.len() {
                    continue;
                }
                for (pattern_arg, witness_arg) in pattern_clause.args.iter().zip(witness_clause.args.iter()) {
                    self.collect_ambiguous_empty_list_vars(pattern_arg, witness_arg, ambiguous_vars, seen);
                }
                self.collect_ambiguous_empty_list_vars(&pattern_clause.ret, &witness_clause.ret, ambiguous_vars, seen);
            }
        }
    }

    fn is_exact_empty_list(&mut self, witness: &Ty) -> bool {
        if !self.has_list_shape(witness) {
            return false;
        }
        let empty = self.empty_list();
        self.is_equivalent(witness, &empty)
    }

    /// Union a directly-collected substitution into the running one: when a
    /// variable binds more than one witness across positions, its binding is
    /// the union of the witnesses (not the first one seen).
    fn merge_subst_union(&mut self, sigma: &mut Sigma<Ty>, direct: Sigma<Ty>) {
        for (var, witness) in direct {
            match sigma.remove(&var) {
                Some(existing) => {
                    let joined = self.union(existing, witness);
                    sigma.insert(var, joined);
                }
                None => {
                    sigma.insert(var, witness);
                }
            }
        }
    }
}

/// Drop ambiguous empty-list variables from a substitution before it surfaces
/// as an instantiation: a variable pinned only by `[]` could be any element
/// type, so leaving it free keeps the result honestly underconstrained.
fn surface_sigma(sigma: &Sigma<Ty>, ambiguous_vars: &HashSet<TypeVarId>) -> Sigma<Ty> {
    sigma
        .iter()
        .filter(|(var, _)| !ambiguous_vars.contains(var))
        .map(|(var, ty)| (*var, *ty))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::MapKey;
    use super::*;
    use std::collections::HashMap;

    fn no_bounds() -> HashMap<TypeVarId, Ty> {
        HashMap::new()
    }

    // Behavior 1: the Known / Underconstrained / Invalid trichotomy.
    #[test]
    fn grounded_argument_yields_known() {
        // (a) -> a applied to (int) grounds a = int.
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        match t.match_arrow(&[a], &a, &no_bounds(), &[int]) {
            ArrowMatch::Known { result, .. } => assert_eq!(result, int),
            other => panic!("expected Known, got {other:?}"),
        }
    }

    #[test]
    fn variable_argument_yields_underconstrained() {
        // (a) -> a applied to a still-free variable leaves the result free.
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let free = t.type_var(TypeVarId(999));
        match t.match_arrow(&[a], &a, &no_bounds(), &[free]) {
            ArrowMatch::Underconstrained { .. } => {}
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    #[test]
    fn arity_mismatch_yields_invalid() {
        // Behavior 3: structural mismatch -> Invalid (arrow arity).
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        assert_eq!(
            t.match_arrow(&[a], &a, &no_bounds(), &[int, str_t]),
            ArrowMatch::Invalid
        );
    }

    // Behavior 2: union-on-rebind when one variable binds several witnesses.
    #[test]
    fn repeated_variable_unions_its_witnesses() {
        // (a, a) -> a applied to (int, str) binds a = int | str, not just int.
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let expected = t.union(int, str_t);
        match t.match_arrow(&[a, a], &a, &no_bounds(), &[int, str_t]) {
            ArrowMatch::Known { result, .. } => {
                assert!(t.is_equivalent(&result, &expected), "a must bind int | str");
            }
            other => panic!("expected Known with unioned result, got {other:?}"),
        }
    }

    // Behavior 4: tuple-arity mismatch -> Invalid. Tuples width-match, so the
    // mismatch is a witness NARROWER than the pattern: a 3-field pattern cannot
    // accept a ground 2-tuple.
    #[test]
    fn tuple_arity_mismatch_yields_invalid() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let pat = t.tuple(&[a, a, a]);
        let int = t.int();
        let two = t.tuple(&[int, int]);
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[two]), ArrowMatch::Invalid);
    }

    // Behavior 4 (map-key presence): a pattern key absent from a ground witness map -> Invalid.
    #[test]
    fn missing_map_key_yields_invalid() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let key = MapKey::Atom("k".to_string());
        let other = MapKey::Atom("other".to_string());
        let pat = t.map(&[(key, a)]);
        let int = t.int();
        let witness = t.map(&[(other, int)]);
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[witness]), ArrowMatch::Invalid);
    }

    // Behavior 5: a variable pinned only by [] is ambiguous -> stays free
    // (Underconstrained). f(a) :: a applied to [] would bind a = [], but [] could
    // be a list of anything, so the binding is dropped and a stays free.
    #[test]
    fn empty_list_binding_is_ambiguous() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let empty = t.empty_list();
        match t.match_arrow(&[a], &a, &no_bounds(), &[empty]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free when pinned only by []");
            }
            other => panic!("expected Underconstrained for empty-list binding, got {other:?}"),
        }
    }

    // Bounds: a witness violating a variable's bound -> Invalid.
    #[test]
    fn bound_violation_yields_invalid() {
        // (a) -> a  when a: int, applied to (str) violates the bound.
        let mut t = Types::new();
        let v = TypeVarId(7);
        let a = t.type_var(v);
        let int = t.int();
        let str_t = t.str_t();
        let mut bounds = HashMap::new();
        bounds.insert(v, int);
        assert_eq!(t.match_arrow(&[a], &a, &bounds, &[str_t]), ArrowMatch::Invalid);
    }
}
