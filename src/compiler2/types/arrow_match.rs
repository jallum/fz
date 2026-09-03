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
//! map-key presence and tuple arity; and ambiguous empty-list witnesses.
//!
//! A WITNESS is what one parameter position OBSERVED: the argument the call
//! supplied there, and nothing else. It is never the pattern restated. A
//! pattern-derived witness — the pattern instantiated by whatever the argument
//! happened to pin — is wrong in both directions. It writes the pattern's own
//! unbound variables back into the observation, so `(a, b) -> b` observing
//! `(binary, int) -> int` would report `(a, int) -> int` and `binary` would be
//! unrecoverable by anything downstream. And it replaces whatever the argument
//! said wherever the pattern was ground, so `{int, a}` observing
//! `{int | binary, binary}` would report `{int, binary}` and the structural
//! gate below would compare `{int, binary}` against `{int, binary}` and accept
//! a call that must be rejected. The gate means `witness ⊆ σ(pattern)` only
//! because the witness is the argument; narrowing a witness toward its pattern
//! erases the very evidence the gate reads (fz-kdt.192).
//!
//! Ambiguity is a property of a WITNESS, not of a variable. `[]` is a member of
//! every list type, so a binding it pins is noise — but only for the position
//! that observed it. `([a], [a])` applied to `([int], [])` learns `a = int`
//! from the first parameter and nothing from the second, so the substitution is
//! collected per position, cleaned there, and only then unioned in.

use std::collections::{HashMap, HashSet};

use super::descr::Descr;
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
        if params.len() != args.len() {
            return ArrowMatch::Invalid;
        }
        self.instantiate_match(params, result, bounds, args)
    }

    /// One walk over `(params, args)`: each position's witness is its argument.
    /// The rows are the same length — `match_arrow` is the only caller and it
    /// answers arity, so arity is read once, there.
    fn instantiate_match(
        &mut self,
        params: &[Ty],
        result: &Ty,
        bounds: &HashMap<TypeVarId, Ty>,
        args: &[Ty],
    ) -> ArrowMatch {
        let mut sigma: Sigma<Ty> = Sigma::new();
        for (pattern, witness) in params.iter().zip(args.iter()) {
            // An uninhabited argument is a position no call can supply, so the
            // signature does not apply to this row. Ground disjointness is the
            // structural gate's job, below.
            if self.is_empty(witness) {
                return ArrowMatch::Invalid;
            }
            let mut position = Sigma::new();
            if self.collect_match_subst(pattern, witness, &mut position) == MatchWitness::Invalid {
                return ArrowMatch::Invalid;
            }
            self.drop_ambiguous_empty_list_bindings(pattern, witness, &mut position);
            self.merge_subst_union(&mut sigma, position);
        }

        let closed = self.close_bounds(bounds, &sigma);
        let mut bound_vars = bounds.keys().copied().collect::<Vec<_>>();
        bound_vars.sort();
        for var in bound_vars {
            let Some(actual) = sigma.get(&var) else {
                if closed.contains_key(&var) {
                    continue;
                }
                let (params, result) = self.instantiated_match(params, result, &sigma);
                return ArrowMatch::Underconstrained { params, result };
            };
            let bound = self.instantiate(&bounds[&var], &closed);
            if !self.is_subtype(actual, &bound) {
                return ArrowMatch::Invalid;
            }
        }

        for (pattern, witness) in params.iter().zip(args.iter()) {
            let expected = self.instantiate(pattern, &closed);
            if !self.has_vars(witness) && !self.has_vars(&expected) && !self.is_subtype(witness, &expected) {
                return ArrowMatch::Invalid;
            }
        }

        let (params, result) = self.instantiated_match(params, result, &closed);
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
        if let Some(outcome) = self.collect_correlated_tuple_match(pattern, witness, sigma) {
            return outcome;
        }
        if self.max_tuple_arity(witness) < arity {
            return if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.tuples.clear()) {
                MatchWitness::Unknown
            } else {
                MatchWitness::Invalid
            };
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
        sigma: &mut Sigma<Ty>,
    ) -> Option<MatchWitness> {
        let pattern_alternatives = self.tuple_positive_alternatives(pattern)?;
        let witness_alternatives = self.tuple_positive_alternatives(witness)?;
        let mut matched_any = false;
        let mut outcome = MatchWitness::Unknown;
        for pattern_fields in &pattern_alternatives {
            for witness_fields in &witness_alternatives {
                if pattern_fields.len() != witness_fields.len() {
                    continue;
                }
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
        } else if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.tuples.clear()) {
            Some(MatchWitness::Unknown)
        } else {
            Some(MatchWitness::Invalid)
        }
    }

    /// True when the witness can still be accepted by the pattern OUTSIDE the
    /// vetoing collector's kind: the witness intersects the pattern with that
    /// kind's component cleared. A kind collector defers (`Unknown`) instead
    /// of vetoing exactly when this holds — `:first | {:acc, a}` accepts
    /// `:first` through its atom member, but `:third` intersects nothing once
    /// the tuple component is cleared, so the veto stands. Whether the
    /// pattern merely HAS other-kind content is not the question; the witness
    /// must land in it.
    fn witness_escapes_kind(&mut self, pattern: &Ty, witness: &Ty, clear: fn(&mut Descr)) -> bool {
        let mut residual = self.descr(pattern).clone();
        clear(&mut residual);
        if residual.looks_empty() {
            return false;
        }
        let residual = self.intern(residual);
        let overlap = self.intersect(residual, *witness);
        !self.is_empty(&overlap)
    }

    /// Positive tuple alternatives of a type, each with its own arity — a
    /// union of tuples yields one field row per member, so a mixed-arity
    /// union (`{:done, a} | {:suspended, a, cont}`) matches each witness
    /// against the alternative of the witness's own width. `None` when the
    /// type has no tuple component or a component is not a plain positive
    /// product (negations or mixed arities inside one conjunction fall back
    /// to the caller's projection path).
    fn tuple_positive_alternatives(&mut self, ty: &Ty) -> Option<Vec<Vec<Ty>>> {
        let conjs = self.descr(ty).tuples.clone();
        if conjs.is_empty() {
            return None;
        }
        let mut alternatives = Vec::new();
        for conj in conjs {
            if !conj.neg.is_empty() || conj.pos.is_empty() {
                return None;
            }
            let arity = conj.pos[0].elems.len();
            if conj.pos.iter().any(|sig| sig.elems.len() != arity) {
                return None;
            }
            let mut fields: Option<Vec<Ty>> = None;
            for sig in conj.pos {
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
            return if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.lists.clear()) {
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
            return if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.resources.clear()) {
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
                if !self.has_vars(witness) && !self.witness_escapes_kind(pattern, witness, |d| d.maps.clear()) {
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
            return if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.funcs.clear()) {
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
        } else if self.has_vars(witness) || self.witness_escapes_kind(pattern, witness, |d| d.funcs.clear()) {
            MatchWitness::Unknown
        } else {
            MatchWitness::Invalid
        }
    }

    /// Drop the bindings ONE position collected through an exact `[]` witness.
    ///
    /// `[]` is a member of every list type, so a variable it pins could be a
    /// list of anything: the binding is noise, not evidence. The drop is scoped
    /// to the position that observed the `[]` because ambiguity belongs to the
    /// witness, not to the variable — `([a], [a])` applied to `([int], [])`
    /// learns `a = int` at the first parameter and nothing at the second, and
    /// vetoing `a` outright would throw the first parameter's proof away
    /// (fz-f98.16).
    fn drop_ambiguous_empty_list_bindings(&mut self, pattern: &Ty, witness: &Ty, position: &mut Sigma<Ty>) {
        let mut ambiguous = HashSet::new();
        let mut seen = HashSet::new();
        self.collect_ambiguous_empty_list_vars(pattern, witness, &mut ambiguous, &mut seen);
        position.retain(|var, _| !ambiguous.contains(var));
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
            // Ask the COLLECTOR what it bound here. `[]` has no element for
            // `collect_instantiation_subst` while `list_element_type` reads it
            // as `none`, so a second reader of the same fact disagreed with the
            // collector about what `[a]` observing `[]` pinned, and the cleaner
            // went blind on the raw argument. One reading of `[]`, one place.
            let mut direct = Sigma::new();
            self.collect_match_subst(pattern, witness, &mut direct);
            ambiguous_vars.extend(direct.into_keys());
            return;
        }

        self.collect_ambiguous_tuple_field_vars(pattern, witness, ambiguous_vars, seen);

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

    /// Descend a tuple position the way the COLLECTOR descends it, so the
    /// cleaner sees every `[]` the collector could have bound through.
    ///
    /// A union of tuples is a union of alternatives with their own arities, and
    /// the collector pairs each pattern alternative with the witness
    /// alternative of the same width that it overlaps
    /// (`collect_correlated_tuple_match`). Projecting both sides onto the
    /// pattern's widest arity instead cannot see inside a mixed-arity union —
    /// `{:done, a} | {:halted, a} | {:suspended, a, () -> any}` observing
    /// `{:done, []}` projects the witness at arity 3, finds it narrower, and
    /// walks away — so the `[]` binding survived the cleaner and the calculator
    /// claimed the result was the empty list as a runtime fact (fz-kdt.192).
    /// Only a type that is not a plain positive product falls back to the
    /// arity projection.
    fn collect_ambiguous_tuple_field_vars(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        ambiguous_vars: &mut HashSet<TypeVarId>,
        seen: &mut HashSet<(Ty, Ty)>,
    ) {
        if let (Some(pattern_alternatives), Some(witness_alternatives)) = (
            self.tuple_positive_alternatives(pattern),
            self.tuple_positive_alternatives(witness),
        ) {
            for pattern_fields in &pattern_alternatives {
                for witness_fields in &witness_alternatives {
                    if !self.tuple_fields_overlap(pattern_fields, witness_fields) {
                        continue;
                    }
                    for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
                        self.collect_ambiguous_empty_list_vars(pattern_field, witness_field, ambiguous_vars, seen);
                    }
                }
            }
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

    // The ambiguity of `[]` belongs to the POSITION that observed it, not to
    // the variable. `List.reverse/2` is spec'd `([a], [a]) :: [a]`, so a call
    // like `List.reverse([1, 2, 3], [])` pins `a = int` at the first parameter
    // and learns nothing at the second. The empty-list position must not veto
    // what the other position proved: vetoing it collapses `[a]` to `[]` and
    // the caller's good `[int]` argument gets narrowed to the empty list.
    #[test]
    fn empty_list_position_does_not_veto_a_variable_another_position_pins() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let int = t.int();
        let list_int = t.list(int);
        let empty = t.empty_list();
        match t.match_arrow(&[list_a, list_a], &list_a, &no_bounds(), &[list_int, empty]) {
            ArrowMatch::Known { params, result } => {
                assert_eq!(params, vec![list_int, list_int], "both parameters instantiate to [int]");
                assert_eq!(result, list_int, "the result instantiates to [int]");
            }
            other => panic!("expected Known with a = int, got {other:?}"),
        }
    }

    // A union-of-tuples pattern whose alternatives have DIFFERENT arities must
    // match a ground witness against the alternative of the witness's own
    // arity, not demand the widest arity of the union. This is the
    // `Enum.reduce_finish` shape: `{:done, a} | {:halted, a} | {:suspended, a,
    // () -> any}` applied to `{:done, int}` grounds a = int.
    #[test]
    fn mixed_arity_tuple_union_pattern_matches_by_alternative_arity() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let done = t.atom_lit("done");
        let halted = t.atom_lit("halted");
        let suspended = t.atom_lit("suspended");
        let any = t.any();
        let continuation = t.arrow(&[], any);
        let done_pat = t.tuple(&[done, a]);
        let halted_pat = t.tuple(&[halted, a]);
        let suspended_pat = t.tuple(&[suspended, a, continuation]);
        let pat = t.union(done_pat, halted_pat);
        let pat = t.union(pat, suspended_pat);
        let int = t.int();
        let witness = t.tuple(&[done, int]);
        match t.match_arrow(&[pat], &a, &no_bounds(), &[witness]) {
            ArrowMatch::Known { result, .. } => assert_eq!(result, int),
            other => panic!("expected Known with a = int, got {other:?}"),
        }
    }

    // The same shape must still reject a witness no alternative accepts.
    #[test]
    fn mixed_arity_tuple_union_pattern_rejects_uncovered_witness() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let done = t.atom_lit("done");
        let suspended = t.atom_lit("suspended");
        let any = t.any();
        let continuation = t.arrow(&[], any);
        let done_pat = t.tuple(&[done, a]);
        let suspended_pat = t.tuple(&[suspended, a, continuation]);
        let pat = t.union(done_pat, suspended_pat);
        let other_tag = t.atom_lit("other");
        let int = t.int();
        let witness = t.tuple(&[other_tag, int]);
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[witness]), ArrowMatch::Invalid);
    }

    // A pattern that unions ACROSS kinds (`:first | {:acc, a}`) accepts a
    // witness through its non-tuple member: the tuple collector must not veto
    // the signature for a witness the atom member covers. This is the
    // `Enum.reduce_first_acc` shape: applied to `:first` the signature fits
    // and `a` stays free.
    #[test]
    fn cross_kind_union_pattern_accepts_a_non_tuple_witness() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let first = t.atom_lit("first");
        let acc_tag = t.atom_lit("acc");
        let acc_pat = t.tuple(&[acc_tag, a]);
        let pat = t.union(first, acc_pat);
        match t.match_arrow(&[pat], &a, &no_bounds(), &[first]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the :first member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    // The same cross-kind union nested inside a tuple field: `{:done, :first |
    // {:acc, a}}` applied to `{:done, :first}` (the `reduce_first_finish`
    // shape) fits with `a` free.
    #[test]
    fn cross_kind_union_nested_in_a_tuple_field_accepts_the_atom_member() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let done = t.atom_lit("done");
        let first = t.atom_lit("first");
        let acc_tag = t.atom_lit("acc");
        let acc_pat = t.tuple(&[acc_tag, a]);
        let state_pat = t.union(first, acc_pat);
        let pat = t.tuple(&[done, state_pat]);
        let witness_field = t.atom_lit("first");
        let witness = t.tuple(&[done, witness_field]);
        match t.match_arrow(&[pat], &a, &no_bounds(), &[witness]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the {{:done, :first}} member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    // A cross-kind union still rejects a TUPLE witness that no tuple member
    // accepts: `{:other, int}` cannot be `:first` (kind-disjoint) and matches
    // no tuple alternative.
    #[test]
    fn cross_kind_union_pattern_rejects_an_uncovered_tuple_witness() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let first = t.atom_lit("first");
        let acc_tag = t.atom_lit("acc");
        let acc_pat = t.tuple(&[acc_tag, a]);
        let pat = t.union(first, acc_pat);
        let other_tag = t.atom_lit("other");
        let int = t.int();
        let witness = t.tuple(&[other_tag, int]);
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[witness]), ArrowMatch::Invalid);
    }

    // The veto question is whether the WITNESS lands in the pattern's
    // other-kind content, not whether such content exists: `:third` is
    // accepted by neither `:first` nor `{:acc, a}`, so the signature is
    // Invalid even though the pattern is a cross-kind union.
    #[test]
    fn cross_kind_union_pattern_rejects_a_witness_no_member_accepts() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let first = t.atom_lit("first");
        let acc_tag = t.atom_lit("acc");
        let acc_pat = t.tuple(&[acc_tag, a]);
        let pat = t.union(first, acc_pat);
        let third = t.atom_lit("third");
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[third]), ArrowMatch::Invalid);
    }

    // The same acceptance question per kind collector: a cross-kind union
    // whose non-<kind> member does not accept the witness is Invalid; one
    // whose non-<kind> member does accept it defers with the variable free.
    #[test]
    fn cross_kind_union_with_list_member_vetoes_by_witness_acceptance() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_pat = t.list(a);
        let empty_tag = t.atom_lit("empty");
        let pat = t.union(list_pat, empty_tag);
        let third = t.atom_lit("third");
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[third]), ArrowMatch::Invalid);
        let empty_witness = t.atom_lit("empty");
        match t.match_arrow(&[pat], &a, &no_bounds(), &[empty_witness]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the :empty member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    #[test]
    fn cross_kind_union_with_resource_member_vetoes_by_witness_acceptance() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let resource_pat = t.resource(a);
        let none_tag = t.atom_lit("none");
        let pat = t.union(resource_pat, none_tag);
        let third = t.atom_lit("third");
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[third]), ArrowMatch::Invalid);
        let none_witness = t.atom_lit("none");
        match t.match_arrow(&[pat], &a, &no_bounds(), &[none_witness]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the :none member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    #[test]
    fn cross_kind_union_with_map_member_vetoes_by_witness_acceptance() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let key = MapKey::Atom("k".to_string());
        let map_pat = t.map(&[(key, a)]);
        let none_tag = t.atom_lit("none");
        let pat = t.union(map_pat, none_tag);
        let third = t.atom_lit("third");
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[third]), ArrowMatch::Invalid);
        let none_witness = t.atom_lit("none");
        match t.match_arrow(&[pat], &a, &no_bounds(), &[none_witness]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the :none member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
        }
    }

    #[test]
    fn cross_kind_union_with_arrow_member_vetoes_by_witness_acceptance() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let arrow_pat = t.arrow(&[a], a);
        let none_tag = t.atom_lit("none");
        let pat = t.union(arrow_pat, none_tag);
        let third = t.atom_lit("third");
        assert_eq!(t.match_arrow(&[pat], &a, &no_bounds(), &[third]), ArrowMatch::Invalid);
        let none_witness = t.atom_lit("none");
        match t.match_arrow(&[pat], &a, &no_bounds(), &[none_witness]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(t.has_vars(&result), "a must stay free for the :none member");
            }
            other => panic!("expected Underconstrained, got {other:?}"),
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

    #[test]
    fn dependent_rhs_only_bound_closes_before_validation() {
        let mut t = Types::new();
        let outer = TypeVarId(7);
        let inner = TypeVarId(3);
        let outer_ty = t.type_var(outer);
        let inner_ty = t.type_var(inner);
        let a = t.atom_lit("a");
        let b = t.atom_lit("b");
        let domain = t.union(a, b);
        let mut bounds = HashMap::new();
        bounds.insert(outer, inner_ty);
        bounds.insert(inner, domain);

        match t.match_arrow(&[outer_ty], &outer_ty, &bounds, &[a]) {
            ArrowMatch::Known { result, .. } => assert_eq!(result, a),
            other => panic!("expected known dependent-bound match, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// PINNED VERDICTS. The adversarial constructions the fz-kdt.120, fz-kdt.184
// and fz-kdt.192 reviews built to attack this calculator, promoted from
// throwaway probes to named tests that assert the verdict it gives them.
// A pin is a fact, not an endorsement: several record answers that are wrong
// and say so, naming the ticket that must move them. None of them may move
// without an argument written here.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod pinned_verdicts {
    use super::super::MapKey;
    use super::*;
    use std::collections::HashMap;

    fn no_bounds() -> HashMap<TypeVarId, Ty> {
        HashMap::new()
    }

    /// The verdict as the pin table records it.
    fn render(t: &Types, v: &ArrowMatch) -> String {
        match v {
            ArrowMatch::Known { params, result } => {
                let ps: Vec<String> = params.iter().map(|p| t.display(p)).collect();
                format!("Known params=[{}] result={}", ps.join(", "), t.display(result))
            }
            ArrowMatch::Underconstrained { params, result } => {
                let ps: Vec<String> = params.iter().map(|p| t.display(p)).collect();
                format!(
                    "Underconstrained params=[{}] result={}",
                    ps.join(", "),
                    t.display(result)
                )
            }
            ArrowMatch::Invalid => "Invalid".to_string(),
        }
    }

    // R0. Is an INTERSECTION of arrows (an overloaded callable) even
    // representable, and does `callable_clauses` hand the matcher two clauses?
    #[test]
    fn r0_overload_representation() {
        let mut t = Types::new();
        let int = t.int();
        let str_t = t.str_t();
        let f1 = t.arrow(&[int], int);
        let f2 = t.arrow(&[str_t], str_t);
        let and = t.intersect(f1, f2);
        let or = t.union(f1, f2);
        assert_eq!(
            t.display(&and),
            "(int | binary) -> none",
            "an intersection of arrows collapses to one clause"
        );
        assert_eq!(t.callable_clauses(&and).map(|c| c.len()), Some(1));
        assert_eq!(t.display(&or), "(binary) -> binary | (int) -> int");
        assert_eq!(t.callable_clauses(&or).map(|c| c.len()), Some(2));
        assert!(!t.is_empty(&and));
    }

    // R1. An OVERLOADED (intersection) callable argument. `map([a], (a) -> b)
    // :: [b]` at `([int], ((int)->int) and ((binary)->binary))`. The call is
    // legal: the overload accepts ints. If the upper bounds of the two clauses
    // are MET, `a`'s upper is `int ∩ binary = none` and the lower `int` escapes
    // it — a FALSE Invalid.
    #[test]
    fn r1_overloaded_callable_argument() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let f1 = t.arrow(&[int], int);
        let f2 = t.arrow(&[str_t], str_t);
        let overloaded = t.intersect(f1, f2);
        let list_a = t.list(a);
        let mapper = t.arrow(&[a], b);
        let list_b = t.list(b);
        let list_int = t.list(int);
        let v = t.match_arrow(&[list_a, mapper], &list_b, &no_bounds(), &[list_int, overloaded]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[int | binary], (int | binary) -> none] result=[none]",
            "R1 overloaded"
        );
    }

    // R2. MOVED, and the move is a FIX. A UNION-of-arrows callable argument:
    // `(int)->int | (binary)->binary` guarantees nothing about which clause
    // you hold, so the only safe domain is `int ∩ binary = none` and Invalid
    // is the honest answer. The pattern-derived witness restated the argument
    // as the pattern and reported `Known [int | binary]` -- an unsound accept
    // reached with no polarity machinery at all, just by asking what the call
    // supplied.
    #[test]
    fn r2_union_of_arrows_argument() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let f1 = t.arrow(&[int], int);
        let f2 = t.arrow(&[str_t], str_t);
        let either = t.union(f1, f2);
        let list_a = t.list(a);
        let mapper = t.arrow(&[a], b);
        let list_b = t.list(b);
        let list_int = t.list(int);
        let v = t.match_arrow(&[list_a, mapper], &list_b, &no_bounds(), &[list_int, either]);
        assert_eq!(render(&t, &v), "Invalid", "R2 union-of-arrows");
    }

    // R3. A variable in a MAP VALUE under an arrow parameter: is the map field
    // covariant, and does the flip reach through it?
    // `f([a], ({k: a}) -> nil) :: [a]` at `([int], ({k: any}) -> nil)`.
    #[test]
    fn r3_map_field_under_an_arrow_parameter() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let key = MapKey::Atom("k".to_string());
        let int = t.int();
        let any = t.any();
        let nil = t.nil();
        let pat_map = t.map(&[(key.clone(), a)]);
        let wit_map = t.map(&[(key, any)]);
        let pat_fn = t.arrow(&[pat_map], nil);
        let wit_fn = t.arrow(&[wit_map], nil);
        let list_a = t.list(a);
        let list_int = t.list(int);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, wit_fn]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[any], (%{:k: any}) -> :nil] result=[any]",
            "R3 map-under-param"
        );
    }

    // R4. The same through a RESOURCE payload — the lattice's other
    // single-field carrier. If a resource payload were INVARIANT, neither a
    // lower nor an upper bound would be the whole story.
    #[test]
    fn r4_resource_payload_under_an_arrow_parameter() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let nil = t.nil();
        let pat_res = t.resource(a);
        let wit_res = t.resource(any);
        let pat_fn = t.arrow(&[pat_res], nil);
        let wit_fn = t.arrow(&[wit_res], nil);
        let list_a = t.list(a);
        let list_int = t.list(int);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, wit_fn]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[any], (resource(any)) -> :nil] result=[any]",
            "R4 resource-under-param"
        );
        // And covariantly, for contrast: resource(any) at resource(a).
        let v2 = t.match_arrow(&[pat_res], &a, &no_bounds(), &[wit_res]);
        assert_eq!(
            render(&t, &v2),
            "Known params=[resource(any)] result=any",
            "R4 resource-covariant"
        );
    }

    // R5. A PARTIALLY GROUND callable argument — the state a closure passes
    // through while the fixpoint is still running. `map([a], (a) -> b) :: [b]`
    // at `([int | binary], (int) -> b999)`. The closure's parameter is already
    // ground and NARROWER than the list the call also supplies.
    #[test]
    fn r5_partially_ground_closure_narrower_than_the_list() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let mixed = t.union(int, str_t);
        let list_mixed = t.list(mixed);
        let list_a = t.list(a);
        let mapper = t.arrow(&[a], b);
        let list_b = t.list(b);
        let ret_var = t.type_var(TypeVarId(999));
        let half = t.arrow(&[int], ret_var);
        let v = t.match_arrow(&[list_a, mapper], &list_b, &no_bounds(), &[list_mixed, half]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[[int | binary], (int | binary) -> a1] result=[a1]",
            "R5 half-ground closure"
        );
    }

    // R6. THREE parameter descents: `f((((a) -> nil) -> nil) -> nil) :: [a]`
    // at the same shape with `int` at the leaf. An odd number of flips is an
    // UPPER bound, so `a` must stay free.
    #[test]
    fn r6_three_deep_arrow_is_still_an_upper_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let nil = t.nil();
        let int = t.int();
        let p1 = t.arrow(&[a], nil);
        let p2 = t.arrow(&[p1], nil);
        let p3 = t.arrow(&[p2], nil);
        let w1 = t.arrow(&[int], nil);
        let w2 = t.arrow(&[w1], nil);
        let w3 = t.arrow(&[w2], nil);
        let list_a = t.list(a);
        let v = t.match_arrow(&[p3], &list_a, &no_bounds(), &[w3]);
        assert_eq!(
            render(&t, &v),
            "Known params=[(((int) -> :nil) -> :nil) -> :nil] result=[int]",
            "R6 three-deep"
        );
    }

    // R7. An arrow RESULT whose parameter is a TUPLE carrying the variable:
    // `f(a, ({a, int}) -> nil) :: ({a, int}) -> nil` at `(int, ({any, int}) ->
    // nil)`. The published result must use the LOWER bound.
    #[test]
    fn r7_tuple_inside_a_contravariant_result() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let nil = t.nil();
        let pat_pair = t.tuple(&[a, int]);
        let pat_fn = t.arrow(&[pat_pair], nil);
        let wit_pair = t.tuple(&[any, int]);
        let wit_fn = t.arrow(&[wit_pair], nil);
        let v = t.match_arrow(&[a, pat_fn], &pat_fn, &no_bounds(), &[int, wit_fn]);
        assert_eq!(
            render(&t, &v),
            "Known params=[any, ({any, int}) -> :nil] result=({any, int}) -> :nil",
            "R7 tuple-in-contravariant-result"
        );
    }

    // R8. A DECLARED bound meeting an observed upper bound.
    // `f(a, (a) -> nil) :: a when a: int | float` at `(int, (float) -> nil)`.
    // The lower bound is `int`, the upper `float`: no solution exists.
    #[test]
    fn r8_declared_bound_meets_an_upper_bound() {
        let mut t = Types::new();
        let v = TypeVarId(7);
        let tv = t.type_var(v);
        let int = t.int();
        let float = t.float();
        let nil = t.nil();
        let dom = t.union(int, float);
        let mut bounds = HashMap::new();
        bounds.insert(v, dom);
        let pat_fn = t.arrow(&[tv], nil);
        let wit_fn = t.arrow(&[float], nil);
        let verdict = t.match_arrow(&[tv, pat_fn], &tv, &bounds, &[int, wit_fn]);
        assert_eq!(render(&t, &verdict), "Invalid", "R8 bound-vs-upper");
    }

    // R9. `any` and `none` on both sides of a parameter arrow.
    #[test]
    fn r9_any_and_none_witnesses() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let none = t.none();
        let nil = t.nil();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let pat_fn = t.arrow(&[a], nil);
        let none_fn = t.arrow(&[none], nil);
        let any_fn = t.arrow(&[any], nil);
        let v1 = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, none_fn]);
        assert_eq!(render(&t, &v1), "Invalid", "R9 (none)->nil argument");
        let v2 = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, any_fn]);
        assert_eq!(
            render(&t, &v2),
            "Known params=[[any], (any) -> :nil] result=[any]",
            "R9 (any)->nil argument"
        );
        // any as the covariant witness of the element itself.
        let list_any = t.list(any);
        let v3 = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_any, any_fn]);
        assert_eq!(
            render(&t, &v3),
            "Known params=[[any], (any) -> :nil] result=[any]",
            "R9 [any] + (any)->nil"
        );
    }

    // R10. A callable argument with MORE parameters than the pattern declares.
    #[test]
    fn r10_arity_mismatch_under_contravariance() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let pat_fn = t.arrow(&[a], nil);
        let wide = t.arrow(&[int, int], nil);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, wide]);
        assert_eq!(render(&t, &v), "Invalid", "R10 wide callable");
    }

    // R11. The report's headline off-corpus case, and this ticket's own
    // reproducer: `reduce([a], b, (a, b) -> b) :: b` at
    // `([int], int, (binary, int) -> int)`. The third position OBSERVES
    // `(binary, int) -> int`; a pattern-derived witness restated it as
    // `(a, int) -> int` as soon as `a` failed to bind there, and `binary` --
    // the whole reason the call is illegal -- was unrecoverable from it. The
    // verdict is `Invalid` either way (the polluted union reached it by
    // another route), so what this pins is the ARGUMENT'S survival, not a
    // changed answer; the discriminating cases are the two structural-gate
    // tests below.
    #[test]
    fn r11_reduce_with_a_binary_reducer() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let reducer = t.arrow(&[a, b], b);
        let bad = t.arrow(&[str_t, int], int);
        let v = t.match_arrow(&[list_a, b, reducer], &b, &no_bounds(), &[list_int, int, bad]);
        assert_eq!(render(&t, &v), "Invalid", "R11 reduce/binary reducer");
    }

    // R12. A FREE VARIABLE inside the upper bound: `f([a], (a) -> nil) :: [a]`
    // at `([int], (c) -> nil)` where `c` is some other variable. `is_subtype`
    // over a var-carrying upper bound is where a solvability gate would be
    // most likely to misjudge.
    #[test]
    fn r12_free_variable_inside_the_upper_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let c = t.type_var(TypeVarId(4242));
        let list_a = t.list(a);
        let list_int = t.list(int);
        let pat_fn = t.arrow(&[a], nil);
        let var_fn = t.arrow(&[c], nil);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, var_fn]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[int], (int) -> :nil] result=[int]",
            "R12 var upper bound"
        );
    }

    // R13. TWO callable arguments bounding the same variable from above with
    // disjoint domains: the meet is `none` and every lower bound escapes it.
    #[test]
    fn r13_two_disjoint_upper_bounds() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let nil = t.nil();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let pat_fn = t.arrow(&[a], nil);
        let int_fn = t.arrow(&[int], nil);
        let str_fn = t.arrow(&[str_t], nil);
        let v = t.match_arrow(
            &[list_a, pat_fn, pat_fn],
            &list_a,
            &no_bounds(),
            &[list_int, int_fn, str_fn],
        );
        assert_eq!(render(&t, &v), "Invalid", "R13 two disjoint uppers");
    }

    // R14. The A2 question with the variable ALSO in a covariant result:
    // `each([a], (a) -> any) :: :ok` has no `a` in the result at all, but
    // `f((a) -> nil) :: [a]` does. Does anything downstream want `[any]`?
    #[test]
    fn r14_only_upper_bounded_variable_in_the_result() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let nil = t.nil();
        let any = t.any();
        let int = t.int();
        let pat_fn = t.arrow(&[a], nil);
        let list_a = t.list(a);
        let any_fn = t.arrow(&[any], nil);
        let int_fn = t.arrow(&[int], nil);
        let v1 = t.match_arrow(&[pat_fn], &list_a, &no_bounds(), &[any_fn]);
        assert_eq!(
            render(&t, &v1),
            "Known params=[(any) -> :nil] result=[any]",
            "R14 only-upper (any)"
        );
        let v2 = t.match_arrow(&[pat_fn], &list_a, &no_bounds(), &[int_fn]);
        assert_eq!(
            render(&t, &v2),
            "Known params=[(int) -> :nil] result=[int]",
            "R14 only-upper (int)"
        );
    }

    // R15. An `[]` witness UNDER an arrow parameter — the empty-list cleaner's
    // `side` flip. `f([a], (a) -> nil) :: [a]` at `([int], ([]) -> nil)`.
    #[test]
    fn r15_empty_list_under_an_arrow_parameter() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let empty = t.empty_list();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let pat_fn = t.arrow(&[a], nil);
        let empty_fn = t.arrow(&[empty], nil);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, empty_fn]);
        assert_eq!(render(&t, &v), "Invalid", "R15 [] under a parameter");
        // And the shape where the [] is the ONLY thing that could veto `a`:
        // `f([a], ([a]) -> nil) :: [a]` at `([int], ([]) -> nil)`.
        let list_a_inner = t.list(a);
        let pat_fn2 = t.arrow(&[list_a_inner], nil);
        let v2 = t.match_arrow(&[list_a, pat_fn2], &list_a, &no_bounds(), &[list_int, empty_fn]);
        assert_eq!(render(&t, &v2), "Invalid", "R15 [] as the parameter itself");
    }

    // R16. Both polarities of the SAME variable in the result:
    // `f(a, (a) -> nil) :: {a, (a) -> nil}` at `(int, (any) -> nil)`.
    #[test]
    fn r16_both_polarities_in_the_result() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let nil = t.nil();
        let pat_fn = t.arrow(&[a], nil);
        let res = t.tuple(&[a, pat_fn]);
        let wit_fn = t.arrow(&[any], nil);
        let v = t.match_arrow(&[a, pat_fn], &res, &no_bounds(), &[int, wit_fn]);
        assert_eq!(
            render(&t, &v),
            "Known params=[any, (any) -> :nil] result={any, (any) -> :nil}",
            "R16 both polarities"
        );
    }

    // R17. A variable whose only LOWER bound arrives through an arrow's RETURN
    // while an arrow PARAMETER bounds it from above with something disjoint:
    // `f((int) -> a, (a) -> nil) :: [a]` at `((int) -> int, (binary) -> nil)`.
    #[test]
    fn r17_lower_from_a_return_upper_from_a_parameter() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let nil = t.nil();
        let producer_pat = t.arrow(&[int], a);
        let consumer_pat = t.arrow(&[a], nil);
        let producer = t.arrow(&[int], int);
        let consumer = t.arrow(&[str_t], nil);
        let list_a = t.list(a);
        let v = t.match_arrow(
            &[producer_pat, consumer_pat],
            &list_a,
            &no_bounds(),
            &[producer, consumer],
        );
        assert_eq!(render(&t, &v), "Invalid", "R17 return-lower vs param-upper");
    }

    // R18. `[]` observed at a CONTRAVARIANT position. fz-f98.16's whole point is
    // that `[]` is a member of every list type, so it is not evidence — the
    // cleaner drops such bindings on the LOWER side. Nothing drops them on the
    // UPPER side, so `f([a], ([a]) -> nil) :: [a]` at `([int], ([]) -> nil)`
    // reads `a ⊆ none` and the list's `int` escapes it.
    #[test]
    fn r18_empty_list_as_a_contravariant_witness() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let empty = t.empty_list();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let inner = t.list(a);
        let pat_fn = t.arrow(&[inner], nil);
        let empty_fn = t.arrow(&[empty], nil);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_int, empty_fn]);
        assert_eq!(render(&t, &v), "Invalid", "R18 [] at a callable's list parameter");
    }

    // R19. The same one level up: the callable takes the ELEMENT and the list
    // is a list of lists, so `a`'s lower bound is `[int]` and its upper is the
    // `[]` the callable was observed to take.
    #[test]
    fn r19_empty_list_as_the_contravariant_element() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let empty = t.empty_list();
        let list_int = t.list(int);
        let list_list_int = t.list(list_int);
        let list_a = t.list(a);
        let pat_fn = t.arrow(&[a], nil);
        let empty_fn = t.arrow(&[empty], nil);
        let v = t.match_arrow(&[list_a, pat_fn], &list_a, &no_bounds(), &[list_list_int, empty_fn]);
        assert_eq!(render(&t, &v), "Invalid", "R19 [] as the contravariant element");
    }

    // R20. MOVED, and it is a PRECISION LOSS. One TUPLE parameter carrying
    // both a lower-bound list and a `[]` under an arrow's parameter. At the
    // pattern-derived witness this answered `Known [int]`, but only because
    // the restatement had already erased the `[]` before the cleaner looked;
    // the `[]` the call really supplied vetoes `a` for the whole parameter,
    // and the answer is now `Underconstrained`.
    //
    // The veto's scope is the PARAMETER, so this DISAGREES with its
    // two-parameter sibling X6B: the same constraint (`a` observed at `[]`
    // once and at `[int]` once) answers `Known [int]` spread over two
    // parameters and `Underconstrained` folded into one tuple. That is
    // fz-f98.16's per-position scoping seen from inside a single position --
    // a real loss, not a consistency win. It dies with the cleaner in
    // fz-kdt.120, which marks ambiguity at the moment of binding.
    #[test]
    fn r20_cleaner_flip_inside_one_position() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let empty = t.empty_list();
        let list_a = t.list(a);
        let inner = t.list(a);
        let pat_fn = t.arrow(&[inner], nil);
        let pat = t.tuple(&[list_a, pat_fn]);
        let list_int = t.list(int);
        let empty_fn = t.arrow(&[empty], nil);
        let arg = t.tuple(&[list_int, empty_fn]);
        let v = t.match_arrow(&[pat], &list_a, &no_bounds(), &[arg]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[{[a0], ([a0]) -> :nil}] result=[a0]",
            "R20 cleaner flip in one position"
        );
    }

    // --- A-series (fz-kdt.120 cold review) -------------------------------------

    /// An arrow whose every leaf is a distinct free variable: the shape a
    /// callable argument has before its body has been analyzed.
    fn unanalyzed_arrow(t: &mut Types, arity: usize) -> Ty {
        let args: Vec<Ty> = (0..arity).map(|i| t.type_var(TypeVarId(900 + i as u32))).collect();
        let ret = t.type_var(TypeVarId(999));
        t.arrow(&args, ret)
    }

    // A1. Two arrow-parameter descents restore the original direction:
    // `f(((a) -> int) -> nil) :: [a]` at `(((binary) -> int) -> nil)`.
    #[test]
    fn a1_nested_arrow_parameters() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let nil = t.nil();
        let str_t = t.str_t();
        let inner_pat = t.arrow(&[a], int);
        let pat = t.arrow(&[inner_pat], nil);
        let list_a = t.list(a);
        let inner_wit = t.arrow(&[str_t], int);
        let wit = t.arrow(&[inner_wit], nil);
        let v = t.match_arrow(&[pat], &list_a, &no_bounds(), &[wit]);
        assert_eq!(
            render(&t, &v),
            "Known params=[((binary) -> int) -> :nil] result=[binary]",
            "A1"
        );
    }

    // A2. A variable occurring ONLY under an arrow parameter.
    #[test]
    fn a2_only_negative_occurrence() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let nil = t.nil();
        let any = t.any();
        let pat = t.arrow(&[a], nil);
        let list_a = t.list(a);
        let wit = t.arrow(&[any], nil);
        let v = t.match_arrow(&[pat], &list_a, &no_bounds(), &[wit]);
        assert_eq!(render(&t, &v), "Known params=[(any) -> :nil] result=[any]", "A2");
    }

    // A3. The reducer shape: `reduce([a], b, (a, b) -> b) :: b` at
    // `([int], [], (any, [int]) -> [int])`.
    #[test]
    fn a3_reducer_parameter_widening() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let list_a = t.list(a);
        let reducer = t.arrow(&[a, b], b);
        let int = t.int();
        let any = t.any();
        let list_int = t.list(int);
        let empty = t.empty_list();
        let ground = t.arrow(&[any, list_int], list_int);
        let v = t.match_arrow(&[list_a, b, reducer], &b, &no_bounds(), &[list_int, empty, ground]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[any], [int], (any, [int]) -> [int]] result=[int]",
            "A3"
        );
    }

    // A4. A variable in a CONTRAVARIANT spot of the RESULT:
    // `f(a, (a) -> nil) :: (a) -> nil` at `(int, (any) -> nil)`.
    #[test]
    fn a4_contravariant_result_position() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let nil = t.nil();
        let any = t.any();
        let int = t.int();
        let arrow_pat = t.arrow(&[a], nil);
        let result_pat = t.arrow(&[a], nil);
        let wit = t.arrow(&[any], nil);
        let v = t.match_arrow(&[a, arrow_pat], &result_pat, &no_bounds(), &[int, wit]);
        assert_eq!(
            render(&t, &v),
            "Known params=[any, (any) -> :nil] result=(any) -> :nil",
            "A4"
        );
    }

    // A5. The same join read by the BOUND check:
    // `f(a, (a) -> nil) :: a when a: int` at `(int, (any) -> nil)`.
    #[test]
    fn a5_negative_occurrence_and_a_declared_bound() {
        let mut t = Types::new();
        let v = TypeVarId(7);
        let a = t.type_var(v);
        let nil = t.nil();
        let any = t.any();
        let int = t.int();
        let arrow_pat = t.arrow(&[a], nil);
        let mut bounds = HashMap::new();
        bounds.insert(v, int);
        let wit = t.arrow(&[any], nil);
        let verdict = t.match_arrow(&[a, arrow_pat], &a, &bounds, &[int, wit]);
        assert_eq!(render(&t, &verdict), "Invalid", "A5");
    }

    // A6. A variable inside a TUPLE inside an arrow RETURN, unanalyzed then ground.
    #[test]
    fn a6_variable_in_an_arrow_return() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let c = t.param_alpha(2);
        let list_a = t.list(a);
        let pair = t.tuple(&[b, c]);
        let fn_pat = t.arrow(&[a], pair);
        let list_b = t.list(b);
        let int = t.int();
        let list_int = t.list(int);
        let str_t = t.str_t();
        let nil = t.nil();
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let v1 = t.match_arrow(&[list_a, fn_pat], &list_b, &no_bounds(), &[list_int, unanalyzed]);
        assert_eq!(
            render(&t, &v1),
            "Underconstrained params=[[int], (int) -> {a1, a2}] result=[a1]",
            "A6 unanalyzed"
        );
        let ground_ret = t.tuple(&[str_t, nil]);
        let ground = t.arrow(&[int], ground_ret);
        let v2 = t.match_arrow(&[list_a, fn_pat], &list_b, &no_bounds(), &[list_int, ground]);
        assert_eq!(
            render(&t, &v2),
            "Known params=[[int], (int) -> {binary, :nil}] result=[binary]",
            "A6 ground"
        );
    }

    // A7. `f(a, a) :: a` at `(int, <unanalyzed arrow>)`.
    #[test]
    fn a7_var_carrying_argument_contributes_no_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let v = t.match_arrow(&[a, a], &a, &no_bounds(), &[int, unanalyzed]);
        assert_eq!(render(&t, &v), "Known params=[int, int] result=int", "A7");
    }

    // A8. `f(a, a, a) :: a` at `(int, [], <unanalyzed arrow>)`.
    #[test]
    fn a8_three_positions_one_variable() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let empty = t.empty_list();
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let v = t.match_arrow(&[a, a, a], &a, &no_bounds(), &[int, empty, unanalyzed]);
        assert_eq!(render(&t, &v), "Invalid", "A8");
    }

    // A9. A declared bound answering a var-carrying argument: `dbg(t) :: t when t: any`.
    #[test]
    fn a9_declared_bound_answers_a_var_carrying_argument() {
        let mut t = Types::new();
        let v = TypeVarId(7);
        let tv = t.type_var(v);
        let any = t.any();
        let mut bounds = HashMap::new();
        bounds.insert(v, any);
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let verdict = t.match_arrow(&[tv], &tv, &bounds, &[unanalyzed]);
        assert_eq!(render(&t, &verdict), "Known params=[any] result=any", "A9");
    }

    // A10. `f(t) :: t when t: int | float` at `[]`.
    #[test]
    fn a10_empty_list_against_a_numeric_bound() {
        let mut t = Types::new();
        let v = TypeVarId(7);
        let tv = t.type_var(v);
        let int = t.int();
        let float = t.float();
        let dom = t.union(int, float);
        let mut bounds = HashMap::new();
        bounds.insert(v, dom);
        let empty = t.empty_list();
        let verdict = t.match_arrow(&[tv], &tv, &bounds, &[empty]);
        assert_eq!(render(&t, &verdict), "Invalid", "A10");
    }

    // A11. The fz-f98.16 shape with the empty list FIRST.
    #[test]
    fn a11_empty_list_position_may_come_first() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let int = t.int();
        let list_int = t.list(int);
        let empty = t.empty_list();
        let v = t.match_arrow(&[list_a, list_a], &list_a, &no_bounds(), &[empty, list_int]);
        assert_eq!(render(&t, &v), "Known params=[[int], [int]] result=[int]", "A11");
    }

    // A12. A union pattern with a top-level variable member: `f(a | int) :: [a]` at `int`.
    #[test]
    fn a12_union_pattern_member_covers_the_witness() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let pat = t.union(a, int);
        let list_a = t.list(a);
        let v = t.match_arrow(&[pat], &list_a, &no_bounds(), &[int]);
        assert_eq!(render(&t, &v), "Underconstrained params=[int | a0] result=[a0]", "A12");
    }

    // A13. `filter`'s shape: `(t(a), (a) -> any) :: [a]` at `([int], (any) -> bool)`.
    #[test]
    fn a13_predicate_with_an_any_parameter() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let any = t.any();
        let pred_pat = t.arrow(&[a], any);
        let int = t.int();
        let list_int = t.list(int);
        let bool_t = t.bool();
        let ground_pred = t.arrow(&[any], bool_t);
        let v = t.match_arrow(&[list_a, pred_pat], &list_a, &no_bounds(), &[list_int, ground_pred]);
        assert_eq!(render(&t, &v), "Known params=[[any], (any) -> any] result=[any]", "A13");
    }

    // A14. `none` at a bare variable.
    #[test]
    fn a14_none_argument() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let none = t.none();
        let v = t.match_arrow(&[a], &a, &no_bounds(), &[none]);
        assert_eq!(render(&t, &v), "Invalid", "A14");
    }

    // A15 (pre-existing, fz-kdt.182). `union([], [int])` interns distinctly
    // from `[int]` though the two denote the same set.
    #[test]
    fn a15_empty_list_union_is_not_normalised() {
        let mut t = Types::new();
        let int = t.int();
        let list_int = t.list(int);
        let empty = t.empty_list();
        let joined = t.union(empty, list_int);
        assert_eq!(t.display(&joined), "[] | [int]");
        assert!(joined != list_int, "identity differs");
        assert!(t.is_equivalent(&joined, &list_int), "denotation does not");
    }

    // A16 (pre-existing, fz-kdt.181). `intersect` DELETES a union member whose
    // surface carries a free variable.
    #[test]
    fn a16_intersect_deletes_a_var_carrying_union_member() {
        let mut t = Types::new();
        let int = t.int();
        let list_int = t.list(int);
        let payload = t.tuple(&[list_int, int]);
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_ground = t.tuple(&[cont, payload]);
        let halt_ground = t.tuple(&[halt, payload]);
        let observed = t.union(cont_ground, halt_ground);
        let c = t.param_alpha(2);
        let halt_var = t.tuple(&[halt, c]);
        let surface = t.union(cont_ground, halt_var);
        let refined = t.intersect(observed, surface);
        assert_eq!(t.display(&refined), "{:cont, {[int], int}}");
    }

    // ---------------------------------------------------------------------
    // fz-kdt.192's own gate: a witness is the OBSERVATION.
    // ---------------------------------------------------------------------

    /// A parameter position OBSERVES its argument. `{int, a}` applied to
    /// `{int | binary, str}` is a violation — the pattern's ground `int` field
    /// does not accept `binary` — and the only thing that can see it is the
    /// argument itself. A pattern-derived witness narrows the observation to
    /// the pattern's own ground content first (`{int, binary}`) and then
    /// compares THAT against the instantiated pattern (`{int, binary}`), so
    /// the check passes vacuously and the call is wrongly accepted.
    #[test]
    fn a_ground_pattern_field_does_not_narrow_away_the_argument_it_rejects() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let mixed = t.union(int, str_t);
        let pat = t.tuple(&[int, a]);
        let arg = t.tuple(&[mixed, str_t]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Invalid");
    }

    /// The same erasure through a list element rather than a tuple field.
    #[test]
    fn a_ground_pattern_element_does_not_narrow_away_the_argument_it_rejects() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let mixed = t.union(int, str_t);
        let pat_pair = t.tuple(&[int, a]);
        let pat = t.list(pat_pair);
        let arg_pair = t.tuple(&[mixed, str_t]);
        let arg = t.list(arg_pair);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Invalid");
    }

    // -----------------------------------------------------------------------
    // The fz-kdt.192 cold review's own constructions (X1-X8), recorded the
    // same way: each is the verdict the calculator gives an adversarial shape.
    // -----------------------------------------------------------------------

    // X1. MOVED. A ground pattern field observing a STRICT SUPERTYPE:
    // `({int, a}) :: a` at `{int | binary, int}`. The pattern-derived witness
    // reported `{int, int}` here and the gate compared it against `{int, int}`
    // and passed vacuously; the argument compares honestly and this clause
    // rejects the row. Whether the CALL is legal is a question about the
    // clause SET, one level up -- `contract_test`'s C1 is this shape at
    // `FunctionContract::apply`, and it is satisfied.
    #[test]
    fn x1_ground_field_supertype_argument() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let mixed = t.union(int, str_t);
        let pat = t.tuple(&[int, a]);
        let arg = t.tuple(&[mixed, int]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Invalid", "X1");
    }

    // X2. PRE-EXISTING, unchanged by this ticket and unfixed: a runtime FACT
    // claimed from an observation that is not ground (fz-kdt.197).
    // A union-of-arrows argument one of whose members
    // still carries a FREE variable. The ground members ground the pattern's
    // variables; the var-carrying member contributes nothing and is not
    // reported. The verdict is Known -- a runtime FACT claimed from an
    // observation that is not ground.
    #[test]
    fn x2_var_carrying_union_member_is_ignored_and_the_verdict_is_known() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let free = t.type_var(TypeVarId(999));
        let ground_clause = t.arrow(&[int], int);
        let free_clause = t.arrow(&[free], free);
        let arg = t.union(ground_clause, free_clause);
        let pat = t.arrow(&[a], b);
        assert!(t.has_vars(&arg), "the argument is NOT ground");
        let v = t.match_arrow(&[pat], &b, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Known params=[(int) -> int] result=int", "X2");
    }

    // X2B. The same shape one level up: the argument's free member has a
    // DIFFERENT domain from the ground member, so the answer the calculator
    // grounds depends on which member it decided to read.
    #[test]
    fn x2b_var_carrying_union_member_with_a_wider_domain() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let free = t.type_var(TypeVarId(999));
        let widened = t.union(free, str_t);
        let ground_clause = t.arrow(&[int], int);
        let free_clause = t.arrow(&[widened], widened);
        let arg = t.union(ground_clause, free_clause);
        let pat = t.arrow(&[a], b);
        let v = t.match_arrow(&[pat], &b, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Known params=[(int) -> int] result=int", "X2B");
    }

    // X3. An uninhabited argument at a POLYMORPHIC pattern: `none` is a row
    // no call can supply, so no clause applies. Whether the CALL is legal is
    // the clause set's question -- C3 says it is.
    #[test]
    fn x3_none_argument_at_a_polymorphic_pattern() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let none = t.none();
        let v = t.match_arrow(&[list_a], &a, &no_bounds(), &[none]);
        assert_eq!(render(&t, &v), "Invalid", "X3");
    }

    // X3B. An uninhabited argument in ONE position of a multi-argument row
    // whose other positions are perfectly good.
    #[test]
    fn x3b_none_in_one_position_invalidates_the_whole_row() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let none = t.none();
        let v = t.match_arrow(&[a, b], &a, &no_bounds(), &[int, none]);
        assert_eq!(render(&t, &v), "Invalid", "X3B");
    }

    // X4. Behavior 5 of this module -- "a variable pinned only by [] is noise
    // and is dropped" -- through a MIXED-ARITY tuple union, where the cleaner
    // once went blind. Projecting both sides onto the pattern's widest arity
    // found the witness narrower and walked away, so `a` kept the `[]` the
    // collector pinned and the verdict claimed as a runtime FACT that the
    // result is the empty list. The cleaner now descends the alternatives the
    // way the collector does, so this agrees with X4B.
    #[test]
    fn x4_mixed_arity_tuple_union_drops_the_empty_list_binding() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let done = t.atom_lit("done");
        let halted = t.atom_lit("halted");
        let suspended = t.atom_lit("suspended");
        let any = t.any();
        let continuation = t.arrow(&[], any);
        let done_pat = t.tuple(&[done, a]);
        let halted_pat = t.tuple(&[halted, a]);
        let suspended_pat = t.tuple(&[suspended, a, continuation]);
        let pat = t.union(done_pat, halted_pat);
        let pat = t.union(pat, suspended_pat);
        let empty = t.empty_list();
        let arg = t.tuple(&[done, empty]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[{:done, a0} | {:halted, a0} | {:suspended, a0, () -> any}] result=a0",
            "X4"
        );
    }

    // X4B. The SAME question with a SAME-arity tuple union, which the arity
    // projection could always descend: X4's control. The two must agree.
    #[test]
    fn x4b_same_arity_tuple_union_drops_the_empty_list_binding() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let done = t.atom_lit("done");
        let halted = t.atom_lit("halted");
        let done_pat = t.tuple(&[done, a]);
        let halted_pat = t.tuple(&[halted, a]);
        let pat = t.union(done_pat, halted_pat);
        let empty = t.empty_list();
        let arg = t.tuple(&[done, empty]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[{:done, a0} | {:halted, a0}] result=a0",
            "X4B"
        );
    }

    // X5. A BRANDED argument at a ground pattern field is ACCEPTED, and that
    // is the refinement law reaching the structural gate.
    // `.agent/docs/set-theoretic-types.md` ("Brands carry their inner"):
    // a brand narrows the `brands` slot of its inner and nothing else, so
    // `Meters(int) <: int` while `int` is NOT a `Meters(int)`. A witness that
    // is the ARGUMENT is what puts that law under the gate: the gate asks
    // `arg <: sigma(P)` with the argument the call really supplied, and a
    // refinement passes a position declared at its inner. The reported
    // parameter surface is the pattern the clause declares, `{int, binary}` --
    // the clause promises no more than `int` at that field, and the caller's
    // narrower `Meters(int)` is not published back as the clause's domain.
    // Compare X5B, the other direction.
    #[test]
    fn x5_branded_argument_at_a_ground_pattern_field() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let branded = t.mint_brand(int, "Meters");
        assert_eq!(t.display(&branded), "Meters(int)", "a brand refines its inner");
        assert!(t.is_subtype(&branded, &int), "a branded int IS a subtype of int");
        assert!(!t.is_subtype(&int, &branded), "a bare int is NOT a branded int");
        let pat = t.tuple(&[int, a]);
        let arg = t.tuple(&[branded, str_t]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(
            render(&t, &v),
            "Known params=[{int, binary}] result=binary",
            "X5 branded argument at a ground int field"
        );
    }

    // X5B. The other direction: a BARE int at a `Meters(int)` pattern field is
    // REJECTED. Nothing about a plain `int` says which brand it carries, so it
    // cannot satisfy a position that demands one -- `binary` accepts a `utf8`,
    // `utf8` rejects a bare `binary`, and this is that law one structure down.
    //
    // This is the gate seeing the call for the first time. A pattern-derived
    // witness restated the ground field as the PATTERN, so the gate compared
    // `{Meters(int), binary}` with itself and answered `Known` -- it never
    // examined the `int` the caller supplied. The witness is the argument now,
    // so the mismatch is reachable and the row is Invalid.
    #[test]
    fn x5b_bare_argument_at_a_branded_pattern_field() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let branded = t.mint_brand(int, "Meters");
        let pat = t.tuple(&[branded, a]);
        let arg = t.tuple(&[int, str_t]);
        let v = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &v), "Invalid", "X5B");
    }

    // X6. R20's shape stripped bare, and the same precision loss: ONE TUPLE
    // PARAMETER carrying the same variable twice, one field observing `[]`
    // and the other `[int]`. Compare X6B.
    #[test]
    fn x6_one_tuple_parameter_two_fields() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let empty = t.empty_list();
        let pat = t.tuple(&[list_a, list_a]);
        let arg = t.tuple(&[empty, list_int]);
        let v = t.match_arrow(&[pat], &pat, &no_bounds(), &[arg]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[{[a0], [a0]}] result={[a0], [a0]}",
            "X6 one tuple parameter"
        );
    }

    // X6B. TWO PARAMETERS carrying the same variable, same observations. The
    // scope of the empty-list veto is the PARAMETER, so this answers Known
    // while X6 answers Underconstrained -- the same constraint, two shapes,
    // two answers.
    #[test]
    fn x6b_two_parameters_same_constraint() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let empty = t.empty_list();
        let v = t.match_arrow(&[list_a, list_a], &list_a, &no_bounds(), &[empty, list_int]);
        assert_eq!(
            render(&t, &v),
            "Known params=[[int], [int]] result=[int]",
            "X6B two parameters"
        );
    }

    // X7. The cleaner reads `[]` through a NESTED list. `[[a]]` at `[[]]`:
    // one `[]` one level down.
    #[test]
    fn x7_empty_list_one_level_down() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let list_list_a = t.list(list_a);
        let empty = t.empty_list();
        let list_empty = t.list(empty);
        let v = t.match_arrow(&[list_list_a], &list_a, &no_bounds(), &[list_empty]);
        assert_eq!(render(&t, &v), "Underconstrained params=[[[a0]]] result=[a0]", "X7");
    }

    // X8. A map field observing a strict supertype under a ground sibling
    // key -- the map form of X1.
    #[test]
    fn x8_map_ground_field_supertype_argument() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let mixed = t.union(int, str_t);
        let k = MapKey::Atom("k".to_string());
        let v_key = MapKey::Atom("v".to_string());
        let pat = t.map(&[(k.clone(), int), (v_key.clone(), a)]);
        let arg = t.map(&[(k, mixed), (v_key, int)]);
        let verdict = t.match_arrow(&[pat], &a, &no_bounds(), &[arg]);
        assert_eq!(render(&t, &verdict), "Invalid", "X8");
    }
}
