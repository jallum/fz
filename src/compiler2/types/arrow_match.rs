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
//! `contract.rs`. Six behaviors the boolean subsumption surface
//! (`key_subsumes_with`) cannot express live here: the Known/Underconstrained/
//! Invalid trichotomy; union-on-rebind when one variable binds several
//! witnesses; structural-mismatch -> Invalid for arrow arity; the same for
//! map-key presence and tuple arity; the POLARITY of a variable's occurrences;
//! and whether the JOIN behind a variable's lower bound is FINISHED.
//!
//! A PARTIAL JOIN IS NOT A FACT (fz-kdt.210). A variable's lower bound is the
//! JOIN of its covariant occurrences, and a join needs every term. Where the
//! walk reaches a NODE it cannot read — every collector answers
//! `MatchWitness::Unknown`, because the witness carries variables or names no
//! structure of the pattern's kind — the terms the covariant variables beneath
//! that node were owed are UNKNOWN, not `none`. What `Sigma` then holds for
//! such a variable is a partial join: still a sound LOWER bound, and the
//! PARAMETER surface may keep refining from it, but not the solution. `Known`
//! claims a runtime FACT, so a result naming such a variable answers
//! `Underconstrained` instead.
//!
//! `reduce_cont([a], b | c, (a, b | c) -> {:cont, b | c} | ..) :: {:done, b |
//! c} | ..` folding `[int]` from a `[]` seed at an opaque reducer is the shape:
//! `b | c` occurs covariantly twice — at the SEED, and inside the reducer
//! arrow's RESULT, which is the occurrence that says what the accumulator
//! BECOMES — and only the seed is readable, so `{:done, []}` would claim the
//! fold returns what it started with.
//!
//! The rule reads the merged outcome of a NODE, and that is precisely what it
//! delivers: a `Known` verdict means no node the walk visited was wholly
//! unreadable — NOT that every covariant occurrence was individually read. Two
//! collectors skip a single unread occurrence while a sibling keeps the node's
//! merged outcome `Known`, so the marking site never fires: `collect_map_match`
//! skips a pattern key the witness does not name, and `collect_arrow_match`
//! skips a pattern clause no witness clause matches on arity. Both are pinned
//! KNOWN-WRONG below (`p5_*`, `p10_*`) and neither is reachable from the
//! shipped library, which declares no map-typed and no multi-clause `@spec`;
//! fz-kdt.218 owns closing them.
//!
//! The coarseness runs the other way too: an unreadable node marks every
//! covariant variable beneath it, including one another position already
//! determined (pinned as `an_uninhabited_arrow_clause_still_marks`). That costs
//! precision, never soundness, and it is measured free — see
//! [`Types::result_variables_are_determined`].
//!
//! A variable the walk observed NOWHERE is a different case and stays a fact:
//! it never enters `Sigma`, `close_bounds` fills it from its DECLARED bound,
//! and a declaration is not a partial observation. `@spec f(integer) :: a when
//! a: binary` is `Known binary`.
//!
//! One interaction to hold in view. `FunctionContract::apply` unions the
//! results of a contract's `Known` clauses and drops an `Underconstrained`
//! clause's, so a clause moving `Known -> Underconstrained` REMOVES a term from
//! a multi-clause contract's published result, which `refine_call_return` then
//! meets into the observed return. That is fz-kdt.190's half-(a) mechanism; on
//! the corpus it does not fire — no contract loses a term and no new narrowing
//! of a published return appears anywhere.
//!
//! POLARITY (fz-kdt.184). Passing argument `W` where pattern `P` is declared
//! asserts `W ⊆ σ(P)`. Covariant slots (list element, tuple field, map field,
//! resource payload, arrow RESULT) preserve that direction and give a variable
//! a LOWER bound, joined across occurrences; an arrow's PARAMETERS reverse it —
//! `(w) -> r ⊆ (σp) -> σr` needs `σp ⊆ w` — and give an UPPER bound, met across
//! occurrences. `collect_arrow_match` is the one reversing node in the collector
//! walk (and `collect_subst_into` in the unifier walk it delegates to). The
//! INSTANTIATION is the join of the lower bounds and nothing else: an upper
//! bound is not evidence about any value, so it never grounds the result, the
//! parameters, or a variable. The meet of the uppers is the solvability CHECK —
//! `join(lowers) ⊆ meet(uppers)` is a NECESSARY condition (over the variables
//! both bounds reached, over observed lowers, before `close_bounds`) for some
//! instantiation to exist; a lower bound outside its meet is `Invalid`. A
//! variable with ONLY upper bounds has no lower bound to publish and stays FREE,
//! so its verdict is `Underconstrained` — this is an OBSERVABLE regression from
//! the old polluted union on the `f((a) -> nil) :: [a]` shape (R6, R14), traded
//! for soundness on the contravariant-result shape (A4) and precision on the
//! `filter`/`reject`/`take_while` shape (A13), where an `any`-typed predicate
//! parameter no longer widens the element type. A var-carrying argument does not
//! arm the check: its evidence is still in flight and an upper bound read from
//! it could ratchet the meet down to a false `Invalid` a later revision revokes.
//!
//! This fix is LATENT on the shipped corpus — it moves no compiled program —
//! because the frontend demand-narrows a callback's parameter type to the
//! covariant element type at the callsite before the calculator ever sees it: a
//! predicate declared `(integer | binary) -> :ok` handed to `filter([1, 2, 3],
//! &pred/1)` arrives as the activation `filter/2[[int], (int) -> bool]`, never
//! wider than the element, so the old polluting union `elem ∪ elem = elem` was
//! idempotent and the contravariant occurrence never saw anything the covariant
//! one did not. The defect is therefore real at the CALCULATOR layer (proven
//! live by the A4/A5 pins, which construct the wider shape directly) but not
//! currently reachable from source — the fz-kdt.143 category of a
//! correct-by-construction fix on a shared surface the present frontend does not
//! drive into the buggy region. This is why the corpus shows zero movers; it is
//! not dead code.
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
//! `[]` NEEDS NO SPECIAL CASE, and the fz-f98.16 cleaner that gave it one is
//! gone (fz-kdt.120). That cleaner dropped, per position, every variable the
//! position had bound through an exact `[]` witness, reasoning that `[]` is a
//! member of every list type so a binding it pins is noise. The lattice already
//! says that, and says it better. Through a LIST PATTERN, `[]`'s element reads
//! as `none`, so `[a]` at `[]` binds `a = none` — the BOTTOM lower bound, true
//! (`[none]` is the empty list) and absorbed by the join the instant any other
//! occurrence contributes: `([a], [a])` at `([int], [])` is `[int]` because
//! `join(int, none) = int`, not because anything was vetoed. What the veto
//! actually reached was the other shape, where a variable IS the argument.
//! `f(a) :: a` at `[]` observes the whole empty list, and the whole argument is
//! a fact about the call, so `dbg([])` is `[]` and not `any`. The two shapes
//! are pinned side by side (`empty_list_binding_is_a_fact`,
//! `an_empty_list_pins_the_bottom_element_through_a_list_pattern`).
//!
//! The veto lasted because it also hid the partial join above: an `{:done, []}`
//! rung binds a fold's accumulator variable to the seed's own type, and
//! dropping the binding suppressed the claim without naming why it was wrong.
//! The partial-join rule marks that rung — and every occurrence the walk cannot
//! read, not only the `[]`-shaped one — so nothing is left for a witness-shaped
//! veto to do.

use std::collections::{HashMap, HashSet};

use super::descr::Descr;
use super::{BindingSide, Sigma, Ty, TypeVarId, Types};

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

/// The two-sided solution of the constraint `witness ⊆ σ(pattern)`.
///
/// A covariant occurrence of a variable gives it a LOWER bound (joined across
/// occurrences); an occurrence under an arrow's parameter reverses polarity and
/// gives it an UPPER bound (met across occurrences). Only the lowers
/// instantiate -- an upper bound is not evidence about a value. The meet of the
/// uppers is the solvability CHECK: `join(lowers) ⊆ meet(uppers)` is a
/// necessary condition for a solution to exist (fz-kdt.184).
#[derive(Clone, Debug, Default)]
struct MatchBounds {
    lower: Sigma<Ty>,
    upper: Sigma<Ty>,
    /// The variables whose lower bound this walk could not finish reading.
    ///
    /// A lower bound is the JOIN of a variable's covariant occurrences, and a
    /// join needs every term. Where the walk reaches a covariant occurrence it
    /// cannot observe -- the witness carries variables, or names no structure
    /// of the pattern's kind -- that term is UNKNOWN, not `none`. The join of
    /// an unknown is unknown, so what `lower` holds for such a variable is a
    /// PARTIAL join: sound as a lower bound, but not the solution
    /// (fz-kdt.210).
    undetermined: HashSet<TypeVarId>,
}

impl MatchBounds {
    fn is_empty(&self) -> bool {
        self.lower.is_empty() && self.upper.is_empty()
    }
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
        let mut solution = MatchBounds::default();
        for (pattern, witness) in params.iter().zip(args.iter()) {
            // An uninhabited argument is a position no call can supply, so the
            // signature does not apply to this row. Ground disjointness is the
            // structural gate's job, below.
            if self.is_empty(witness) {
                return ArrowMatch::Invalid;
            }
            let mut position = MatchBounds::default();
            if self.collect_match_subst(pattern, witness, BindingSide::Lower, &mut position) == MatchWitness::Invalid {
                return ArrowMatch::Invalid;
            }
            solution.undetermined.extend(position.undetermined);
            self.merge_subst_union(&mut solution.lower, position.lower);
            // A var-carrying argument's evidence is still in flight: an upper
            // bound read from it could ratchet the meet down to a false
            // Invalid the next revision revokes. Only a ground argument's upper
            // bounds arm the solvability check (fz-kdt.184).
            if !self.has_vars(witness) {
                self.merge_subst_meet(&mut solution.upper, position.upper);
            }
        }
        let sigma = solution.lower;

        // The solvability CHECK. `join(lowers) ⊆ meet(uppers)` is a necessary
        // condition for some instantiation `A` with `lower ⊆ A ⊆ upper` to
        // exist: folding `[int]` with a `(binary, int) -> int` reducer puts
        // `int` in and passes a callee that only accepts `binary`, so no `A`
        // fits and the row is Invalid. Only variables both bounds reached, over
        // OBSERVED lowers, are checked here; a declared bound is a separate
        // obligation, settled below against the same sigma (fz-kdt.184).
        let mut checked_vars = solution.upper.keys().copied().collect::<Vec<_>>();
        checked_vars.sort();
        for var in checked_vars {
            let Some(lower) = sigma.get(&var).copied() else {
                continue;
            };
            let upper = solution.upper[&var];
            if !self.is_subtype(&lower, &upper) {
                return ArrowMatch::Invalid;
            }
        }

        let closed = self.close_bounds(bounds, &sigma);
        let mut bound_vars = bounds.keys().copied().collect::<Vec<_>>();
        bound_vars.sort();
        for var in bound_vars {
            let Some(actual) = sigma.get(&var) else {
                if closed.contains_key(&var) {
                    continue;
                }
                let (params, result) = self.instantiated_clause(params, result, &sigma);
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

        let result_is_a_fact = self.result_variables_are_determined(result, &sigma, &solution.undetermined);
        let (params, result) = self.instantiated_clause(params, result, &closed);
        if params.iter().any(|param| self.has_vars(param)) || self.has_vars(&result) || !result_is_a_fact {
            ArrowMatch::Underconstrained { params, result }
        } else {
            ArrowMatch::Known { params, result }
        }
    }

    /// Whether the RESULT this match instantiates is a fact about the call.
    ///
    /// `Known` claims a runtime fact. The result may only claim one when every
    /// variable it names was SOLVED -- when the join that produced its lower
    /// bound had every term. A variable the walk observed nowhere is not in
    /// `sigma` at all; `close_bounds` fills it from its DECLARED bound, and a
    /// declaration is a fact the call cannot contradict. A variable the walk
    /// observed at some occurrences and could not read at others is in
    /// `sigma` holding a partial join -- a lower bound, not the solution --
    /// and a result built from it is a guess. The `reduce_cont([a], b | c,
    /// (a, b | c) -> ..) :: {:done, b | c} | ..` fold seeded `[]` at an opaque
    /// reducer is exactly that: `b | c` is read from the SEED alone, the
    /// reducer's arrow result -- the occurrence that says what the accumulator
    /// becomes -- is never read, and `{:done, []}` claims the walk finished a
    /// list that has not been walked (fz-kdt.210).
    ///
    /// The marking behind `undetermined` is per-NODE, so it is coarse: an
    /// unreadable node names every covariant variable beneath it, including
    /// one another position already determined. Keep it that way. Measured
    /// over the 605-fixture corpus at fz-kdt.210, the coarseness costs 1189
    /// `Known` verdicts, and at the consumer that reads them
    /// (`refine_call_return`) 447 become ABSENT and 817 become NOOP: they were
    /// doing nothing. The 4 that were doing something were the 4 that narrowed
    /// a published return to its seed's own type -- this defect. Per-occurrence
    /// marking would buy back verdicts that reach no artifact.
    fn result_variables_are_determined(
        &mut self,
        result: &Ty,
        sigma: &Sigma<Ty>,
        undetermined: &HashSet<TypeVarId>,
    ) -> bool {
        if undetermined.is_empty() {
            return true;
        }
        self.free_var_ids(result)
            .iter()
            .all(|var| !undetermined.contains(var) || !sigma.contains_key(var))
    }

    fn instantiated_clause(&mut self, params: &[Ty], result: &Ty, sigma: &Sigma<Ty>) -> (Vec<Ty>, Ty) {
        let params = params.iter().map(|param| self.instantiate(param, sigma)).collect();
        let result = self.instantiate(result, sigma);
        (params, result)
    }

    /// Collect the bindings the constraint at `side` licenses, and decide the
    /// per-position witness outcome. `side` is the direction of the subtyping
    /// constraint at THIS node (see [`BindingSide`]): every kind but the arrow
    /// is covariant and passes it straight down; only `collect_arrow_match`
    /// reverses it, and only for the arrow's parameters (fz-kdt.184).
    fn collect_match_subst(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
        let outcome = MatchWitness::Unknown
            .merge(self.collect_var_match(pattern, witness, side, bounds))
            .merge(self.collect_tuple_match(pattern, witness, side, bounds))
            .merge(self.collect_list_match(pattern, witness, side, bounds))
            .merge(self.collect_resource_match(pattern, witness, side, bounds))
            .merge(self.collect_map_match(pattern, witness, side, bounds))
            .merge(self.collect_arrow_match(pattern, witness, side, bounds));
        if outcome == MatchWitness::Unknown && self.has_vars(pattern) {
            // No collector read this node. Every variable that occurs
            // covariantly beneath it was owed a term of its join and did not
            // get one, so its lower bound is partial from here on
            // (fz-kdt.210).
            //
            // This is the ONE marking site, and it reads the node's MERGED
            // outcome. A collector that skips a single occurrence while a
            // sibling reads another leaves the node `Known` and marks nothing
            // -- see the `p5_`/`p10_` known-wrong pins for the two that do.
            let mut seen = HashSet::new();
            self.collect_lower_occurrences(pattern, side, &mut seen, &mut bounds.undetermined);
        }
        outcome
    }

    /// The variables a subtree would give a LOWER bound to, had the walk been
    /// able to read it. Mirrors the collectors exactly -- every kind descends
    /// at the same side and only an arrow's parameters flip -- so a variable
    /// bounded only from above is never named here (fz-kdt.184).
    ///
    /// `Unify` contributes like `Lower`, because `Unify` means the two sides
    /// describe the same thing and every position binds. The memo is keyed on
    /// the whole [`BindingSide`] for the same reason: the three sides give
    /// three different answers, so collapsing any two of them into one slot
    /// would return the wrong one.
    fn collect_lower_occurrences(
        &mut self,
        pattern: &Ty,
        side: BindingSide,
        seen: &mut HashSet<(Ty, BindingSide)>,
        out: &mut HashSet<TypeVarId>,
    ) {
        if !self.has_vars(pattern) || !seen.insert((*pattern, side)) {
            return;
        }
        if side == BindingSide::Lower || side == BindingSide::Unify {
            out.extend(self.descr(pattern).clone().vars.values.iter().copied());
        }
        let arity = self.max_tuple_arity(pattern);
        for field in self.tuple_projections(pattern, arity) {
            self.collect_lower_occurrences(&field, side, seen, out);
        }
        if self.has_list_shape(pattern) {
            let elem = self.list_element_type(pattern);
            self.collect_lower_occurrences(&elem, side, seen, out);
        }
        if let Some(payload) = self.resource_payload_type(pattern) {
            self.collect_lower_occurrences(&payload, side, seen, out);
        }
        for key in self.map_known_keys(pattern) {
            if let Some(field) = self.map_field_lookup(pattern, &key) {
                self.collect_lower_occurrences(&field, side, seen, out);
            }
        }
        if let Some(clauses) = self.callable_clauses(pattern) {
            for clause in clauses {
                for arg in &clause.args {
                    self.collect_lower_occurrences(arg, side.flipped(), seen, out);
                }
                self.collect_lower_occurrences(&clause.ret, side, seen, out);
            }
        }
    }

    fn collect_var_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
        if !self.has_vars(pattern) || self.has_vars(witness) {
            return MatchWitness::Unknown;
        }
        let mut direct = MatchBounds::default();
        self.collect_constraint_subst(pattern, witness, side, BindingSide::Lower, &mut direct.lower);
        self.collect_constraint_subst(pattern, witness, side, BindingSide::Upper, &mut direct.upper);
        if direct.is_empty() {
            return MatchWitness::Unknown;
        }
        self.merge_subst_union(&mut bounds.lower, direct.lower);
        self.merge_subst_meet(&mut bounds.upper, direct.upper);
        MatchWitness::Known
    }

    fn collect_tuple_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
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
        if let Some(outcome) = self.collect_correlated_tuple_match(pattern, witness, side, bounds) {
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
            outcome = outcome.merge(self.collect_match_subst(pattern_field, witness_field, side, bounds));
        }
        outcome
    }

    fn collect_correlated_tuple_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
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
                let mut pair_bounds = MatchBounds::default();
                let mut pair_outcome = MatchWitness::Unknown;
                for (pattern_field, witness_field) in pattern_fields.iter().zip(witness_fields.iter()) {
                    pair_outcome = pair_outcome.merge(self.collect_match_subst(
                        pattern_field,
                        witness_field,
                        side,
                        &mut pair_bounds,
                    ));
                }
                if pair_outcome == MatchWitness::Invalid {
                    continue;
                }
                self.merge_subst_union(&mut bounds.lower, pair_bounds.lower);
                self.merge_subst_meet(&mut bounds.upper, pair_bounds.upper);
                bounds.undetermined.extend(pair_bounds.undetermined);
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

    fn collect_list_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
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
        self.collect_match_subst(&pattern_elem, &witness_elem, side, bounds)
    }

    fn collect_resource_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
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
        self.collect_match_subst(&pattern_payload, &witness_payload, side, bounds)
    }

    fn collect_map_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
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
                outcome = outcome.merge(self.collect_match_subst(&pattern_field, &witness_field, side, bounds));
            }
        }
        outcome
    }

    /// The ONE reversing node in the collector walk. `witness ⊆ σ(pattern)` for
    /// two arrows needs `σ(pattern_arg) ⊆ witness_arg` (contravariance) and
    /// `witness_ret ⊆ σ(pattern_ret)` (covariance), so the parameters descend
    /// at the FLIPPED side and the result at the enclosing one. A variable
    /// reached through an odd number of parameter descents is bounded from
    /// ABOVE and contributes no lower bound; two descents restore it
    /// (fz-kdt.184).
    fn collect_arrow_match(
        &mut self,
        pattern: &Ty,
        witness: &Ty,
        side: BindingSide,
        bounds: &mut MatchBounds,
    ) -> MatchWitness {
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
                    outcome = outcome.merge(self.collect_match_subst(pattern_arg, witness_arg, side.flipped(), bounds));
                }
                outcome =
                    outcome.merge(self.collect_match_subst(&pattern_clause.ret, &witness_clause.ret, side, bounds));
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

    /// Meet a directly-collected UPPER bound into the running one: a variable
    /// bounded from above by two positions is bounded by their intersection --
    /// a callee that must accept both an `(int) -> nil` and a `(binary) -> nil`
    /// caller can only be handed values both accept (fz-kdt.184).
    fn merge_subst_meet(&mut self, sigma: &mut Sigma<Ty>, direct: Sigma<Ty>) {
        for (var, witness) in direct {
            match sigma.remove(&var) {
                Some(existing) => {
                    let met = self.intersect(existing, witness);
                    sigma.insert(var, met);
                }
                None => {
                    sigma.insert(var, witness);
                }
            }
        }
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
#[path = "arrow_match_test.rs"]
mod arrow_match_test;
