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

    // A variable that IS the argument is bound to the argument, and `[]` is no
    // exception. `f(a) :: a` at `[]` -- the shape of `dbg([])` -- observes the
    // whole empty list at a bare variable, so `a = []` is a fact about the
    // call and the result is `[]`, not `any` and not free.
    //
    // The retired fz-f98.16 cleaner dropped exactly this binding, reasoning
    // that `[]` is a member of every list type so a binding it pins is noise.
    // The reasoning describes a DIFFERENT shape -- `[a]` observing `[]`, where
    // the collectors bind nothing at all because `[]` has no element (see
    // `an_empty_list_pins_nothing_through_a_list_pattern`) -- and there the
    // cleaner had nothing to drop. Its only reach was here, where the binding
    // is evidence (fz-kdt.120).
    #[test]
    fn empty_list_binding_is_a_fact() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let empty = t.empty_list();
        match t.match_arrow(&[a], &a, &no_bounds(), &[empty]) {
            ArrowMatch::Known { result, .. } => {
                assert!(
                    t.is_equivalent(&result, &empty),
                    "a bare variable observing `[]` is bound to `[]`"
                );
            }
            other => panic!("expected Known [] for an empty-list binding, got {other:?}"),
        }
    }

    // The other half of the same fact, and the reason no cleaner was ever
    // needed for it: through a LIST PATTERN, `[]` pins the BOTTOM of the
    // lower-bound lattice. `[]`'s element reads as `none`, so `[a]` at `[]`
    // binds `a = none` -- the least solution, and a true one: `[none]` IS the
    // empty list. A bottom lower bound is absorbed the instant any other
    // occurrence contributes, which is why `([a], [a])` at `([int], [])`
    // answers `[int]` with no veto in sight (the sibling pin below).
    #[test]
    fn an_empty_list_pins_the_bottom_element_through_a_list_pattern() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let empty = t.empty_list();
        match t.match_arrow(&[list_a], &a, &no_bounds(), &[empty]) {
            ArrowMatch::Known { params, result } => {
                assert!(t.is_empty(&result), "`[]`'s element is the bottom lower bound");
                assert!(
                    t.is_equivalent(&params[0], &empty),
                    "and instantiating `[a]` with it gives back the empty list"
                );
            }
            other => panic!("expected Known none for `[a]` at `[]`, got {other:?}"),
        }
    }

    // fz-f98.16's own shape, and the JOIN is what answers it.
    // `List.reverse/2` is spec'd `([a], [a]) :: [a]`, so
    // `List.reverse([1, 2, 3], [])` bounds `a` from below at `int` from the
    // first parameter and at `none` from the second, and `join(int, none)` is
    // `int`. The empty-list position must not throw away what the other
    // position proved: when the fz-f98.16 cleaner vetoed `a` for the whole
    // position, `[a]` collapsed to `[]` and the caller's good `[int]` argument
    // was narrowed to the empty list.
    #[test]
    fn a_bottom_bound_from_an_empty_list_is_absorbed_by_the_join() {
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
            "Known params=[[int], (int) -> none] result=[none]",
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
            "Known params=[[int], (%{:k: int}) -> :nil] result=[int]",
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
            "Known params=[[int], (resource(int)) -> :nil] result=[int]",
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
            "Underconstrained params=[(((a0) -> :nil) -> :nil) -> :nil] result=[a0]",
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
            "Known params=[int, ({int, int}) -> :nil] result=({int, int}) -> :nil",
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
            "Known params=[[int], (int) -> :nil] result=[int]",
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
            "Underconstrained params=[(a0) -> :nil] result=[a0]",
            "R14 only-upper (any)"
        );
        let v2 = t.match_arrow(&[pat_fn], &list_a, &no_bounds(), &[int_fn]);
        assert_eq!(
            render(&t, &v2),
            "Underconstrained params=[(a0) -> :nil] result=[a0]",
            "R14 only-upper (int)"
        );
    }

    // R15. An `[]` witness UNDER an arrow parameter, where the polarity flip
    // makes it an UPPER bound. `f([a], (a) -> nil) :: [a]` at
    // `([int], ([]) -> nil)`.
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
        // And the shape where the `[]` is the parameter itself:
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
            "Known params=[int, (int) -> :nil] result={int, (int) -> :nil}",
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

    // R18. `[]` observed at a CONTRAVARIANT position, where it bounds from
    // ABOVE. `f([a], ([a]) -> nil) :: [a]` at `([int], ([]) -> nil)` reads
    // `a >= int` from the list and `a <= none` from the callable the caller
    // supplied, no `a` satisfies both, and the row is `Invalid`. R19 is the
    // same law one level up and R20 the same law with a tuple around it.
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

    // R20. One TUPLE parameter carrying both a lower-bound list and a `[]`
    // under an arrow's PARAMETER, which is the solvability check's own shape.
    // The first field gives `a >= int`; the second reverses polarity, so
    // `([a]) -> :nil` accepting a `([]) -> :nil` needs `[a] <: []`, i.e.
    // `a <= none`. `int` is not a subtype of `none`, no `a` satisfies both,
    // and the row is `Invalid` -- consistent with R18 and R19, which state
    // the same law without a tuple around it.
    //
    // The veto had MASKED it: it dropped the position's lower binding
    // whenever an exact `[]` appeared anywhere inside, so `a` had no lower
    // bound left for the check to compare and the contradiction went
    // unreported (fz-kdt.120).
    #[test]
    fn r20_a_contravariant_empty_list_contradicts_a_covariant_lower_bound() {
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
            "Invalid",
            "R20 contravariant [] against a covariant lower bound"
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
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[(a0) -> :nil] result=[a0]",
            "A2"
        );
    }

    // A3. The reducer shape: `reduce([a], b, (a, b) -> b) :: b` at
    // `([int], [], (any, [int]) -> [int])`.
    //
    // `b` has TWO readable covariant occurrences here -- the seed `[]` and the
    // GROUND reducer's result `[int]` -- so the join is complete and the answer
    // is `[] | [int]`. That is the same SET as `[int]` (`[] <: [int]`), and the
    // pin asserts so; the union interns as a distinct `Ty` only because
    // `Types::union` does not absorb a subsumed member, which is fz-kdt.182 and
    // predates this. Before fz-kdt.120 the veto dropped `b`'s `[]` occurrence
    // and the join read `[int]` alone, which is why the literal moves.
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
            "Known params=[[int], [] | [int], (int, [] | [int]) -> [] | [int]] result=[] | [int]",
            "A3"
        );
        let ArrowMatch::Known { result, .. } = &v else {
            unreachable!("A3 answers Known");
        };
        assert!(
            t.is_equivalent(result, &list_int),
            "the joined result is the SAME SET as [int]; only the interning differs (fz-kdt.182)"
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
            "Known params=[int, (int) -> :nil] result=(int) -> :nil",
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
        assert_eq!(
            render(&t, &verdict),
            "Known params=[int, (int) -> :nil] result=int",
            "A5"
        );
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

    // A7. `f(a, a) :: a` at `(int, <unanalyzed arrow>)`. `a` is owed two terms
    // of its join and gets one: the second position's witness carries
    // variables, so what `a` becomes there is unread. `int` is a sound LOWER
    // bound and the parameter surface keeps it, but the result cannot claim
    // the call returns an `int` when the unread term may be an arrow
    // (fz-kdt.210).
    #[test]
    fn a7_var_carrying_argument_contributes_no_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let v = t.match_arrow(&[a, a], &a, &no_bounds(), &[int, unanalyzed]);
        assert_eq!(render(&t, &v), "Underconstrained params=[int, int] result=int", "A7");
    }

    /// fz-kdt.210. The fold shape, as `List.reduce_cont/3` declares it: the
    /// accumulator variable occurs covariantly TWICE -- at the seed, and
    /// inside the reducer arrow's RESULT, which is the occurrence that says
    /// what the accumulator BECOMES. Hand the reducer over unanalyzed and only
    /// the seed is read. `{:done, seed}` would be a claim that the fold
    /// returns what it started with, so the verdict withholds the result.
    ///
    /// Structural throughout (fz-kdt.209): the verdict is matched, and the
    /// parameter surface -- which a partial lower bound is still allowed to
    /// refine -- is compared with the calculator.
    #[test]
    fn a_partially_joined_variable_does_not_make_the_result_a_fact() {
        let mut t = Types::new();
        let acc = t.param_alpha(0);
        let seed = t.atom_lit(":a");
        let done = t.atom_lit(":done");
        let reducer = t.arrow(&[acc], acc);
        let result = t.tuple(&[done, acc]);
        let opaque = unanalyzed_arrow(&mut t, 1);

        match t.match_arrow(&[acc, reducer], &result, &no_bounds(), &[seed, opaque]) {
            ArrowMatch::Underconstrained { params, .. } => {
                assert!(t.is_equivalent(&params[0], &seed), "the seed still refines the surface");
            }
            other => panic!("a partial join must withhold the result, got {}", render(&t, &other)),
        }

        // The control: an observed reducer determines the second occurrence,
        // and the result is a fact again.
        let b = t.atom_lit(":b");
        let grown = t.union(seed, b);
        let observed = t.arrow(&[grown], grown);
        match t.match_arrow(&[acc, reducer], &result, &no_bounds(), &[seed, observed]) {
            ArrowMatch::Known { result, .. } => {
                let expected_payload = t.union(seed, grown);
                let expected = t.tuple(&[done, expected_payload]);
                assert!(t.is_equivalent(&result, &expected), "a full join is a fact");
            }
            other => panic!("a determined variable is a fact, got {}", render(&t, &other)),
        }
    }

    /// fz-kdt.210. `Underconstrained` is not free, and this is the shape that
    /// pays for it. `behavior/mailbox_closure_reduce` folds a
    /// `non_empty_list(int)` from a `0` seed with a reducer that arrives from
    /// `receive` as an opaque `any`, so the accumulator's second covariant
    /// occurrence is unreadable. Before this rule the contract answered
    /// `{:done, int}` -- read from the seed and from nothing else -- and
    /// `refine_call_return` carved the observed `{:done, any}` down to it, so
    /// `Enum.reduce/3[non_empty_list(int), int, any]` published `int` with a
    /// `return_layout` of `reprs=[RawInt]`. It now publishes `any` with
    /// `reprs=[ValueRef]`. That is a real physical de-optimisation on a corpus
    /// fixture, and it is the honest answer: nothing in the call said the fold
    /// returns an `int`.
    #[test]
    fn an_opaque_fold_keeps_its_observed_return_at_the_cost_of_a_raw_lane() {
        let mut t = Types::new();
        let acc = t.param_alpha(0);
        let int = t.int();
        let done = t.atom_lit(":done");
        let reducer = t.arrow(&[acc], acc);
        let result = t.tuple(&[done, acc]);
        let opaque = unanalyzed_arrow(&mut t, 1);
        match t.match_arrow(&[acc, reducer], &result, &no_bounds(), &[int, opaque]) {
            ArrowMatch::Underconstrained { params, .. } => {
                assert!(t.is_equivalent(&params[0], &int), "the seed still refines the surface");
            }
            other => panic!(
                "a ground seed alone is not the fold's return, got {}",
                render(&t, &other)
            ),
        }
    }

    /// fz-kdt.210. Marking mirrors the collectors' POLARITY: an occurrence
    /// reached through an arrow's PARAMETERS is bounded from above and gives
    /// no term of any join, so an unreadable node never names it.
    /// `each([a], (a) -> any) :: [a]` at `([int], <opaque>)` reads `a` at
    /// parameter 0 and owes it nothing at parameter 1, and the result is a
    /// fact.
    #[test]
    fn a_contravariant_only_occurrence_is_not_marked() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let list_a = t.list(a);
        let list_int = t.list(int);
        let each = t.arrow(&[a], any);
        let opaque = unanalyzed_arrow(&mut t, 1);
        match t.match_arrow(&[list_a, each], &list_a, &no_bounds(), &[list_int, opaque]) {
            ArrowMatch::Known { result, .. } => {
                assert!(
                    t.is_equivalent(&result, &list_int),
                    "a contravariant occurrence owes no term"
                );
            }
            other => panic!(
                "a contravariant-only occurrence must not be marked, got {}",
                render(&t, &other)
            ),
        }
    }

    /// fz-kdt.210. An unreadable node marks the variables BENEATH it and no
    /// others, and the verdict then turns on what the RESULT names.
    /// `f(a, b, (b) -> b)` at `(int, binary, <opaque>)` marks `b` alone: a
    /// result naming `a` is still a fact, a result naming `b` is not.
    #[test]
    fn marking_is_scoped_to_the_unreadable_subtree() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let b = t.param_alpha(1);
        let int = t.int();
        let str_t = t.str_t();
        let arrow_b = t.arrow(&[b], b);
        let opaque = unanalyzed_arrow(&mut t, 1);
        match t.match_arrow(&[a, b, arrow_b], &a, &no_bounds(), &[int, str_t, opaque]) {
            ArrowMatch::Known { result, .. } => {
                assert!(t.is_equivalent(&result, &int), "`a` was read at its only occurrence");
            }
            other => panic!("an unmarked result variable is a fact, got {}", render(&t, &other)),
        }
        match t.match_arrow(&[a, b, arrow_b], &b, &no_bounds(), &[int, str_t, opaque]) {
            ArrowMatch::Underconstrained { .. } => {}
            other => panic!("the marked variable withholds the result, got {}", render(&t, &other)),
        }
    }

    /// fz-kdt.210, the load-bearing exception at its exact boundary. A
    /// variable the walk MARKED but never bound is not in `Sigma`, so
    /// `close_bounds` fills it from its DECLARED bound: a declaration is not a
    /// partial observation. `f(a, (any) -> a) :: a when a: binary` at two
    /// opaque arrows marks `a` at BOTH occurrences and binds it at neither.
    #[test]
    fn a_marked_variable_that_never_entered_sigma_keeps_its_declared_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let any = t.any();
        let str_t = t.str_t();
        let a_id = t.param_alpha_id(0);
        let arrow = t.arrow(&[any], a);
        let opaque1 = unanalyzed_arrow(&mut t, 1);
        let opaque2 = unanalyzed_arrow(&mut t, 1);
        let mut bounds = HashMap::new();
        bounds.insert(a_id, str_t);
        match t.match_arrow(&[a, arrow], &a, &bounds, &[opaque1, opaque2]) {
            ArrowMatch::Known { result, .. } => {
                assert!(
                    t.is_equivalent(&result, &str_t),
                    "a declared bound survives the marking"
                );
            }
            other => panic!(
                "an unobserved variable keeps its declaration, got {}",
                render(&t, &other)
            ),
        }
    }

    /// fz-kdt.210. The same exception with no argument occurrence at all:
    /// `only_bound(integer) :: a when a: binary`. `a` never enters `Sigma`, so
    /// nothing about the call can contradict the declaration.
    #[test]
    fn a_result_only_variable_with_a_declared_bound_is_a_fact() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let str_t = t.str_t();
        let a_id = t.param_alpha_id(0);
        let mut bounds = HashMap::new();
        bounds.insert(a_id, str_t);
        match t.match_arrow(&[int], &a, &bounds, &[int]) {
            ArrowMatch::Known { result, .. } => {
                assert!(t.is_equivalent(&result, &str_t), "a declared bound is a fact");
            }
            other => panic!(
                "a result-only variable is its declared bound, got {}",
                render(&t, &other)
            ),
        }
    }

    /// fz-kdt.210, the DELIBERATE coarseness. The marking site reads a node's
    /// MERGED outcome, so an unreadable node names every covariant variable
    /// beneath it -- including one another position already determined.
    /// `f(a, ((any) -> int) | ((any, any) -> a)) :: a` at `(int, (any) -> int)`
    /// has `a` fully determined at position 0, and the arity-2 clause is a
    /// branch the unary witness can never select, yet the node reads as
    /// unreadable and the result stops being a fact. Precision, never
    /// soundness; see [`Types::result_variables_are_determined`] for what the
    /// whole class costs.
    #[test]
    fn an_uninhabited_arrow_clause_still_marks() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let any = t.any();
        let unary = t.arrow(&[any], int);
        let binary_clause = t.arrow(&[any, any], a);
        let pattern = t.union(unary, binary_clause);
        let witness = t.arrow(&[any], int);
        match t.match_arrow(&[a, pattern], &a, &no_bounds(), &[int, witness]) {
            ArrowMatch::Underconstrained { .. } => {}
            other => panic!("per-node marking is coarse by construction, got {}", render(&t, &other)),
        }
    }

    /// fz-kdt.210, KNOWN-WRONG. `collect_map_match` skips a pattern key the
    /// witness does not name -- and raises no `Invalid` when the witness
    /// carries variables, precisely the case where the key might yet appear --
    /// WITHOUT recursing. A sibling key that IS read leaves the node's merged
    /// outcome `Known`, so the one marking site never fires and `a` reaches a
    /// `Known` result on a join that is missing its `:missing` term.
    ///
    /// `f(a, %{:k => c, :missing => a}) :: a` at `(int, α | %{:k => int})`
    /// answers `Known int`. It SHOULD withhold the result. The hole is latent:
    /// no `@spec` in the shipped runtime library declares a map-typed
    /// parameter, so nothing on the corpus reaches it. fz-kdt.218 owns it.
    #[test]
    fn p5_a_skipped_map_key_is_a_partial_join_the_node_rule_misses() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let c = t.param_alpha(2);
        let int = t.int();
        let pattern_map = t.map(&[
            (MapKey::Atom("k".to_string()), c),
            (MapKey::Atom("missing".to_string()), a),
        ]);
        let witness_map = t.map(&[(MapKey::Atom("k".to_string()), int)]);
        let free = t.type_var(TypeVarId(901));
        let witness = t.union(witness_map, free);
        match t.match_arrow(&[a, pattern_map], &a, &no_bounds(), &[int, witness]) {
            ArrowMatch::Known { result, .. } => {
                assert!(
                    t.is_equivalent(&result, &int),
                    "known-wrong: the `:missing` term was never read"
                );
            }
            other => panic!(
                "the known-wrong hole has closed -- re-cut this pin, got {}",
                render(&t, &other)
            ),
        }
    }

    /// fz-kdt.210, KNOWN-WRONG, the same hole in a second collector.
    /// `collect_arrow_match` skips a pattern clause no witness clause matches
    /// on arity without recursing, so that clause's covariant result variable
    /// gets no term and no mark; a sibling clause that DID match keeps the
    /// node `Known`.
    ///
    /// `f(c, ((any) -> b) | ((any, any) -> c)) :: c` at `(int, (any) -> int)`
    /// answers `Known int`. Weaker than the map case -- the skipped clause is
    /// uninhabited by this witness, so the skip is arguably principled -- and
    /// latent for the same reason: the shipped library declares no
    /// multi-clause `@spec`. fz-kdt.218 owns it.
    #[test]
    fn p10_a_skipped_arrow_clause_is_a_partial_join_the_node_rule_misses() {
        let mut t = Types::new();
        let b = t.param_alpha(1);
        let c = t.param_alpha(2);
        let int = t.int();
        let any = t.any();
        let unary = t.arrow(&[any], b);
        let binary_clause = t.arrow(&[any, any], c);
        let pattern = t.union(unary, binary_clause);
        let witness = t.arrow(&[any], int);
        match t.match_arrow(&[c, pattern], &c, &no_bounds(), &[int, witness]) {
            ArrowMatch::Known { result, .. } => {
                assert!(
                    t.is_equivalent(&result, &int),
                    "known-wrong: the arity-2 clause was never read"
                );
            }
            other => panic!(
                "the known-wrong hole has closed -- re-cut this pin, got {}",
                render(&t, &other)
            ),
        }
    }

    /// The "observed nowhere" exception means exactly that, and `[]` is an
    /// observation like any other. `each([a], (a) -> a) :: [a] when a: binary`
    /// at `([], <opaque>)` DID observe `a`: the empty list's element pins the
    /// bottom bound, so `a` is in `Sigma` at `none`. The opaque reducer's
    /// return is an occurrence the walk cannot read, so the join is partial and
    /// the verdict is `Underconstrained` -- the declared `binary` does not step
    /// in, because a declared bound answers only where the call said nothing.
    ///
    /// This pin USED to answer `Known [binary]`, and only because the
    /// fz-f98.16 veto had removed the `[]` binding from `Sigma`, routing an
    /// observed variable into the exception for unobserved ones. That is the
    /// interaction that made the veto's deletion (fz-kdt.120) wait for this
    /// rule (fz-kdt.210) rather than the other way round.
    ///
    /// The reported PARAMETER surface clamps the reducer to `(none) -> none`,
    /// which is a partial join instantiating the clause domain. That half is
    /// KNOWN-WRONG and fz-kdt.216 owns it; the RESULT half, which is what
    /// `FunctionContract::apply` publishes, is correct here.
    #[test]
    fn an_observed_empty_list_does_not_fall_back_to_a_declared_bound() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let str_t = t.str_t();
        let a_id = t.param_alpha_id(0);
        let empty = t.empty_list();
        let list_a = t.list(a);
        let list_str = t.list(str_t);
        let arrow_a = t.arrow(&[a], a);
        let opaque = unanalyzed_arrow(&mut t, 1);
        let mut bounds = HashMap::new();
        bounds.insert(a_id, str_t);
        match t.match_arrow(&[list_a, arrow_a], &list_a, &bounds, &[empty, opaque]) {
            ArrowMatch::Underconstrained { result, .. } => {
                assert!(
                    !t.is_equivalent(&result, &list_str),
                    "the declared bound must not answer for a variable the call observed"
                );
                assert!(
                    t.is_equivalent(&result, &empty),
                    "what it observed was the empty list's bottom element"
                );
            }
            other => panic!(
                "an observed `[]` still routes into the observed-nowhere exception, got {}",
                render(&t, &other)
            ),
        }
    }

    // A8. `f(a, a, a) :: a` at `(int, [], <unanalyzed arrow>)`. This was a
    // FALSE `Invalid`, and deleting the veto FIXES it: the veto dropped the
    // second position's `a = []`, leaving `a = int`, and then the structural
    // gate asked `[] <: int` about an argument the call really supplied and
    // ruled the legal row out. With both observations kept, `a` joins to
    // `int | []` and every position passes the gate. The third position is an
    // unanalyzed arrow the walk cannot read, so the join is partial and the
    // verdict is honestly `Underconstrained` (fz-kdt.210) rather than `Known`.
    #[test]
    fn a8_three_positions_one_variable() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let int = t.int();
        let empty = t.empty_list();
        let unanalyzed = unanalyzed_arrow(&mut t, 1);
        let v = t.match_arrow(&[a, a, a], &a, &no_bounds(), &[int, empty, unanalyzed]);
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[int | [], int | [], int | []] result=int | []",
            "A8"
        );
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
        assert_eq!(render(&t, &v), "Known params=[[int], (int) -> any] result=[int]", "A13");
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

    // X2. A union-of-arrows argument one of whose members still carries a FREE
    // variable. The mapper's `a` occurs ONLY under the arrow's parameter, so it
    // is an upper bound with no lower bound, and a var-carrying argument does
    // not arm the check besides -- so `a` stays free and the verdict is
    // Underconstrained. Before fz-kdt.184 the parameter observation polluted the
    // lower solution and the calculator claimed a runtime FACT (`Known`) from an
    // observation that is not ground (fz-kdt.197); the polarity split withholds
    // that fact instead. The result `b` is still read from one clause of the
    // union, but it is no longer published as Known.
    #[test]
    fn x2_var_carrying_union_member_is_ignored_and_the_verdict_is_underconstrained() {
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
        assert_eq!(render(&t, &v), "Underconstrained params=[(a0) -> int] result=int", "X2");
    }

    // X2B. The same shape one level up: the argument's free member has a
    // DIFFERENT domain from the ground member. `a` is still only an upper bound
    // from a var-carrying argument, so the verdict is Underconstrained and the
    // which-member-did-we-read hazard never reaches a published fact.
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
        assert_eq!(
            render(&t, &v),
            "Underconstrained params=[(a0) -> int] result=int",
            "X2B"
        );
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

    // X4. The `{:done, []}` rung through a MIXED-ARITY tuple union. `a`
    // occupies the union's payload field and the argument supplies exactly
    // `[]` there, so `a = []` is what THIS call observed and `Known []` is the
    // least solution. It agrees with its same-arity control X4B.
    //
    // This is the rung whose published `{:done, []}` used to reach a fold's
    // return, and it was never this verdict that was wrong: read on its own,
    // the row says only what the argument said. What was wrong was
    // `refine_call_return` MEETING a contract return derived from a rung whose
    // reducer arrow the walk could not read into an already-observed return.
    // The partial-join rule (fz-kdt.210) marks that unreadable occurrence at
    // the fold's own row, so this row no longer needs a veto standing in for
    // it; the veto is gone (fz-kdt.120).
    #[test]
    fn x4_mixed_arity_tuple_union_binds_the_payload_the_argument_supplied() {
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
            "Known params=[{:done, []} | {:halted, []} | {:suspended, [], () -> any}] result=[]",
            "X4"
        );
    }

    // X4B. The SAME question with a SAME-arity tuple union, which the arity
    // projection could always descend: X4's control. The two must agree.
    #[test]
    fn x4b_same_arity_tuple_union_binds_the_payload_the_argument_supplied() {
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
            "Known params=[{:done, []} | {:halted, []}] result=[]",
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

    // X6. ONE TUPLE PARAMETER carrying the same variable twice, one field
    // observing `[]` and the other `[int]`. It now AGREES with its
    // two-parameter control X6B, and the disagreement was the veto's: its
    // scope was the POSITION, so one `[]` anywhere inside a tuple threw away
    // what a sibling field had proved. Nothing replaces it, because the
    // lattice never needed it -- `join(none, int) = int` (fz-kdt.120).
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
            "Known params=[{[int], [int]}] result={[int], [int]}",
            "X6 one tuple parameter"
        );
    }

    // X6B. TWO PARAMETERS carrying the same variable, same observations. X6's
    // control: the same constraint written two ways must give one answer, and
    // since fz-kdt.120 it does.
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

    // X7. `[]` one level down: `[[a]]` at `[[]]`. The inner `[]` reads its
    // element as `none`, so `a = none` -- the BOTTOM lower bound, and the
    // least solution, since instantiating the pattern with it gives back
    // `[[]]`, the argument itself. Sound, and absorbed by the join the moment
    // any other occurrence contributes.
    #[test]
    fn x7_empty_list_one_level_down() {
        let mut t = Types::new();
        let a = t.param_alpha(0);
        let list_a = t.list(a);
        let list_list_a = t.list(list_a);
        let empty = t.empty_list();
        let list_empty = t.list(empty);
        let v = t.match_arrow(&[list_list_a], &list_a, &no_bounds(), &[list_empty]);
        assert_eq!(render(&t, &v), "Known params=[[[none]]] result=[none]", "X7");
        let ArrowMatch::Known { params, .. } = &v else {
            unreachable!("X7 answers Known");
        };
        assert!(
            t.is_equivalent(&params[0], &list_empty),
            "the least solution instantiates the pattern back to the argument"
        );
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
