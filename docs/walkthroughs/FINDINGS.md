# RED.0+ — Cross-fixture findings, refined rules, ticket adjustments

Source: 50 paper walkthroughs across `docs/walkthroughs/*-paper-walk.md`,
produced by a team of 7 agents covering distinct corners of the
fixture matrix (trivial, arithmetic, type-dispatch, pattern matching,
recursion, closures, higher-order, modules, spawn/receive,
multi-process, misc).

## Headline ELI5

**All 50 fixtures walk mechanically through the rules.** No hopeless
issue surfaced. The original seven rules cover the algorithm; the
walkthroughs surfaced **two rules to name explicitly** and **a handful
of clarifications** that should land in the doc before we ship code.

Body-count predictions from the walks:

- **40 fixtures** (the static-input cases): **0 user bodies**. Fully
  reduce to constant `print(...)` calls.
- **6 fixtures** (process / receive): **1 body per process** that
  parks on receive. Boundary is the untyped mailbox.
- **2 fixtures** (count_100k, fib_tailrec at large N — but the
  fixture only tests fib(0|1|10|20), all under budget): **1 body**
  via stop-budget for count_100k.
- **1 fixture** (spec_ok): **0 or 1 body** depending on the
  "trivially inlinable" criterion we ratify — both are sound; the
  walkthrough surfaces both options.
- **1 fixture** (errors): N/A — never reaches the reducer.

The big takeaway is consistent with the design promise:

> Programs with no opacity reduce to constants. Programs with
> opacity get one body per boundary. Predictable from source.

## The refined rule set

The original seven rules + two named additions:

| Rule | When | Effect |
|---|---|---|
| **dispatch** | the callee is a multi-clause fn OR a `case` / `with` scrutinee — anything fed to the pattern matrix; try clause heads (with guards) against the input Descrs | on success: yield `MatchedClause(min_idx, bindings)` with first-match-wins; on no static match: `StopOpaque`; on guard fold-prims-to-false: clause is rejected and we try the next |
| **substitute** | a `MatchedClause` is in hand | replace pattern-bound names in the clause body with their bound Descrs; safe for multi-occurrence; splices effect-sequences correctly when inlining unit-returning calls at statement position |
| **fold-prim** | a `Prim` whose inputs are all literal Descrs OR whose Descr lattice answer is decidable (e.g. cross-kind `==` folds to `false` even on non-literal operands of disjoint kinds) | evaluate to a literal Descr |
| **closure-inline** *(named explicitly)* | the call's callee Var has Descr `closure_lit(F, captures)` | rewrite as a direct call to F with `captures ++ args`; then `dispatch` on F |
| **if-fold** *(named explicitly)* | `Term::If(cond, T, E)` where `cond` is `bool_lit(true)` or `bool_lit(false)` | rewrite to `Term::Goto(T or E, [])` |
| **descend** | the substituted body contains nested calls; not the same callee as the parent | reduce each nested call (counter +1, no decrease check) |
| **recurse-self** | a nested call is the same callee as the parent | only fires if the input Descr is **strictly structurally smaller** than the parent's (counter +1) |
| **stop-opaque** | `dispatch` reports no clause statically matches (Descr too wide) | leave the call in place; emit a body for the callee |
| **stop-non-decrease** | a same-callee recursive call's input is not provably smaller | leave the call in place |
| **stop-budget** | counter exceeds `UNROLL_BUDGET` (default 32) | abandon partial work; leave the **original top-level** call in place |

### Changes from the original seven rules

1. **Added: closure-inline** (rule 4). Two walkthrough batches
   (closures + spawn) confirmed this is the cleanest way to express
   what was implicit. Naming it makes the diagnostic story honest
   ("we inlined this closure because its Descr was a literal
   `closure_lit`").

2. **Added: if-fold** (rule 5). `If(bool_lit, T, E)` collapses to a
   `Goto` — distinct from fold-prim because it operates on a
   terminator, not a Prim.

3. **Split: recurse → descend + recurse-self.** The old `recurse`
   conflated nested-call descent (always fires) with same-callee
   recursion (needs structural-decrease check). Splitting them
   keeps the decrease check from being gratuitously applied to
   non-recursive descent.

4. **Clarified: dispatch.** Operates on any pattern matrix — `fn`
   clauses, `case`, `with`. First-match-wins is load-bearing. Guards
   are part of the dispatch decision (a guard that fold-prims to
   `false` rejects the clause).

5. **Clarified: fold-prim.** Consults the Descr lattice, not just
   literal values. Cross-kind `==`/`!=` folds even on non-literal
   operands when kinds are disjoint.

6. **Clarified: literal Descrs.** First-class literals in the
   lattice include int_lit, float_lit, bool_lit, atom_lit, nil,
   literal tuples (every element literal), literal cons cells
   (head and tail literal), AND `closure_lit(F, [literal captures])`.

7. **Clarified: substitute.** Safe for multi-occurrence
   (`x * x` substitutes `x`'s expr twice — usually fine because the
   bound expr is itself a literal Descr by the time substitution
   fires). Effect-sequences inline correctly at statement position
   (unit-returning calls). Captures from outer scopes flow through
   too (cont closures get literal captures substituted before
   emission).

### Structural-decrease measure — finalized

`recurse-self` fires only when the recursive call's input is
strictly smaller than the parent's. Smaller in any of:

- Tuple arity / projection (fewer fields after extracting one).
- List length (cons → tail).
- Literal-int decrement when the start is a literal int
  (`fact(n-1)` where `n := int_lit(k > 0)` — `n - 1` constant-folds
  to a smaller literal int).

Decrement of an **opaque** integer (`n :: int`, not a literal) does
NOT qualify — count_100k still gets one body via stop-budget.

## What we don't need to change

- **Modules**: zero new rules; fully-qualified `FnId` post-resolve.
- **Macros**: expand pre-reducer. The reducer sees post-expansion IR.
- **Bitstrings**: `ir_const_bs` already folds byte literals into
  `Prim::ConstBitstring` (fz-cty.8). Reducer treats `ConstBitstring`
  as a literal Descr.
- **Imports / aliases**: front-end concerns.
- **`send` / `receive` / `spawn`**: ordinary externs/primitives.
  Only `spawn` has special handling — its fn-value argument
  participates in closure_lit reduction.

## What's still ambiguous and needs ratification

### 1. `@spec` and the "trivially inlinable" criterion (spec_ok)

`spec_ok` demonstrates two valid outcomes:

- **Always-stop:** `add1` gets one body; `main` becomes
  `print(M.add1(41))` → runtime returns `42`.
- **Trivially inlinable:** `add1`'s body is a single Prim tree,
  inline it anyway; `main` becomes `print(42)` directly. Body count: 0.

Both honor the `@spec :: integer → integer` contract (declared type
is an upper bound; narrower inferred is allowed).

**Proposed criterion** (lands in RED.9): a function with `@spec` is
trivially inlinable iff its body is a **single block, single
non-control statement** (one `Prim` plus a `Return`). `add1`
qualifies (`n + 1; Return`). A function with branches, recursion,
or multiple statements gets emitted as a body and treated as a
firewall.

This is a knob the user can flip per-callsite later
(`@inline :always` / `@inline :never`), but the default heuristic
needs to be named before RED.9 ships.

### 2. `spawn(named_fn)` vs `spawn(anonymous_fn)` residual shape

Both produce zero-capture fn-values, but:

- `spawn(child)` (named fn) preserves `child` as a residual body
  in the emitted artifact. Code reads like the source.
- `spawn(fn () -> child(42))` (anonymous, with literal body) lets
  the reducer inline `child(42)` into a synthetic thunk. The
  emitted body is a thunk with no user-visible name.

Both are correct. The difference is observable only in the
diagnostic ("which body does the user see in `--explain-bodies`?").
Recommendation: preserve named-fn identity when the user wrote it
that way; flatten anonymous lambdas. No design change — this is a
naming-convention note for RED.7.

## Ticket adjustments

The findings translate into the following ticket annotations
(applied via `bw comment <id>`):

### fz-jg5.2 (RED.1 — pattern reduction primitive)

> Expand `fold-prim`'s coverage to include kind-disjoint
> `==`/`!=` (from vr5a fixtures): when operand Descrs have
> empty intersection at the kind level, fold to `bool_lit(false)`
> for `==` and `bool_lit(true)` for `!=` — even when operands
> aren't literal values. Also: name `closure_lit(F, [literal
> captures])` and literal cons cells as fold-prim outputs
> alongside int_lit, float_lit, bool_lit, atom_lit, nil. Test
> coverage matrix should include each literal form.

### fz-jg5.3 (RED.2 — clause dispatch via pattern matrix)

> Dispatch returns `MatchedClause(min_idx, bindings)` — first-
> match-wins is load-bearing (from wildcard_then_specific
> fixture). The matrix from fz-ul4.43 already preserves source
> order; the API must surface it. Also: guards (`when ...`) are
> part of the dispatch decision — a guard that fold-prims to
> `false` rejects the clause and continues to the next. And:
> the dispatcher operates on `fn`, `case`, AND `with` matrices
> uniformly — they share the same matrix representation post
> fz-ul4.43.

### fz-jg5.4 (RED.3 — reducer pass scaffold)

> Implement two named rules explicitly: **closure-inline** (when
> the callee's Descr is `closure_lit(F, captures)`, rewrite to a
> direct call to F with captures prepended; then dispatch) and
> **if-fold** (when `Term::If(cond, T, E)` has `cond` as a
> `bool_lit`, rewrite to `Term::Goto`). Both surface explicitly
> in the diagnostic story (RED.7). Also: substitute must handle
> multi-occurrence binders and unit-returning calls at statement
> position (vr5b_typed_print).

### fz-jg5.5 (RED.4 — recursive reduction with unroll budget)

> Ratify **structural-decrease measure** explicitly: tuple
> projection, list cons → tail, AND literal-int decrement when
> start is a literal int. Opaque-int decrement does NOT qualify
> (count_100k touchstone). Split the old `recurse` rule into
> `descend` (any nested call, no decrease check — always fires
> within budget) and `recurse-self` (same-callee recursion;
> structural decrease required). Counter is **per top-level
> callsite**, not per-callee — confirmed by mutual_recursion.

### fz-jg5.7 (RED.6 — re-bless every fixture golden)

> Skip the `errors/` subfixtures entirely — they fail in
> lex/lower/macro/resolve before the reducer runs and have no
> golden CLIF. RED.6's per-fixture review checklist should call
> them out as "N/A — diagnostic-only fixture."

### fz-jg5.8 (RED.7 — --explain-bodies diagnostic)

> For `spawn(named_fn)`, preserve the user's chosen name in the
> diagnostic (the body's source location and identifier come
> from the named fn). For `spawn(fn () -> ...)`, flatten the
> anonymous lambda into a synthetic thunk and label it with the
> spawn site. Both are valid; the diagnostic should be
> consistent and predictable.

### fz-jg5.12 (RED.9 — @spec as downstream-narrowing contract)

> Ratify the **"trivially inlinable" criterion** for @spec'd
> functions: trivially inlinable iff the body is a single block
> containing one non-control statement plus a `Return`. `add1`
> qualifies (one BinOp + Return); anything with multiple stmts,
> branches, or recursion is treated as a firewall. Surface a
> per-callsite override later (`@inline :always` /
> `@inline :never`). This is the heuristic v1; expansion is a
> follow-up not blocking the contract semantics.

## Spike verdict, final

**GO** across the entire fixture matrix. The rules are clean, the
edge cases are named, the ambiguities have proposed resolutions.
The arc proceeds from fz-jg5.2 (RED.1) — implementation work — with
no architectural surprises pending.
