# descr-cleanup — set-theoretic alignment

**Status:** design doc for epic `fz-try`. North star for children B1–H.

## What this doc is for

`Descr::Any` currently means three operationally distinct things in the
fz typer. This doc establishes what `Descr` is *for* after the cleanup,
where the other two meanings move to, and the join law and subsumption
rules that follow. All implementation children (`fz-try.2` through
`fz-try.14`) consume the contract written here.

## The problem, named

Today `Descr::Any` is reached for in three situations that the
type-system literature keeps separate:

1. **Pending** — a slot that will be filled by a *later specialization
   step*. The canonical instance: a MakeClosure spec key contains the
   lambda's captures plus padding for its yet-unbound parameters. At
   construction time the parameter values don't exist yet. We pad with
   `Descr::any()` as a placeholder until the call site supplies them.
   See `src/ir_typer.rs:1297` for the padding (`vec![Descr::any();
   n_params]`).

2. **Opaque** — a position whose type is *deliberately erased* so that
   the surrounding function can be reused across many concrete shapes.
   The canonical instance: a closure handle threaded through a
   polymorphic higher-order function like `apply(f, x), do: f(x)`.
   We render the handle's arrow signature as `(any) -> any` because we
   don't want `apply` to be specialized once per closure shape. See
   `src/types.rs:495–496` for the closure_lit constructor that does
   this with `vec![Descr::any(); n_args]`.

3. **Genuine `Any`** — the set-theoretic top. A widening fixpoint we
   reach when a join of disjoint informations exceeds budget, or when
   a recursive call's argument shape converges. The `fib(n, a, b)`
   recursion in `fixtures/fib_tailrec/input.fz` converges to
   `[int, int, int]` — the `int`s are genuine top.

These three situations produce different *operational* behavior in the
reducer, the spec registry, and the codegen. The behavior is currently
correct only because of *implicit reasoning* — code reads the position
of the `Descr::any()` and infers which kind it must be. That implicit
reasoning is spread across the typer, reducer, codegen, and formatter.
Every consumer re-learns the rules. Every refactor risks breaking one
of them silently. The fz-kgk experience already taught us that
positional encoding of identity breaks under IR transformations; this
is the same lesson at the type-system layer.

## The framing: set-theoretic types

The fz type system draws on the set-theoretic typing tradition —
Castagna's work, CDuce, the Elixir team's collaboration with Castagna
([Castagna 2024], [Frisch/Castagna/Benzaken 2008], [Elixir
set-theoretic types]). That tradition is explicit about what the type
lattice does and does not do:

- **Types describe what values *are*.** A type is a set of values; the
  lattice has set-theoretic operations (union, intersection,
  negation). There is one top: the universe of all values.
- **Binding states are not types.** A slot that hasn't received a
  value doesn't *have* a type — it doesn't have a value yet to
  classify. The type lattice should not be used as a placeholder for
  "to be supplied later"; that's a property of the IR shape, not the
  value's type.
- **Parametric polymorphism is its own mechanism.** Types that are
  "the same for all instantiations" are universally-quantified type
  variables, not the top type. A function `(α) -> β` is polymorphic;
  a function `(any) -> any` claims to accept literally any input and
  return literally any output — a different and weaker claim.

The cleanup aligns `Descr`'s job with this framing. The three
overloaded meanings move to their proper homes:

- **Pending → IR shape.** MakeClosure spec keys carry *only the
  captures*. There is no "parameter placeholder" slot in the key at
  all. The body specialization happens at the call site, where the
  parameters get concrete values from the call.
- **Opaque → parametric polymorphism.** Higher-order functions get
  type variables in their signatures. `apply: ∀α,β. ((α) -> β, α) -> β`.
  The variables are inferred (no surface `∀` syntax yet), instantiated
  at each call site, and rendered as α/β in goldens. Monomorphization
  per call site remains the implementation strategy — type variables
  are a typer/surface concept, not a runtime one.
- **Genuine Any stays.** A single top: `Descr::Any`. Appears only at
  widening fixpoints. Construction sites are audited and authorized
  in this doc.

## The cleanup, concretely

### `Descr` after cleanup

```rust
enum Descr {
    // ... existing ground-type constructors:
    //   Int, Float, Bool, Nil, Atom(_), List(_), Tuple(_), Union(_), …
    Var(TypeVarId),    // NEW: parametric type variable
    Any,               // unchanged in spelling; semantically narrowed
                       //   to "widening fixpoint" only
}
```

`Pending` and `Opaque` are not variants. They were never types; they
were positions in the IR or surface using `Descr::any()` as a stand-in.

### MakeClosure spec keys (B1, B2, B3)

**Refinement after investigation: two separate spec kinds, not one.**

The current code registers a single full-arity spec at the MakeClosure
event, padded with `Descr::any()` for the unbound parameter positions.
Reading `src/spec_registry.rs` revealed that this padded spec serves
two distinct roles today:

1. It records that a handle of shape `(fn_id, captures)` exists.
2. It serves as the **any-key body spec** — the canonical compiled
   body for the lambda that indirect dispatch (`stub_fp` path) falls
   through to when a `ClosureCall` can't resolve to a closure literal.

The any-key body role is load-bearing: `register_any_key_at` in
`spec_registry.rs:51` aligns `SpecId.0 == fn_id.0` precisely so the
indirect dispatch path has a stable target. fz-uwq.6 specifically
protected this. Simply removing the padding would break indirect
dispatch.

So the cleanup separates the two roles into two registry entries:

```
// before — one padded spec, two roles overloaded
SpecKey { fn_id, args: [cap_0, …, cap_n, Pending, …, Pending] }

// after — handle spec (new) + any-key body spec (existing)
HandleSpec { fn_id, captures: [cap_0, …, cap_n] }
BodySpec   { fn_id, args: [α_0, …, α_n, α_n+1, …, α_n+m] }  // any-key body
```

The `HandleSpec` records "a handle of shape (fn_id, captures) exists
in some caller's environment." It has arity `captures.len()` and is
*not* a body-dispatch target — indirect dispatch never looks up by
handle shape. It is consumed by the formatter (to render handle
identity in outcomes) and by C3's polymorphism work (the handle's
arrow signature carries type variables; the captures pin which type
variables get instantiated where).

The `BodySpec` is the existing any-key body, unchanged in role. Under
B1+C3, its argument descriptors become type variables (`Var(α_i)`)
instead of `Descr::any()`, so the arrow signature is polymorphic by
construction rather than ad-hoc-opaque. Indirect dispatch still
resolves to it via the any-key (or, after C4, via type-variable
subsumption).

This separation means:

- The registry gets a new entry kind (`HandleSpec`) or grows a marker
  distinguishing handle records from body records. B1's implementation
  decides which.
- Body specs at concrete call sites continue to be minted as today —
  combine captures + arg descrs, look up in the registry, mint if
  absent. B2's job is to make this minting not depend on reading any
  Descr::any() padding from elsewhere.
- The `pending_makeclosure_arity` gate keeps doing its job for body
  specs — body specs depend on opaque arity. The gate stops being
  responsible for the handle spec, which is a separate registration
  that doesn't need arity gating.

**This refinement changes B1's surface area.** The original B1 ticket
proposed removing padding from a single key shape. The refined B1
maintains two key shapes (handle + any-key body) with a clear
contract for each. The work is comparable in size; the design is
more honest.

**Second refinement after implementation (fz-try.15).** Implementation
of B1+B2 surfaced a *fourth* role of the MakeClosure-side padded body
spec that this section initially missed: it carries the per-capture
narrow `return_repr` that the indirect-dispatch `chain_repr`
analysis in `ir_codegen` reads to canonicalize the seam ABI between
a `TailCallClosure` caller and its lambda body. Without the narrow
body spec, the chain sees Tagged at the seam, but the lambda body
(typed at any-key) returns its narrow `ret_repr` — ABI mismatch
surfaces as wrong halt values at runtime
(`spawn_enqueues_child_task` was the canonical repro).

The clean resolution is to canonicalize closure-target body return to
`Tagged` unconditionally — coerce at `Term::Return`, match at
`Term::TailCall` to closure-target callees, match at the cont sig of
the indirect seam. That canonicalization is the prerequisite (filed
as `fz-try.15`) for the full structural collapse envisioned here.

**What lands now (partial B1+B2):**

- The handle channel exists: `ModuleTypes.closure_handles` is
  populated at every reachable MakeClosure site with `(lam_fn_id,
  captures-Descrs)`. Test consumers read it directly.

**What's deferred behind `fz-try.15`:**

- Deletion of MakeClosure's body-spec emit (still emits the padded
  `[captures, Any, ..., Any]` so chain_repr sees narrow seam types).
- Deletion of `opaque_arities` / `pending_makeclosure_arity`
  machinery (still gating the body-spec emit so the .29.10.3
  optimization keeps dropping unreached any-keys).
- Reroute of `closure_shapes` / `MakeClosure` prim codegen to
  `FnId.0` alignment (still goes through dispatch_targets).
- Drop of `dispatch_targets[MakeClosure]` (still written/read).

### Type variables (C1–C5)

A function's typed signature gains type variables wherever it has a
parameter whose type is not pinned by its use within the body. For
example:

```fz
fn apply(f, x), do: f(x)
```

Typed signature: `apply: ∀α,β. ((α) -> β, α) -> β`. Two variables: α
binds to f's parameter type (which is also x's type, by the call
`f(x)`); β binds to f's return type (which is also apply's return
type).

At each call site, type variables are *substituted* (not unified) with
the concrete arg types:

```
apply(add3(10), 20)
  // f = closure handle with arrow (int) -> int (after monomorphization)
  // x = 20: int
  // α ← int, β ← int
  // body spec: apply[α=int, β=int]
```

Substitution, not unification: we monomorphize per call. We do not
infer recursive constraints across mutually-recursive polymorphic
functions. This is a deliberate simplification — full Hindley–Milner is
out of scope for this epic.

Closure handles' surface signatures use type variables too. In
`src/types.rs:495–496` today:

```rust
// before
ArrowSig {
    args: vec![Descr::any(); n_args],
    ret: Box::new(Descr::any()),
}
```

After C3:

```rust
// after
ArrowSig {
    args: (0..n_args).map(|_| Descr::Var(fresh_var())).collect(),
    ret: Box::new(Descr::Var(fresh_var())),
}
```

A closure handle constructed at `add_to(10, 20)` has arrow `(α) -> β`
at construction time. When it flows into `apply1(handle, 12)`, the
typer instantiates α=int (from 12) and β=int (from the body's
inferred return). The arrow becomes concrete `(int) -> int` at that
call site, but the type-variable form persists in the closure_lit's
own representation.

## Join law

The lattice's join (least upper bound) on the cleaned-up `Descr`:

| left  | right        | result        | rationale                                  |
|-------|--------------|---------------|--------------------------------------------|
| Any   | x            | Any           | Top absorbs.                               |
| x     | Any          | Any           | Top absorbs.                               |
| Var α | Var α        | Var α         | Alpha-equivalent variables join trivially. |
| Var α | Var β (α≠β)  | Any           | Distinct variables have no common upper bound less than top. (See note 1.) |
| Var α | Concrete c   | Concrete c    | Variable is a constraint; concrete is a witness. The join is the witness; α is recorded as bound to c. (See note 2.) |
| C1    | C2 (ground)  | C1 ∪ C2       | Set-theoretic union on ground types — unchanged. |

**Note 1: distinct variables join to Any.** This is the conservative
choice. It means that if two control-flow paths produce two
type-variable-typed values from different polymorphic functions, the
join discards the polymorphism. The alternative would be to introduce
a join variable bound by both, which moves us toward proper HM
inference; out of scope. Practically, distinct-variable joins happen
only in pathological code paths, and falling to Any is observable
(the goldens show it) rather than silent.

**Note 2: var ⊔ concrete = concrete (with binding).** This is the
substitution rule. When a type variable meets a concrete witness in a
join, the variable is *instantiated* to the witness at that
specialization scope. The join result is the witness. This is what
makes monomorphization work without unification.

## Subsumption rules (for spec_registry dispatch)

When a dispatch query carrying arg descriptors `q = [q_0, …, q_n]`
looks up a spec keyed on `k = [k_0, …, k_n]`, the match succeeds iff
`q_i ⊆ k_i` for all i, where `⊆` is:

| q_i      | k_i           | match? | binding produced       |
|----------|---------------|--------|------------------------|
| Any      | Any           | yes    | none                   |
| Concrete | Any           | yes    | none                   |
| Var α    | Any           | yes    | none                   |
| Concrete | Concrete (=)  | yes    | none                   |
| Concrete | Concrete (≠)  | no     | —                      |
| Concrete | Var α         | yes    | α ↦ Concrete           |
| Var α    | Var α         | yes    | none (alpha-equiv)     |
| Var α    | Var β (α≠β)   | yes    | α ↦ β                  |
| Var α    | Concrete      | no     | —                      |
| Any      | Concrete      | no     | —                      |
| Any      | Var α         | no     | —                      |

**Ordering when multiple specs match.** Most-specific wins. Specificity
order, high to low: all-concrete > some-Var > all-Var > some-Any >
all-Any. When the order is ambiguous (specs match equally), it's a
design bug in spec emission and should panic in debug. The Castagna
line resolves this via the type-case ordering literature; we adopt
the most-specific rule and rely on debug assertions to catch ambiguity.

## Outcome row schema (E)

The `expected.outcomes` rows take this shape after E:

```
<fn_name>[<spec args, with type-var bindings inline if any>]:
  @<file>:<start>-<end> <Slot> -> <Dispatch>
```

Where:

```
Slot     ::= Direct | Cont | ClosureCall | MakeClosure
Dispatch ::= Folded(value)
           | Static(target)
           | Indirect(body=spec_key, via=value)
           | Stalled(reason)

reason   ::= BudgetExhausted
           | NonReduciblePrim
           | BoundaryFn
           | StructuralDecrease
           | CalleeBodyShape
           | UnresolvedTypeVar   // NEW: arg is Descr::Var(_)
           | OpaqueArg           // arg is Descr::Any (couldn't fold)
           | Other
```

`NoClosureLitTarget` does not survive — it's implied by `Indirect`.
`OpaqueArg` survives but its meaning narrows: it appears only on
`Stalled` rows where the arg is genuine `Any` (widening fixpoint), not
when the arg is a closure handle (that's `Indirect` now).

## What this dissolves

Walking the six smells identified in the closure_typed_captures
proof-on-paper, by node:

| Smell | Description | Node that eliminates it |
|-------|-------------|------------------------|
| S1    | `ClosureLit(0,0)` + `NoClosureLitTarget` self-contradiction | E (slot/dispatch split) |
| S2    | `(any) -> any` on closure handle | C2 + C3 (type vars instead of Descr::any() stubs) |
| S3    | `() -> any` mismatched placeholder (same handle, different rendering) | C3 (consistent type-variable representation) |
| S4    | `lambda_14#14 [10, 20, any]` Pending in MakeClosure spec | B1 (spec key captures-only) |
| S5    | `via OpaqueArg` on closure-handle-arg call | D + E (verb carries no-fold information) |
| S6    | `via OpaqueArg` inherited downstream | D + E (verb carries no-fold information) |

## Acceptance & audit

Acceptance for this doc (`fz-try.1`):

- This doc lands. Subsequent children reference it.
- `Descr::any()` audit complete: every current construction site is
  classified below.

`Descr::any()` construction sites today (fresh grep `rg 'Descr::any\(\)' src/`,
118 total). Counts per file:

```
src/ir_typer.rs        38
src/ir_typer_tests.rs  25
src/types.rs           24
src/ir_codegen.rs       7
src/typer.rs            4
src/type_expr.rs        4
src/reducer.rs          4
src/ir_codegen_tests.rs 4
src/spec_check.rs       3
src/spec_registry.rs    1
src/ir_lower.rs         1
src/ir_dce.rs           1
src/ir_callgraph.rs     1
src/fz_ir.rs            1
```

Classification (categories defined in this doc):

- **Migrates-to-B (Pending):** `src/ir_typer.rs:1297` (the canonical
  `vec![Descr::any(); n_params]` MakeClosure padding) and the small
  number of callers/test sites that mirror it. The B arc removes
  these.
- **Migrates-to-C (Opaque):** `src/types.rs:495–496` (closure_lit
  constructor arrow), plus any other site that constructs a closure
  signature with `Descr::any()` stubs. The C arc replaces these with
  `Descr::Var(fresh_var())`.
- **Stays as widening Any:** sites in join/union/intersect operations
  that legitimately produce top when budget is exceeded or paths
  diverge. Documented in `src/types.rs` algebra and in `src/ir_typer.rs`
  closure-return resolution (`resolve_closure_return` fallbacks at
  lines 345, 350, 360 — these are "we have no information from this
  clause; conservative top").
- **Test sites:** `*_tests.rs` files. These mirror the production
  sites and will migrate alongside them.
- **Default / fallback (audit during execution):** `src/ir_lower.rs:752`
  (extern declaration without type annotation), `src/ir_codegen.rs:877`
  (return type fallback when spec lookup fails), `src/spec_registry.rs:169`
  (any_key padding for any-parameter specs). These are mostly defensive
  fallbacks. The B/C arcs may or may not need to touch them; audit
  during execution.

The full per-site audit happens *during* the B and C children, not
here — this doc identifies the categories; the implementing tickets
make the migrations and prove the audit by grep + tests.

## What the cleanup unlocks

- `pending_makeclosure_arity` becomes a one-line "all captures
  concrete" check or vanishes entirely. Today it's a fragile coupling
  on opaque-arity liveness (recall fz-uwq.6).
- `closure_lit` stops using `Descr::any()` as ad-hoc Opaque stubs.
  The polymorphism in higher-order function signatures is encoded in
  the type, not tribal knowledge about where the `any()` came from.
- Spec-registry subsumption gets a real join law. Dispatch-key
  collisions stop being a class of silent bugs.
- The reducer's defer-vs-dispatch decision becomes a pattern match.
  Implicit reasoning across three sections of `ir_reducer.rs` becomes
  one explicit `match descr { … }`.
- The open `fz-0on` bug (closure-with-captures + higher-order
  recursion SIGILL after first iteration) may become diagnosable by
  type — "Opaque (now `Var`) flowed where concrete was expected"
  becomes visible in the outcomes goldens.
- Three-path parity (interpreter / JIT / AOT) becomes
  compiler-enforced via exhaustiveness on `match descr`.

## Open questions resolved here

0. **The any-key body role is not retired by B1.** Discovered during
   the up-front investigation when reading `spec_registry.rs`. The
   MakeClosure-side padded spec serves two roles today; B1 splits
   them into a new handle spec + the existing any-key body spec.
   The any-key body spec stays load-bearing for indirect dispatch
   (the `stub_fp` path fz-uwq.6 protected). See "MakeClosure spec
   keys (B1, B2, B3)" above for the refined contract.

1. **Type variable representation: `Descr::Var(TypeVarId)` vs separate
   type-scheme layer.** Resolved: `Descr::Var(TypeVarId)`. The
   wrapping-type-scheme approach (Castagna's preferred form) is
   theoretically cleaner but invasive to adopt — every consumer
   already pattern-matches on `Descr` directly, and wrapping would
   require updating all of them to unwrap. `Descr::Var` keeps the
   representation flat and pattern-matchable. The trade-off: alpha
   renaming and instantiation logic must be explicit at the
   instantiation sites rather than absorbed by a substitution
   primitive on the wrapping layer. We accept this cost.

2. **`Stalled(OpaqueArg)` after the split.** Resolved: keeps its
   variant. After the cleanup, `OpaqueArg` means "arg is genuine
   `Descr::Any` (widening fixpoint)" — the reducer would have folded
   if a literal had been available, but the arg is top. Closure-handle
   args become `Indirect`, not `Stalled(OpaqueArg)`. The variant
   survives but its meaning narrows. New variant `UnresolvedTypeVar`
   added for "arg is `Descr::Var(_)`."

3. **Recursion + type variables.** Resolved: type variables persist
   across recursive calls within a single polymorphic function's
   monomorphization. They do not widen to `Any`. A polymorphic
   recursive function `fold` called once at `int` monomorphizes the
   whole recursion at `int`. The widening fixpoint case (the
   `fib [int, int, int]` example) is genuine `Any` only because the
   recursion *narrows* a literal across calls — type variables are
   inferred where types are *static*; widening happens where values
   *flow*. These are different mechanisms.

4. **`fz-0on` framing.** Noted as future work. The cleanup should
   make `fz-0on`'s investigation sharper by exposing the type-level
   information that's currently buried. Not in scope for this epic;
   followup ticket recommended after H.

## References

- Castagna, G. (2024). *Programming with Union, Intersection, and
  Negation Types.* The reference treatment of set-theoretic typing
  with parametric polymorphism. Distinguishes the type lattice from
  the polymorphism mechanism.
- Frisch, A., Castagna, G., Benzaken, V. (2008). *Semantic
  Subtyping: Dealing Set-Theoretically with Function, Union,
  Intersection, and Negation Types.* The foundational paper for
  subsumption with set-theoretic operations.
- Castagna, G., Petrucciani, T., Lanvin, M. (2024). *A type system
  for Elixir.* Working group output with the Elixir core team —
  specifically discusses how the lattice handles polymorphism and
  what stays out of it. Most directly applicable precedent for fz.
- fz-uwq.6 (in this repo) — MakeClosure opaque_arities gate, the
  predecessor to the `pending_makeclosure_arity` mechanism this
  cleanup retires.
- fz-kgk (in this repo) — CallsiteIdent. The lesson "positional
  encoding of identity breaks under IR transformations" applies at
  the type-system layer here.
- fz-j07 (closed, in this repo) — the prior, abandoned design that
  proposed `Descr::Pending | Opaque | Any` as lattice variants. The
  investigation done there (`bw show fz-j07`) informs this doc's
  audit categories.

## Process notes

- The B arc and C arc may proceed in parallel (they touch different
  files; the only shared touch-point is the `pending_makeclosure_arity`
  gate which B retires before C lands). Convention: prefer
  serial-on-trunk to avoid merge conflicts on the spec_registry types,
  unless the implementing engineer has visibility into both arcs.
- D consumes both arcs. D cannot land until both B and C are
  complete and rebased.
- E is structurally independent of B/C but its outcomes goldens
  diverge significantly only after the lattice cleanup lands. Land E
  after D; F is the single rebless commit.
- G runs the full suite. Exhaustiveness check on `match descr { … }`
  sites is the compiler-enforced parity gate.
- H is the final verification: regenerate `report.html` against the
  new goldens, confirm drift-notes sections are empty.
