# The Addressed Arrow

Every function surface in compiler2 — activation keys, callable surfaces, and
source contracts — speaks one type language: an interned, structurally-addressed
arrow, `(a0, {a1_0, a1_1}, a2) -> r0`. A type variable's canonical identity is
its **structural address** in a signature, not a counter value. Because vars are
addressed the moment a surface is built, the hash-consing interner folds each
alpha-equivalence class to a single integer by construction — so interned
identity *is* the canonical form, and there is no separate normalization pass.

The pieces, and what each owns:

- `types/addressed.rs` — the address vocabulary (`AddrStep`), the var-id
  partition (`ADDRESS_TAG`), and the addressing builders (`address_arrow`,
  `address_inputs`, `own_surface`). This is the construction machinery.
- `identity.rs` — `ActivationKey { root, function, arrow: Ty }`. Dispatch
  identity is the arrow's param side.
- `semantic.rs` — `CallableSurface { inputs }`, addressed at birth.
- `resolve.rs` — `resolve_spec` resolves an `@spec` and addresses it at the
  binder, emitting params/result/bounds all in the address frame.
- `contract.rs` — `ContractArrow { arrow, bounds }`: one interned arrow plus an
  address-keyed bounds sidecar.
- `types/arrow_match.rs` — `match_arrow`, the trichotomy calculator that decides
  contract application. This is the authority for every *compatibility* question.

## A variable is a structural address

Resolving a signature assigns every variable a canonical id that is its address
in the arrow:

- parameter `i` → `a{i}`; the result slot → `r0`
- component `j` of the slot at address `P` → `P_j` (param 1, field 0 → `a1_0`);
  nesting extends the path
- component `j` inside tuple-union alternative `k` at address `P` →
  `P_u{k}_{j}`; repeated source names still reuse their first address, but
  independent variables in different tuple alternatives do not collapse just
  because they occupy the same field position
- a *name's* canonical id is the address of its **first occurrence** (pre-order:
  params left-to-right, then result); repeats reuse it

```text
@spec foo(a, {b, c}, d)    -->  (a0, {a1_0, a1_1}, a2) -> r0    %{a:a0, b:a1_0, c:a1_1, d:a2}
@spec flibble(t, t) :: t   -->  (a0, a0) -> a0                  %{t:a0}
@spec g(t, {t, u})         -->  (a0, {a0, a1_1}) -> r0          %{t:a0, u:a1_1}
```

The address is the structural *path*, not a sequence position. In `foo`, `d` is
`a2` — "parameter 2," full stop — regardless of how many fields the second
parameter's tuple holds. Adding a field to that tuple never renumbers `d`. A
dense counter cannot express the relationship between the slot `a1` (the whole
second parameter) and its contents `a1_0`/`a1_1`; an address can. Two distinct
positions therefore have distinct addresses by construction. The only way two
slots share an id is a shared *name* — which is deliberate.

`AddrStep` is one step of a path: `Param(i)`, `Result`, `Field(j)`,
`Variant(k)`, `Elem`, `Payload`, `MapField(j)`, `VarSlot(k)`. A full address is
a `&[AddrStep]` rooted at a `Param` or `Result`. `address_remap` walks a `Ty`,
replacing each variable with the address of its first occurrence;
`address_remap_children` recurses into tuples/lists/resources/maps/funcs,
extending the path at each child.

## Addressing makes the interner the canonical form

Interning is hash-consing: same structure — variable ids and all — yields the
same integer. That, alone, is **alpha-blind**. `(a5, a5) -> a5` and
`(a9, a9) -> a9` are alpha-equivalent, but their leaf vars differ, so they
intern to two integers; the interner cannot fold them.

Addressing closes the gap at the binder. Every member of an alpha-equivalence
class is built with the *same* ids (`a0`, `a1`, `r0`), so the members are
byte-identical and the interner folds them into one integer — and that integer
is the canonical form.

```text
addressing  canonicalizes variable identity  (assigned once, at the binder)
interning   canonicalizes structure          (hash-consing)
together →  one integer per alpha-equivalence class, by construction
```

Addresses are interned through `Types::address_id`, so `param_alpha(0)` always
yields the same `a0` for a given `Types` instance: structurally identical
signatures build byte-identical arrows.

## Var ids are partitioned by kind

`TypeVarId` carries its KIND in its top bit, with no out-of-band lookup. Bit 31
SET means a structural address (minted by `address_id`); bit 31 CLEAR means a
free var — a closure-surface var (`closure_var_id`, `fn_id*64+pos`), a resolver
encounter var, or a typedef param. The two kinds densely overlap the low range
otherwise (`closure_var_id(0,0) == 0 ==` the first address), so the tag is what
lets display render `a0`/`r0` for addresses and `αN` for free vars without
guessing. `render_var` reads the tag: an address renders by its path
(`format_address`), a free var as the bare `αN`. The tag changes only a var's
*number* — the calculator reads vars by identity, never magnitude — so interning
and equality are untouched: alpha-equivalent arrows still fold to one identity,
`(a, b)` still differs from `(a, a)`.

## Two binders address; everything downstream reads

"Canonical at the binder" has two binders.

**The resolver binder** (`resolve.rs::resolve_spec`). The resolver allocates
first-occurrence ids as raw material, then addresses the whole spec scope in one
pass: `address_arrow_with_env(&params, result)` returns the canonical arrow plus
an `original-id -> address-id` map. Names and bounds re-key through that map —
the `when`-clause bounds become an address-keyed `HashMap<TypeVarId, Ty>` — so
nothing escapes un-addressed. Source contracts (`ContractArrow`) are therefore
*born* canonical: two alpha-equivalent specs intern byte-identical.

**The compiler2 key-mint** (`identity.rs::ActivationKey::from_inputs`).
Activation inputs are produced by *inference* with arbitrary unification ids, not
by the resolver. `from_inputs` addresses the whole input vector with
`address_inputs`: the inputs map into the param-address space `(a0, a1, …)` in
one shared pass — distinct positions stay distinct, repeats share — and the
arrow is canonical the instant it is built. `CallableSurface::new` and the
contribution/callsite normalizers (`normalize_contributions`,
`define_callsite_summary`) call the *same* `address_inputs`, so every
compiler2-side surface lands in one canonical frame.

The activation key's result side is the addressed result var `r0`
(`types.result_alpha()`) — an unknown to resolve, never a `none()` fallback: a
key is minted from inputs only, dispatch is on inputs, and nothing keys on the
result. The activation's real pending return lives in the `ReturnType` fact
(an `Option`, where "unknown" is distinct from the type `none`). `from_inputs` is the
single mint shared by `World::canonical_activation_key` and every other
key-construction site; `realpha_inputs` carries a key minted elsewhere (a flow
edge, a cloned summary) back onto the canonical addresses, and is idempotent on
an already-addressed arrow.

## The dispatch key is a derived collapse, not the evidence

`canonical_activation_key` mints the precise evidence arrow with `from_inputs`,
then — for recursive functions only — derives the dispatch key with
`convergence_collapse(arrow, demand, returned)`, where `demand` is
`InputDemand::forwarded_dispatch` — this body's own entry dispatch joined with
what every callee it forwards a slot to asks of that slot (fz-kdt.183) — and
`returned` is `InputDemand::returned`, the positions this activation's
published return is built from and the recursion does not supply (fz-kdt.199).
`demand` is a
vector of `DispatchDemand`, not a boolean keep/drop bit: UNDEMANDED subtrees
collapse to their `convergence_class` (`list(τ)`, `[]`, and `[] | [τ]` all key
as one addressed list class), while demanded structure can keep only the part
dispatch observes (for example a tuple tag) and collapse the payload. A
demanded list keeps its ELEMENT at every depth, because the element decides
which callee activation the forward reaches; only freight collapses. A RETURNED
position keeps its addressed convergence class on the second axis — list
families normalise to `list(elem)` with the element kept, brands still erase —
because an activation publishes one return and a returned position the key
erased is a position on which two callers' answers blend. `{:done, acc}` is the
shape: the tag is the question, the payload is the answer, and each axis keeps
its own half. A `Whole` slot has no collapse at all, and forwarding can hand a
`Whole` up; that slot sits outside fz-y6w's termination argument. The returned
axis does not widen that: it never keeps a slot verbatim.
`ListShape(elem_demand)` is
still a recursive convergence key: it preserves the demanded element information
from the whole list-family descriptor, then converges empty/non-empty shape to
the all-list class, so a tail-recursive list walk does not fork one activation
for the initial cons case, another for the possibly-empty tail, or another for
an already-joined equivalent list family. A recursive ascent therefore settles
without erasing the discriminator that chose the clause.

Key != evidence is intentional. The precise arrow stays in the
`ActivationInputs` fact; the collapsed arrow is the `HashMap` dispatch key.
Recursive activation-input evidence uses the same demand shape, but only widens
variable-bearing ignored payloads so concrete caller evidence is not lowered by
key convergence. This is a bounded-specialization control, and it is
one whole-arrow operation on the interned arrow — not a per-input pre-pass.

## Matching is subsumption — the trichotomy calculator

Every address in a signature is its own interned `Ty`; the arrow sits on top.
Because each slot is a real interned type, matching a contract against a
less-structured activation is a plain type question, answered by
`Types::match_arrow` (`types/arrow_match.rs`). It returns `ArrowMatch`:

- `Known { params, result }` — every bound variable is grounded; the
  instantiated result is a runtime fact.
- `Underconstrained { params, result }` — the arguments fit but some variable
  stayed free; the instantiation is partial.
- `Invalid` — a structural mismatch (arity, missing map key, tuple width,
  incompatible arrow) or a bound violation rules the signature out.

```text
foo(x, y, z)  vs  foo(a, {b, c}, d):
  addresses align slot 1 ↔ slot 1 (no positional zip)
  question: does y subsume the interned {a1_0, a1_1}?
  yes — y binds the tuple, a1_0/a1_1 stay free → Underconstrained
```

`match_arrow` checks arity and then `instantiate_match` walks `(params, args)`
**once**, collecting a two-sided solution (`MatchBounds { lower, upper }`) one
position at a time, cleaning that position's LOWER bindings, and merging it in —
lowers by union, uppers by meet. A position's WITNESS is its ARGUMENT: what
the call actually supplied there, never the pattern restated. An uninhabited
argument is a row no call can supply and is `Invalid`; ground disjointness is
the structural gate's job, at the end of the walk. Six behaviors live here that
the boolean subsumption surface (`key_subsumes_with`) cannot express, and are
the reason contract matching is this calculator rather than that one:

1. the `Known`/`Underconstrained`/`Invalid` trichotomy, not a bool;
2. union-on-rebind (`merge_subst_union`) — a variable binding several witnesses
   across positions takes their union, not the first;
3. structural-mismatch → `Invalid` for arrow arity;
4. the same for map-key presence and tuple arity;
5. ambiguous empty-list witnesses (`drop_ambiguous_empty_list_bindings`): `[]`
   is a member of every list type, so a binding it pins is noise and is dropped;
6. the POLARITY of a variable's occurrences (below).

## Polarity: lowers instantiate, the meet of uppers is the check

Passing `W` where pattern `P` is declared asserts `W ⊆ σ(P)`. Covariant slots
(list element, tuple field, map field, resource payload, arrow RESULT) preserve
that direction and give a variable a LOWER bound; an arrow's PARAMETERS reverse
it — `(w) -> r ⊆ (σp) -> σr` needs `σp ⊆ w` — and give an UPPER bound.
`BindingSide { Unify, Lower, Upper }` carries the direction: it flips (once) at
an arrow's parameters, `Unify` never flips and is the mode the four unifier
callers (`collect_instantiation_subst`) use so template instantiation is
unchanged. The INSTANTIATION is the join of the lower bounds and nothing else —
an upper bound is not evidence about a value, so it never grounds the result,
the parameters, or a variable. `map([a], (a) -> b)` folded against a reducer
whose parameter is typed `any` keeps `a = int` (the list's element), not
`a = any`; and `f(a, (a) -> nil) :: (a) -> nil` at `(int, (any) -> nil)`
publishes `(int) -> nil` — a supertype of every legal answer — rather than the
unsound `(any) -> nil`.

The meet of the uppers is the solvability CHECK: `join(lowers) ⊆ meet(uppers)`
is a NECESSARY condition (over the variables both bounds reached, over the
OBSERVED lowers, before `close_bounds`) for an instantiation to exist —
`merge_subst_meet` intersects an upper bounded by two positions, so folding
`[int]` with a `(binary, int) -> int` reducer has `int ⊄ binary` and is
`Invalid`. Only the LOWER side is cleaned (an `[]` under an arrow parameter is
an upper bound, which no cleaner touches); a var-carrying argument does not arm
the check, because an upper read from in-flight evidence could ratchet the meet
to a false `Invalid` a later revision revokes. A variable with only upper bounds
has no lower to publish and stays free (`Underconstrained`) — an observable loss
on `f((a) -> nil) :: [a]`, traded for the soundness and precision wins above.

A witness is an OBSERVATION. The alternative — the pattern instantiated by
whatever the argument happened to pin — is not a smaller observation but a
different object, and it is wrong in both directions. It writes the pattern's
own unbound variables back in: `(a, b) -> b` observing `(binary, int) -> int`
comes back as `(a, int) -> int` and `binary` is unrecoverable by anything
downstream. And it replaces whatever the argument said wherever the pattern is
ground: `{int, a}` observing `{int | binary, binary}` comes back as
`{int, binary}`, so the per-position check `witness ⊆ instantiate(pattern,
closed)` compares `{int, binary}` against `{int, binary}` and accepts a call
that must be rejected. The check means `W ⊆ σ(P)` only because `W` is the
argument, so a witness is never narrowed toward its pattern, and a var-carrying
argument cannot arm the check because the observation carries its variables
honestly. Narrowing into a clause domain is a decision one level up, at
`FunctionContract::apply`'s coverage fallback.

The ambiguity in (5) belongs to the **witness**, not to the variable, which is
why the substitution is collected and cleaned per position before (2) unions it
in. The cleaner asks the COLLECTOR which variables one `[]` bound rather than
re-deriving them, because `[]` has no element for `collect_instantiation_subst`
while `list_element_type` reads it as `none`: two readings of one fact is one
reading too many, and they disagreed. It descends a tuple position through the
same positive alternatives the collector pairs, so a mixed-arity tuple union
(`{:done, a} | {:suspended, a, cont}` observing `{:done, []}`) is descended
rather than skipped for being narrower than the pattern's widest arity.

`([a], [a])` applied to `([int], [])` learns `a = int` from the first
parameter and nothing from the second, and answers `Known` with both parameters
`[int]`. A variable *every* position leaves ambiguous simply never enters
`Sigma`, so it stays free and the verdict is honestly `Underconstrained` — the
`f(a) :: a` applied to `[]` case. Vetoing such a variable globally instead would
discard what another position proved: `[a]` would collapse to `[]`, and a good
`[int]` argument would be narrowed to the empty list by `refine_contract_inputs`
(whose empty-intersection fallback does not fire, because `[]` is not empty).

The veto's scope is the **parameter**, so folding the same constraint into one
tuple parameter loses precision that spreading it over two keeps: `([a], [a])`
at `([], [int])` answers `Known [int]`, while `{[a], [a]}` at `{[], [int]}`
answers `Underconstrained` — one `[]` inside the tuple vetoes `a` for the whole
position, including the sibling field that proved `int`. The two shapes state
the same constraint and give different answers. The cleaner is what carries the
scope; marking ambiguity at the moment of binding removes both the scope and the
disagreement.

`ContractArrow::apply` is then a thin loop: for each clause, read
`arrow_params`/`arrow_result`, call `match_arrow` with the bounds sidecar, and
fold `Known`/`Underconstrained` param projections into the applied contract,
unioning the per-clause results.

## Captures are leading addressed slots

A closure activation's surface is `(cap0..capK, param0..) -> r0` — the captures
are leading addressed slots and the source-contract params are the suffix. The
suffix carries `a{K}..` addresses in the full arrow frame. `own_surface`
re-addresses that suffix standalone, rebasing it to the canonical `a0`-based
surface frame, so two closures that share a body but differ in captures yield
one own-surface comparable to a standalone `CallableSurface`.
`own_surface_past_captures` decides capture identity by prefix equality (the
left-to-right addressing property makes the addressed captures exactly the
arrow's leading prefix) and re-addresses the suffix only when the prefix matches.

## The backend boundary: value templates

The interned addressed arrow is the only thing that crosses into keying,
transport, and the backend; names and bounds stop at the semantics boundary. The
one thing that must NOT cross is an activation whose argument has no runtime
representation. `is_value_template` is that predicate: a bare type variable, or a
tuple one of whose fields is a bare variable. It is narrower than `has_vars` — a
callable `(a)->a` or a `list(a)` is a representable value (a pointer, a list), so
inner variables do not make the *value* a template. It is the cheap, sound,
syntactic approximation of meaningful-variable groundness.
`key_is_value_template` lifts it over a whole input vector;
`ground_surface_for_template` uses it to redirect a boxed callable's resolution
from a dead generic activation to a real ground sibling, comparing siblings by
their `own_surface` (by address, not raw position).

The predicate reads the SLOT, not the activation. A value-template activation is
a legitimate semantic fact — the analysis of a generic body — and pruning it
where it is minted breaks escaped-lambda capture analysis, which reads exactly
those facts. What is unrepresentable is the argument, so the semantics say so at
the argument: `callee_has_no_inhabitants` makes a closure call through a bare
variable dead, its result the empty type, and the phantom body then lowers as
the unreachable code it is (fz-f98.18).

## Policy: normalize the key, ask the calculator everywhere else

Canonicalization serves exactly one purpose — the hashable dispatch key. Every
*compatibility* question is a subsumption decision on interned types, never a
comparison of normalized forms.

- **Intra-scope is identity.** Two activations that both ground `a1_0` to `int`
  are interned-identical: pointer equality, zero comparison. This is what shrinks
  activation churn — alpha-equivalent signatures are one object.
- **Cross-scope is the calculator.** When a generic caller threads its *own*
  `a1` into a callee's slot, the namespaces differ; compatibility is consistent-Σ
  subsumption (`key_subsumes_with` / `match_arrow`), exactly as hard as it
  truly is.

Names (`a`, `t`) and bounds (`when a: number`) are an ephemeral resolution
environment. They resolve through the name→address map, live through
type-checking and diagnostics, and never enter the interned type.

## Proof points

```text
cargo test --lib compiler2::types::addressed
cargo test --lib compiler2::types::arrow_match
cargo test --lib compiler2::world_test::compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace
cargo test --test fixture_matrix spec_ok
cargo test --test fixture_matrix spec_boundary
```
