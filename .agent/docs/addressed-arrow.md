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

The activation key's result side is currently a `none()` placeholder: a key is
minted from inputs only, dispatch is on inputs, and nothing keys on the result.
The activation's real pending return lives in the `ReturnType` fact (an
`Option`, where "unknown" is distinct from the type `none`). `from_inputs` is the
single mint shared by `World::canonical_activation_key` and every other
key-construction site; `realpha_inputs` carries a key minted elsewhere (a flow
edge, a cloned summary) back onto the canonical addresses, and is idempotent on
an already-addressed arrow.

## The dispatch key is a derived collapse, not the evidence

`canonical_activation_key` mints the precise evidence arrow with `from_inputs`,
then — for recursive functions only — derives the dispatch key with
`convergence_collapse(arrow, dispatch_mask)`. The mask is a vector of
`DispatchDemand`, not a boolean keep/drop bit: ignored subtrees collapse to
their `convergence_class` (`list(τ)`, `[]`, and `[] | [τ]` all key as
`list(any)`), while demanded structure can keep only the part dispatch observes
(for example a tuple tag) and collapse the payload. `ListShape(elem_demand)` is
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
key convergence. This is the fz-y6w bounded-specialization control, and it is
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

`match_arrow` first computes per-parameter `overlapping_witnesses` (arity
mismatch or a disjoint parameter → `Invalid`), then `instantiate_match` collects
a substitution `Sigma` across positions. Five behaviors live here that the
boolean subsumption surface (`key_subsumes_with`) cannot express, and are the
reason contract matching is this calculator rather than that one:

1. the `Known`/`Underconstrained`/`Invalid` trichotomy, not a bool;
2. union-on-rebind (`merge_subst_union`) — a variable binding several witnesses
   across positions takes their union, not the first;
3. structural-mismatch → `Invalid` for arrow arity;
4. the same for map-key presence and tuple arity;
5. ambiguous empty-list vars (`collect_ambiguous_empty_list_vars`): a variable
   pinned only by `[]` could be a list of anything, so `surface_sigma` drops it
   and it stays free, keeping the result honestly `Underconstrained`.

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
