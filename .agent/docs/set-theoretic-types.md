# Set-Theoretic Types

## Model

A fz type denotes a **set of values**. Subtyping is set inclusion, and the lattice
operations are literal set operations:

```text
A <: B        <=>  ⟦A⟧ ⊆ ⟦B⟧
A and B       =    ⟦A⟧ ∩ ⟦B⟧        (intersect)
A or  B       =    ⟦A⟧ ∪ ⟦B⟧        (union)
A \ B         =    ⟦A⟧ \ ⟦B⟧        (difference)
A is empty    <=>  ⟦A⟧ = ∅          (the decision procedure)
A, B disjoint <=>  ⟦A⟧ ∩ ⟦B⟧ = ∅
```

Everything reduces to deciding emptiness: `is_subtype(a, b)` asks whether
`(a \ b)` is empty; `is_disjoint(a, b)` asks whether `(a and b)` is empty.
Difference, not complement, is the primitive: a descriptor cannot hold the
complement of a branded type (see "Brands carry their inner" below), so
`Descr::diff` subtracts factor by factor rather than meeting with a negation.

`is_subtype` is NOT a safe "covers everything the other says" test for a
closure-literal column. `emptiness.rs::func_clause_empty` decides `P \ N` for a
negative arrow carrying a `ClosureLit` from `fn_id` and `captures` alone — it
never reads `args` or `ret` — so two arrows over ONE lambda are mutually
subtypes however far apart their signatures are. That is also why a template
arrow and its ground instance come out equivalent: it is `func_clause_empty`'s
capture-subset test on the shared literal that erases the difference, not a
general absorbing property of free vars. A literal whose own capture TYPE is
empty is empty whatever the rest of the clause says — a closure holds exactly
one value per capture slot, so `#3closure[none]` denotes nothing. Two literals
that can name one value MERGE at intern time rather than staying distinct, so
that is where a `none` capture comes from: one brand met at two capture types,
or the ANONYMOUS literal (a `ClosureLit` with no `fn_id`, fz-kdt.127, which is
every brand at once) met with a branded one. (Vars are nominal on their own axis:
`is_subtype(int, α)` and `is_subtype(α, int)` are both false.) The blind spot
is structural — a lambda inside a tuple, a list, a resource payload, a map
field or another arrow's signature is reached the same way.

Callers that need containment rather than the lattice order ask
`Types::row_column_dominates`, which adds equal `free_var_ids` and containment
of `lit_arrow_shapes` — the `(fn_id, captures, args, ret)` evidence subtyping
discards, collected by the same structural walk `free_var_ids` uses — on top of
`is_subtype`. It is memoized under its own NON-symmetric
`ComparisonKey::RowColumnDominates`; the symmetric-key helper is for relations
whose two positions are interchangeable, and this one's are not.

A type is a union across independent **axes**, one per runtime kind, held in
disjunctive normal form (DNF). A `Descr` is that union:

```text
basic      presence bits: int, float, binary (str is the binary bit)
atoms      finite-or-cofinite set of atom names   (:ok, :error, nil, true, …)
opaques    finite-or-cofinite set of opaque-type names   (nominal)
vars       finite-or-cofinite set of type-variable ids
tuples     DNF of tuple shapes (nested type per element)
lists      DNF of list shapes  (nested elem type, empty/non-empty flag)
resources  DNF of resource shapes (nested payload type)
funcs      DNF of arrow shapes (arg types + ret type, optional closure lit)
maps       DNF of map shapes   (nested value types)
```

One slot is NOT a kind. `brands` is a finite-or-cofinite set of brand names
that REFINES every kind above it at once — a conjunctive factor, not another
member of the union:

```text
brands     which brand a value carries: top = "no constraint" (the unbranded
           case and every brand), a finite set = a nominal refinement
```

`nil`, `true`, and `false` live on the `atoms` axis, not on `basic` (`bool_lit` is
`atom_lit("true")` / `atom_lit("false")`). `str` is exactly the `binary` basic bit.

**Numbers have no literal sets — numeric constants are values, not types.** The
lattice deliberately cannot express `int_lit(42)` or `0 | 1`: `int()` and
`float()` are indivisible presence bits, exactly as in Elixir's
`Module.Types.Descr`. Constant dispatch (`fn f(0)`) is a value comparison the
matcher performs at runtime; constant map keys ride the lowering as values
(`LoweredMapKey`). A numeric literal written in TYPE position (`@type d :: 0`)
means its kind and emits the `type/numeric-literal-widened` warning
(`compiler2/resolve.rs`). Atoms keep singleton sets because `:ok | :error`
unions are the language's backbone. Compiler2's `int_lit` and
`as_int_singleton` trait methods are documented degenerates for the shared
trait surface.
A value belongs to a type if it belongs to the axis for its kind AND its brand is
one the slot admits. `any()` is every axis at top, `none()` every axis at bottom,
and a descriptor is empty when its brand slot is empty (`Meters and Feet`) or every
kind axis is (structural clauses checked recursively, with a coinductive memo for
recursive shapes). `Descr::none()` alone carries the empty slot; every value
constructor starts from `Descr::unbranded()`, whose slot is top. Because a bottom
therefore has more than one shape, `union` asks `looks_empty()` before it joins
anything, so a bottom is the identity however it was reached — a pointwise hull
would read an empty operand's top slot as "any brand" and widen the other side by
it.

DNF construction keeps clause lists hygienic by boolean identity. One clause-
product skeleton (`dnf.rs::dnf_intersect_with`) serves both intersections —
the structural kernel (`Descr::intersect`) and the semantic path
(`Types::intersect`, which collapses same-shape positives through `MergeSig`)
— and it drops duplicate clauses (`A ∨ A = A`), clauses holding a literal
both positively and negatively (`P ∧ ¬P = ∅`), and clauses a `MergeSig` merge
proves empty (`PosMeet::Empty`: tuple arity mismatch, an empty tuple
coordinate or resource payload, a non-empty list sig with no element left).
`dnf_union` drops duplicate clauses and `dnf_neg` skips duplicate factors.

The persistence boundary (`Types::intern`) canonicalizes every descriptor
entering the interner, in three order-preserving passes.

First, ORDER (`order.rs::ClauseOrder`): every DNF axis is sorted by a total
order on clauses, so a descriptor's clause list is a function of its clause set
rather than of the arrival order that built it. A DNF axis denotes a set but is
stored as a `Vec` and every producer appends, so `A ∨ B` and `B ∨ A` used to
reach the interner as two vectors and be handed two `Ty`s for one type — and a
`Ty` IS the identity of a specialization, so which bodies exist was a function
of the schedule (fz-kdt.105). The order is lexicographic over the structure,
compared in place rather than rendered as text: two `Ty`s compare by their
descriptors, recursively, which terminates because a descriptor can only name
`Ty`s interned before it. It is injective — ties happen only between identical
clauses — because the interner is keyed by `Descr`, so distinct ids have
distinct structure; a comparator that could tie two DIFFERENT clauses would hand
the survivor back to arrival order. Closure literals order by the owner's stable
`Module.name/arity` label (`Types::name_callable`, filled in by `World` as it
mints each function id) and structural address vars by their `AddrStep` path,
never by the mint-order `FnId`/`TypeVarId` behind them. Two residuals are
deliberate: a tie broken by two FREE type vars falls back to mint order, and
intra-clause factor order (`Conj::pos`, grown in `dnf_intersect_with` arrival
order) is a second dimension this pass does not touch.

Then ABSORPTION, on the tuples axis: provably-empty clauses are dropped
(`A ∨ ∅ = A`) and subsumed clauses absorbed (`A ⊆ B ⇒ A ∨ B = B`, via
`dnf.rs::tuple_clause_subsumed` over the memoized comparison cache). It has to
run AFTER the sort: it keeps the FIRST of a mutually-subsuming pair, so without
a canonical order the schedule would still be choosing which clause lives.

Then IDEMPOTENCE, on the lists, resources, funcs and maps axes: exact-duplicate
clauses are dropped (`A ∨ A = A`, `dedupe_exact_clauses`, first occurrence
kept). Both later passes are order-preserving filters, so what reaches the
interner index is still sorted — which is also why one pass suffices:
re-interning an interned descriptor sorts a sorted list to itself, finds nothing
left to absorb or collapse, and hits the index.

What clause order canNOT reconcile is a different CARVING of one type:
`{[int], :false} | {[int], :true}` and `{[int], :false | :true}` are one
denotation in two decompositions and still intern apart (fz-kdt.48).

Union-time hygiene is not enough, because clauses are also made
equal AFTER a union — `erase_closure_identity` strips closure brands in place,
turning a legitimate two-brand union into `A ∨ A`, and `funcs = [A, A]` would
otherwise intern as a different `Ty` than `funcs = [A]`. That difference is
what the activation key is built from, so idempotence at the boundary is what
makes the key a join homomorphism (fz-kdt.80). A debug-build assert in
`TypeInterner::intern` (`debug_assert_dnf_axes_hygienic`) sweeps every intern
for both invariants. The tuple-emptiness recursion
(`emptiness::phi_tuple`) returns early on an empty coordinate and drops
negations disjoint from the product, so it explores only inhabited splits
instead of fanning out `arity^|negs|` branches.

## One implementation, shared trait

Consumers ask type questions through the `Types` trait (`src/types/mod.rs`), not by
inspecting a representation. The active implementation is compiler2's
`Types` (`src/compiler2/types/`): `Ty(u32)`, an interned id into one owning
interner. Its structural `Descr` stays private and the id space is
compiler2-owned. See [`type-world`](type-world.md) for the ownership and why
id-equality is what lets facts detect change without hashing.

A `Ty` handle is meaningful only with the implementation value that produced it,
so handles from two `Types` instances are never composed.

The trait is the abstraction boundary for construction, projection, substitution,
nominal disjointness, widening, and equivalence:

- `Types` default methods compose existing hooks (`bool_lit`, `is_equivalent`,
  `differs_only_nominally`).
- An implementation supplies the representation primitives: constructors, lattice
  operations, shape projections, subtype/disjointness decisions, and the
  widening/classification hooks.
- Each implementation's own tests cover representation mechanics only — DNF
  normalization, axis views, interning — while implementation-agnostic semantics are
  asserted once through the shared conformance and smoke suites.

## Schemes vs concrete facts

Free type variables are meaningful only inside a **type scheme** — a parametric
promise such as `forall a b. (a, b) -> {a, b}`. At a callsite the scheme is
instantiated by collecting a substitution from declared parameter patterns and the
caller's witness types, then applying it to the result pattern:

```text
params  : [a, b]
witness : [1, :ok]
sigma   : a := 1, b := :ok
result  : {a, b}[sigma] = {1, :ok}
```

Witness collection is structural and walks only shapes that preserve correlation
clearly enough to bind variables: tuples positionally, list elements, resource
payloads, callable arrows (args and ret), and map fields where keys align. A
variable can be determined by a nested position, not only a top-level parameter:

```text
param   : (a, b) -> {:cont, b} | {:halt, c}
witness : (integer, {:not_found, int}) ->
            {:cont, {:not_found, int}} | {:halt, {:found, int}}
sigma   : a := integer
          b := {:not_found, int}
          c := {:found, int}
```

This is the load-bearing case for higher-order functions such as
`Enum.reduce_while/3`: the accumulator variable is witnessed by the initial
accumulator and the reducer's `{:cont, b}` payload. The halt payload has its own
variable when the contract allows a search result to differ from the accumulator
type.

Witness collection keeps evidence three-valued so a safe-fallback projection is not
mistaken for proof:

```text
Known     this position produced usable substitution evidence
Unknown   this position produced no evidence; keep walking other positions
Invalid   this position is incompatible with the declared shape
```

**The boundary rule is load-bearing:** a scheme may contain free variables; a
complete executable fact may not. A `Ty` with free variables can live in a declared
spec, an arrow clause, or an underconstrained result, but a *settled* return fact or
activation key must be a known concrete type, a boundary-erased dynamic value, or a
diagnostic — never a free variable, and never `none` standing in for "not proven
yet" (see [`semantic-fixpoint`](semantic-fixpoint.md)). Compiler2 now owns
contract-aware arrow matching; `src/specs` only carries the structural shape
model described in [`specs`](specs.md).

## Brands carry their inner; opaques are nominal tags

`brands` and `opaques` are **nominal refinements** over structural representations.
They are carried differently because they mean different things. A brand `B`
declared `@type B :: refines U` is the structural type `U` with the `brands` slot
ALSO narrowed to `{B}` — the same values, fewer of them. An opaque is a pure
nominal tag on its own kind axis: `opaque_of("T")` sets only the `opaques` axis, so
the tag is not a subtype of the plain representation it hides.

```text
mint_brand(binary, "utf8")  : { basic = binary, brands = {utf8} }
plain binary                : { basic = binary, brands = any     }
opaque_of("T")              : { opaques = {T},  brands = any     }
```

An unbranded type's slot is TOP, not empty: `binary` constrains nothing about
brands, so `utf8 <: binary` — dropping the refinement leaves a structural
`binary` — while a plain `binary` is NOT a `utf8`, because `any ⊄ {utf8}`. The
direction is the whole point: a `@spec` position declared `binary` accepts a
`utf8` argument, and a position declared `utf8` rejects a bare `binary`
(`spec/violation`). Opaque tags make two distinct opaque names lattice-disjoint,
and disjoint from plain structural values unless a consumer explicitly combines
the tag with structural axes.

A value carries at most ONE brand. That is a rule of the LANGUAGE, not an
artefact: there is no intersection type expression, so `Positive and Even` is
unwritable, and the lattice reads the meet of two brands over one inner as
EMPTY. `Meters or int` is `int`, and `Meters and Feet` is `none`.

There is no complement operation on a descriptor, and that is by construction:
`not Meters` is "not an int" OR "an int under another brand", two rectangles
where a descriptor holds one, so any `neg` would have to widen to `any` and
forget the brand. Difference is the primitive instead — `Descr::diff` subtracts
the two factors separately. It is EXACT in the three shapes a brand model
produces at one structure: the subtrahend's slot covers ours (`Meters \ int` is
empty), the slots are disjoint (`Meters \ Feet` is `Meters`), and the structures
are syntactically equal (`int \ Meters` is `not(Meters)(int)`). It
OVER-approximates when the slots partly overlap across DIFFERENT structures —
`(int | binary) \ Meters(int)` is the whole `int | binary`, because the exact
answer is two rectangles and a descriptor holds one. That is the safe direction:
every consumer asks `diff(..).is_empty()`, so a too-big difference can only
answer `is_subtype = false` or leave a narrowed branch too wide.
`Descr::neg_structure` is its private helper, the complement of the kind axes
alone.

The empty type therefore has more than one interned identity: `Descr::none()`
carries an empty slot, while `int and binary` meets at empty kind axes with the
slot still at top. `Descr::looks_empty()` is the bottom test; `== Descr::none()`
is not, and `union` and `erase_nominal` both ask it first so that no bottom
widens or resurrects. The canonical form is unaffected — `TyCanon` answers on
emptiness first, so every bottom renders `none` and fingerprints `fp[none]`.

A refinement renders as a refinement, never as a union: `utf8(binary)`,
`not(Meters)(int)`, `(Feet | Meters)(int)`. Rendering it `binary | utf8` would
read as a SUPERTYPE of `binary`, which is the lattice inverted. `display` and
`TyCanon` share the one renderer (`format::brand_refinement`), so the two
surfaces cannot drift.

**Where the encoding is not exact.** A descriptor holds ONE rectangle, and
`union` is the pointwise hull of both factors. That is exact whenever the
operands agree on one factor (`Meters | int`, `Meters | Feet`), but ANY union
whose operands disagree on BOTH factors releases the slot to top and loses the
brand entirely. It takes only one brand to reach: `utf8 | nil` — the shape every
optional `@spec` is written in — admits a bare binary, and so does `utf8 |
integer`. `TypeExpr::Union` is the language's only type combinator, so a brand
cannot yet be trusted at a `@spec` gate beyond the single-brand case. This is a
missed diagnostic, never a miscompile: no runtime test reads the slot, so a
program that slips through the gate runs exactly as the unbranded one would. The
cure is a descriptor holding a union of rectangles — the slot pushed down onto
the per-axis DNF clauses — which is a data-model change; it is a known-wrong pin
in `brand_lattice_law`, see fz-kdt.203.

Because brand inners live in the symbol, **brand questions are answered from the
symbol's own structure** — there is no side map and nothing about a name is
looked up. `mint_brand(inner, name)` is the constructor that establishes a
brand; it is called once, where the name is defined (see
[`type-naming`](type-naming.md)), so the symbol is complete from birth. There is
no constructor for a bare tag with no inner: a refinement of nothing denotes
nothing. Opaque source definitions publish the tag itself. Structs are not
opaques: a `MapSig` carries `MapTag::Struct(ModuleId, name)` and its fields in
one atomic record leaf.

**Brands carry no runtime witness.** There is no brand `ValueKind` (the runtime
kinds are Bitstring/ProcBin/Struct/…; see [`any-value`](any-value.md)), and the
runtime compares structure and bytes, so a `utf8` value is indistinguishable from
the binary it wraps. `erase_nominal` is the type-level expression of that fact: it
releases the `brands` slot to top and drops the `opaques` axis, keeping the
structural axes that remain and recursing through every structural position, so a
brand nested inside a tuple is discharged too. Releasing the slot IS the whole
brand erasure, because the inner is already the structural axes beside it. A pure
opaque tag with no structural axes over-approximates to `any()` so the erased set
is never too small. The runtime type predicate reads the same way: it never
consults the brand slot.

## Two models: typing vs runtime

Two different questions get two different models. Both are decided structurally
from the type value itself — no carrier of nominal maps is threaded into the call:

```text
TYPING question    "is this assignment / dispatch / parameter / FFI legal?"
                   -> brand-AWARE. Brands count. A utf8 parameter rejects a bare
                      binary. is_disjoint / is_subtype use the full lattice.

RUNTIME question   "can these two values be equal? can this pattern match?"
                   -> brand-BLIND. The runtime erases brands and == compares bytes.
                      is_value_disjoint uses the brand-erased lattice.
```

`is_value_disjoint(a, b)` erases nominal tags from both operands and asks whether the
results intersect emptily — set-equal to `is_disjoint(erase_nominal(a),
erase_nominal(b))`. It is the only disjointness that may authorize folding `==`/`!=`
or pruning a pattern arm.

```text
is_value_disjoint(utf8, binary)        = false    (overlap -> == runs)
is_value_disjoint(utf8, int)           = true     (a binary is never an int)
is_value_disjoint(:ok, :error)         = true     (distinct atom singletons)
```

`differs_only_nominally(a, b)` is the in-between case: `a` and `b` are
brand-aware-disjoint yet not value-disjoint, i.e. they look disjoint only because of
an erased brand. That is exactly the set of comparisons a brand-aware fold would have
broken, so consumers surface it rather than fold the comparison away.

## Which predicate, where

The choice of predicate follows the question, not the call site:

```text
== / != fold, pattern-literal match, guard, runtime type test
    ->  is_value_disjoint / runtime_type_predicate   (value; the slot is never read)
@spec argument coverage (arrow_set_covers), extern contracts, dispatch planning
    ->  is_subtype                                   (typing; the slot is compared)
```

There is one runtime-equality relation, `is_value_disjoint`, and every value site
consults it; a literal/guard comparison and a pattern-arm prune lower to that same
brand-blind question. The brand slot is a TYPING fact only: a runtime test is
built by `Types::runtime_type_predicate`, which never reads the slot, so no
runtime test can separate a `utf8` from the binary it wraps. A brand is checked
where types are checked — spec positions, dispatch, boundaries — and nowhere
else.

## Struct field types

A struct schema has two separate source facts, and the type model joins them:

```text
defstruct [:first, :last, :step]              # field order
@type t :: %Range{first: integer, ...}        # field types
```

A struct value's hard type is one tagged map signature: typed `ModuleId`, stable
qualified display name, and declared fields are conjunctive. Plain maps use the
disjoint `MapTag::Plain`; therefore `%Range{first: integer}` cannot become
`%{first: integer}` during overload carving. Record-axis top contains both
families, while `map_top` contains only plain maps. Runtime test envelopes derive
the observable schema-tag question by clearing positive field constraints;
positional tuple storage is derived later from the settled schema, never unioned
into the semantic type. Unknown or ambiguous field projection stays `any`.

## Proof gates

```text
cargo test --lib compiler2::types   # the interned implementation
cargo test --lib dispatch_matrix    # shared generic dispatch/type-region model
cargo test --lib brand_lattice_law  # the refinement direction, by construction
cargo test value_disjoint_soundness_table
cargo test value_disjoint_nested_in_tuple_is_false
```

The fixture corpus pins that `==`, `case`-match, and guard agree across the execution
paths on branded values (`bsx_nested_eq`, `bsx_nested_match`, `bsx_guard_eq`), and
that the typing side is brand-AWARE in both directions: `brand_refines_its_inner`
passes a branded value to an inner-typed `@spec`, and `brand_rejects_a_bare_inner`
is a `spec/violation` for the bare inner at a brand-typed one.
