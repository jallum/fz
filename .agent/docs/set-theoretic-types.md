# Set-Theoretic Types

## Model

A fz type denotes a **set of values**. Subtyping is set inclusion, and the lattice
operations are literal set operations:

```text
A <: B        <=>  ⟦A⟧ ⊆ ⟦B⟧
A and B       =    ⟦A⟧ ∩ ⟦B⟧        (intersect)
A or  B       =    ⟦A⟧ ∪ ⟦B⟧        (union)
not A         =    domain \ ⟦A⟧     (complement)
A is empty    <=>  ⟦A⟧ = ∅          (the decision procedure)
A, B disjoint <=>  ⟦A⟧ ∩ ⟦B⟧ = ∅
```

Everything reduces to deciding emptiness: `is_subtype(a, b)` asks whether
`(a and not b)` is empty; `is_disjoint(a, b)` asks whether `(a and b)` is empty.

A type is a union across independent **axes**, one per runtime kind, held in
disjunctive normal form (DNF). A `Descr` is that union:

```text
basic      a 1-bit bitset: the single bit is `binary` (str is this bit)
atoms      finite-or-cofinite set of atom names   (:ok, :error, nil, true, …)
ints       finite-or-cofinite set of i64
floats     finite-or-cofinite set of f64 bit-patterns
opaques    finite-or-cofinite set of opaque-type names   (nominal)
brands     finite-or-cofinite set of brand names         (nominal)
vars       finite-or-cofinite set of type-variable ids
tuples     DNF of tuple shapes (nested type per element)
lists      DNF of list shapes  (nested elem type, empty/non-empty flag)
resources  DNF of resource shapes (nested payload type)
funcs      DNF of arrow shapes (arg types + ret type, optional closure lit)
maps       DNF of map shapes   (nested value types)
```

`nil`, `true`, and `false` live on the `atoms` axis, not on `basic` (`bool_lit` is
`atom_lit("true")` / `atom_lit("false")`). `str` is exactly the `binary` basic bit.
A value belongs to a type if it belongs to the axis for its kind. `any()` is every
axis at top, `none()` every axis at bottom, and `is_empty` holds when every axis is
empty (structural clauses checked recursively, with a coinductive memo for recursive
shapes).

## Two implementations, one trait

Consumers ask type questions through the `Types` trait (`src/types/mod.rs`), not by
inspecting a representation. `Types::Ty` is an associated type, so the same algebra
runs over two carriers:

- **`ConcreteTypes`** (`src/types/concrete_types/`) — `Ty(Arc<Descr>)`, a
  reference-counted structural descriptor. `types::new()` builds it and
  `DefaultTypes = ConcreteTypes`.
- **Compiler2's `Types`** (`src/compiler2/types/`) — `Ty(u32)`, an interned id into
  one owning interner. The structural kernel is duplicated here so its `Descr` stays
  private and the id space is compiler2-owned. See [`type-world`](type-world.md) for
  the ownership and why id-equality is what lets facts detect change without hashing.

Both kernels carry the same axis model and decision procedure; they differ only in
how a structural child is stored (an `Arc` vs an interned id). A `Ty` handle is
meaningful only with the implementation value that produced it, so handles from two
instances are never composed.

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
param   : (a, b) -> {:cont, b} | {:halt, b}
witness : (integer, {:not_found, int}) ->
            {:cont, {:not_found, int}} | {:halt, {:found, int}}
sigma   : a := integer
          b := {:not_found, int} | {:found, int}
```

This is the load-bearing case for higher-order functions such as
`Enum.reduce_while/3`: the accumulator variable is witnessed by the initial
accumulator and by the reducer's `{:cont, b}` / `{:halt, b}` payloads.

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
yet" (see [`semantic-fixpoint`](semantic-fixpoint.md)). The scheme matcher and
`apply_spec_set` are detailed in [`specs`](specs.md).

## Brands carry their inner; opaques are nominal tags

`brands` and `opaques` are **nominal refinements** over structural representations,
carried as their own axes. A brand carries its inner representation **in the same
`Descr`**, alongside the tag: a brand `B` declared `@type B :: refines U` is the
structural type `U` with the `brands` axis also set. An opaque is a pure nominal
tag: `opaque_of("T")` sets only the `opaques` axis, so the tag is not a subtype of
the plain representation it hides.

```text
mint_brand(binary, "utf8")  : { brands = {utf8}, basic = binary }
plain binary                : { basic  = binary }
opaque_of("T")              : { opaques = {T} }
```

`utf8` is the canonical brand: `utf8 <: binary` because dropping the `brands` axis
leaves a structural `binary`, while a plain `binary` is not a `utf8` because the
unbranded type lacks the tag. Opaque tags make two distinct opaque names
lattice-disjoint, and disjoint from plain structural values unless a consumer
explicitly combines the tag with structural axes.

Because brand inners live in the symbol, **brand questions are answered from the
symbol's own structure** — there is no side map and nothing about a name is
looked up. `mint_brand(inner, name)` is the constructor that establishes a
brand; it is called once, where the name is defined (see
[`type-naming`](type-naming.md)), so the symbol is complete from birth. Opaque
source definitions publish the tag itself; places that need structure, such as a
struct value, model it as the opaque tag intersected with the relevant structural
shape.

**Brands carry no runtime witness.** There is no brand `ValueKind` (the runtime
kinds are Bitstring/ProcBin/Struct/…; see [`any-value`](any-value.md)), and the
runtime compares structure and bytes, so a `utf8` value is indistinguishable from
the binary it wraps. `erase_nominal` is the type-level expression of that fact: it
drops the `brands` and `opaques` axes and keeps the structural axes that remain,
recursing through every structural position, so a brand nested inside a tuple is
discharged too. A pure tag with no structural axes over-approximates to `any()` so
the erased set is never too small.

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
== / != fold, pattern-literal match, guard ==   ->  is_value_disjoint   (value)
parameter / argument checks, FFI marshalling    ->  is_disjoint         (typing)
runtime type test (`x is T`)                    ->  is_subtype/disjoint (typing)
```

There is one runtime-equality relation, `is_value_disjoint`, and every value site
consults it; a literal/guard comparison and a pattern-arm prune lower to that same
brand-blind question. A type test asks the typing question, so `x is utf8`
distinguishes a branded value from a bare binary.

## Struct field types

A struct schema has two separate source facts, and the type model joins them:

```text
defstruct [:first, :last, :step]              # field order
@type t :: %Range{first: integer, ...}        # field types
```

A struct value's hard type is the nominal opaque tag for the implementation target:
`opaque(impl-target::Range)`. A source record type also preserves field information
in its resolved structural shape (`ResolvedTypeShape::StructRecord`), so spec
machinery can see the declared field names and field type shapes without pretending
the opaque tag is a tuple. Field projection at runtime follows the actual struct
value/schema path; unknown or ambiguous receivers stay `any`. The nominal tag is the
same identity protocol dispatch uses (see [`protocols`](protocols.md)) and keeps
`Range` distinct from any structurally similar value.

## Proof gates

```text
cargo test --lib types::            # shared conformance + smoke over ConcreteTypes
cargo test --lib compiler2::types   # the interned implementation
cargo test --lib types::concrete_types::concrete_types_test::
                                    # concrete Descr / DNF / component mechanics
cargo test value_disjoint_soundness_table
cargo test value_disjoint_nested_in_tuple_is_false
```

The fixture corpus pins that `==`, `case`-match, and guard agree across the execution
paths on branded values (`bsx_nested_eq`, `bsx_nested_match`, `bsx_guard_eq`).
