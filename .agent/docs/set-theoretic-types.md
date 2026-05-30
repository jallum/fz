# Set-Theoretic Types

## Model

A fz type denotes a **set of values**. Subtyping is set inclusion, and the
lattice operations are literal set operations:

```text
A <: B        <=>  ⟦A⟧ ⊆ ⟦B⟧
A and B       =    ⟦A⟧ ∩ ⟦B⟧        (intersect)
A or  B       =    ⟦A⟧ ∪ ⟦B⟧        (union)
not A         =    domain \ ⟦A⟧     (neg)
A is empty    <=>  ⟦A⟧ = ∅          (the decision procedure)
A, B disjoint <=>  ⟦A⟧ ∩ ⟦B⟧ = ∅
```

Everything reduces to deciding emptiness: `is_subtype(a, b)` asks whether
`(a and not b)` is empty; `is_disjoint(a, b)` asks whether `(a and b)` is
empty.

The carrier is `Descr` (`src/concrete_types/descr.rs`). A `Descr` is a union
across independent **axes**, one per runtime kind, held in DNF:

```text
basic      bitset of binary / ... base kinds
atoms      finite-or-cofinite set of atom names   (:ok, :error, …)
ints       finite-or-cofinite set of i64
floats     finite-or-cofinite set of f64
opaques    finite-or-cofinite set of opaque-type names   (nominal)
brands     finite-or-cofinite set of brand names         (nominal)
vars       type variables
tuples     DNF of tuple shapes (nested Descr per element)
lists      DNF of list shapes  (nested elem Descr)
maps       DNF of map shapes   (nested value Descrs)
funcs      DNF of arrow shapes
resources  DNF of resource shapes
```

A value belongs to a `Descr` if it belongs to the axis for its kind. `any()`
is every axis at top, `none()` every axis at bottom, and `is_empty` holds when
every axis is empty (structural clauses checked recursively).

## Schemes Vs Concrete Facts

Free type variables are meaningful only inside a **type scheme**. A scheme is a
parametric promise such as:

```text
forall a b. (a, b) -> {a, b}
```

At a callsite, the scheme is instantiated by collecting a substitution from
declared parameter patterns and the caller's witness types, then applying that
substitution to the result pattern:

```text
params  : [a, b]
witness : [1, :ok]
sigma   : a := 1, b := :ok
result  : {a, b}[sigma] = {1, :ok}
```

This is the same operation for `@spec foo(a, b) :: {a, b}` and for callable
arrow clauses like `fn (a, b), do: {a, b}`. The shared API is
`types::instantiate_scheme_result`, which reports:

```text
Known(T)             all result variables were determined by witnesses
Underconstrained(T)  variables remain after substitution
Invalid              arity or constraint/subtype checks failed
```

The boundary rule is load-bearing:

```text
Schemes may contain free variables.
Concrete planner/codegen facts may not.
```

A `Ty` with free variables is not executable knowledge. It can live in a
declared spec, arrow clause, or underconstrained-instantiation result, but it
must not be published as a known return fact or ABI-driving spec key. Callsite
shape is structural: a reachable `Term::Call` contributes its direct edge and
its continuation edge independently of how precise the return type currently
is. If the return value is still pending, the planner keeps the continuation
edge with an opaque slot and lets the worklist refine it; it does not encode
"unknown" as `none()` or erase the edge.

## Brands And Opaques

`brands` and `opaques` are **nominal refinements** layered on a structural
type. A brand `B` is declared `@type B :: refines U`; the module records
`brand_inners[B] = U`. `utf8` is the canonical brand: `utf8 <: binary`, while a
plain `binary` is not a `utf8` — the refinement means something precisely
because the unbranded type excludes it.

A minted brand value is a **pure tag**. `Descr::brand_of("utf8")` sets
`brands = {utf8}` and leaves every structural axis — including `basic` —
empty. The "it is really a binary" fact lives in `brand_inners`, not in the
value's `Descr`. `is_subtype_under` consults `brand_inners` to discharge a tag:
a `utf8` is a `binary` because `brand_inners[utf8] <: binary`.

```text
utf8 value's Descr   : { brands = {utf8} }          (basic empty)
plain binary's Descr : { basic  = binary }
brand_inners[utf8]   = { basic  = binary }          (the representation)
```

Brands carry no runtime witness. There is no brand `ValueKind`
(see [any-value](any-value.md) — the kinds are Bitstring/ProcBin/Struct/…).
The `ir_brand_erase` pass rewrites every `Prim::Brand(src, _)` to a
pass-through before codegen, and `fz_value_eq` compares structure and bytes. A
`utf8` value is therefore indistinguishable from the binary it wraps.

## Two Models: Typing Vs Runtime

Two different questions get two different models:

```text
TYPING question    "is this assignment / dispatch / parameter / FFI legal?"
                   -> brand-AWARE. Brands count. A utf8 parameter rejects a
                      bare binary. is_disjoint / is_subtype use the full lattice.

RUNTIME question   "can these two values be equal? can this pattern match?"
                   -> brand-BLIND. The runtime erases brands and == compares
                      bytes. is_value_disjoint uses the brand-erased lattice.
```

`is_value_disjoint(a, b)` is `is_disjoint(erase_nominal(a), erase_nominal(b))`.
`Descr::erase_nominal` discharges every brand and opaque tag to its inner
representation (`brand_inners` / `opaque_inners`), recursing through
tuples/lists/maps — a brand nested inside a tuple is discharged too. It is the
type-level twin of `ir_brand_erase`: both express the single fact that the
runtime has no brand/opaque witness. A new nominal axis must be erased in both.

```text
erase_nominal(utf8)            = binary           (tag -> brand_inners[utf8])
erase_nominal({:ok, utf8})     = {:ok, binary}    (recurses into the tuple)
is_value_disjoint(utf8, binary)        = false    (overlap -> == runs)
is_value_disjoint(utf8, int)           = true     (a binary is never an int)
is_value_disjoint(:ok, :error)         = true     (distinct atom singletons)
```

A minted brand is never a singleton, so it never reaches the both-literal arm
of the equality fold; only the disjoint arm consults the erased model.

## Struct Field Type Declarations

A struct schema has two separate source facts:

```text
defstruct [:first, :last, :step]              # field order
@type t :: %Range{first: integer, ...}        # field types
```

The record type expression is resolved during module type-env construction and
stored as `Program.struct_field_types`, keyed by the struct module name. It is
not guessed from constructor expressions, because constructors are use sites
and may omit fields or carry narrower literals. The schema declaration owns
order; the record type declaration owns declared field types.

The next struct-typing step consumes that map to model a struct as a nominal
opaque tag over the tuple of declared field types. Field projection then becomes
the same kind of structural read as tuple projection, guarded by the nominal
schema tag.

## Which Predicate, Where

```text
== / != fold              reducer::fold_runtime_eq  (is_value_disjoint)   value
codegen == lowering       descrs_value_disjoint     (is_value_disjoint)   value
pattern-literal matching  lowers to the same equality fold                value
guard == (when ...)       reducer::fold_runtime_eq                        value
dead-binop lint           !kinds_overlap && is_value_disjoint             value
parameter / arg checks    is_disjoint / is_subtype                        typing
FFI extern marshalling    is_disjoint                                     typing
x is T  (fold_type_test)  is_disjoint / is_subtype                        typing
```

There is one runtime-equality relation, `is_value_disjoint`, and every value
site consults it. `reducer::fold_runtime_eq` is the shared compile-time
`==`/`!=` decision the reducer and guards use; codegen reaches the same
relation through `descrs_value_disjoint`. A value-equality or matchability site
uses one of these, not the brand-aware `is_disjoint`.

A runtime type test (`x is T`) asks the typing question, so it uses the
brand-aware lattice: `x is utf8` distinguishes a branded value from a bare
binary.

`kinds_overlap` is a deliberately coarse "same kind class?" check used only by
the dead-binop lint. It lets the lint flag genuinely cross-kind comparisons
(`x == :ok` when `x: int`) while staying quiet on within-axis literal-disjoint
pairs (`:ok == :error`). Pairing it with `is_value_disjoint` also keeps it
quiet on a brand against its underlying type, which share a kind once erased.

When a comparison is brand-aware-disjoint but not value-disjoint —
`differs_only_nominally`, i.e. it looks disjoint only because of an erased
brand — the lint stays silent and emits a `[fz, type, brand_blind_eq]`
telemetry event. The comparison runs; the signal records that brands were the
only thing separating the operand types.

## Proof Gates

Gate this model with:

- `cargo test concrete_types::tests::value_disjoint_soundness_table`
- `cargo test concrete_types::tests::value_disjoint_nested_in_tuple_is_false`
- `cargo test reducer::tests::fold_runtime_eq_is_brand_blind`
- `cargo test ir_lower::tests::dead_binop_diagnostic_observable_via_telemetry`
- `cargo test --test fixture_matrix bsx_nested_eq` (and `bsx_nested_match`,
  `bsx_guard_eq`) — `==`, case-match, and guard agree across jit/interp/aot/repl
- `cargo test --test fixture_matrix bsx_brand_blind_eq_emits_telemetry`
