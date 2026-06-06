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

The model is represented by each `Types` implementation's private carrier.
`ConcreteTypes` uses `src/types/concrete_types/descr.rs::Descr`; a `Descr` is a
union across independent **axes**, one per runtime kind, held in DNF:

```text
basic      a 1-bit bitset: the single bit is `binary` (str is this bit)
atoms      finite-or-cofinite set of atom names   (:ok, :error, nil, true, …)
ints       finite-or-cofinite set of i64
floats     finite-or-cofinite set of f64 bit-patterns
opaques    finite-or-cofinite set of opaque-type names   (nominal)
brands     finite-or-cofinite set of brand names         (nominal)
vars       finite-or-cofinite set of type-variable ids
tuples     DNF of tuple shapes (nested Descr per element)
lists      DNF of list shapes  (nested elem Descr, empty/non-empty flag)
resources  DNF of resource shapes (nested payload Descr)
funcs      DNF of arrow shapes (arg Descrs + ret Descr, optional closure lit)
maps       DNF of map shapes   (nested value Descrs)
```

`nil`, `true`, and `false` live on the `atoms` axis, not on `basic`
(`bool_lit` is `atom_lit("true")` / `atom_lit("false")`). `str` is exactly the
`binary` basic bit. A value belongs to a descriptor if it belongs to the axis
for its kind. `any()` is every axis at top, `none()` every axis at bottom, and
`is_empty` holds when every axis is empty (structural clauses checked
recursively, with a coinductive memo for recursive shapes).

## Implementation Boundary

Consumers ask type questions through `Types`, not by inspecting a descriptor.
`Types::Ty` is an associated type and varies by implementation. `ConcreteTypes`
uses `Ty(Arc<concrete_types::Descr>)`; `InternedConcreteTypes` uses
`InternedTy(u32)` handles backed by an interner owned by the
`InternedConcreteTypes` instance.

The interned implementation duplicates the concrete kernel under
`src/types/interned_types/` instead of importing
`types::concrete_types::Descr`. Its own `Descr` is `pub(super)` and structural
children store already-interned `InternedTy` handles. Each instance owns its
`TypeInterner` plus a `HashMap<Descr, InternedTy>` dedup index; there is no
global/static interner, so every handle is meaningful only with the owning
`InternedConcreteTypes` value. `InternedTy` is intentionally local: a raw id
without its arena is a meaningless wire value, so it is never serialized.

`Types` is the abstraction boundary for construction, projection,
substitution, nominal disjointness, widening, and equivalence. Behavior lives
in the highest layer that can express it without knowing the representation:

- `Types` default methods compose existing trait hooks: `bool_lit`,
  `cpointer`, `as_map_key`, `is_equivalent`, `differs_only_nominally`.
- A `Types` implementation supplies representation primitives: constructors,
  lattice operations, shape projections, subtype/disjointness decisions, and
  widening/classification hooks whose answers depend on its internal model.
- `ConcreteTypes`/`Descr` tests cover representation mechanics only: DNF
  normalization, axis views, exact rendering, literal-tag preservation.

Shared behavior is tested from `src/types/mod.rs`. An implementation registers
with `impl_types_conformance_tests!`, which expands the key, shape/seam,
semantic, and closure-surface suites; `impl_smoke_suite!` adds the lattice-law
smoke set. Implementation-agnostic assertions go in those suites; a concrete
test is kept only when the assertion mentions `Descr`, DNF clauses, components,
or another representation detail.

Production code holds one default implementation through the compiler owner:
`Compiler::new()` calls `types::new()` once, stores `DefaultTypes`
(`= ConcreteTypes`), and threads `&mut DefaultTypes` through frontend
expansion/checking, lowering, planning, interpretation, and codegen.
`types::new()` is the factory for the process default; tests may create
isolated instances. Interned `Ty` handles are meaningful only with their owning
implementation value, so composing handles created by different owners is
invalid by construction.

## Schemes Vs Concrete Facts

Free type variables are meaningful only inside a **type scheme** — a parametric
promise such as `forall a b. (a, b) -> {a, b}`. At a callsite, the scheme is
instantiated by collecting a substitution from declared parameter patterns and
the caller's witness types, then applying it to the result pattern:

```text
params  : [a, b]
witness : [1, :ok]
sigma   : a := 1, b := :ok
result  : {a, b}[sigma] = {1, :ok}
```

Witness collection is structural and walks only shapes that preserve
correlation clearly enough to bind variables: tuples positionally, list
elements, resource payloads, callable arrows (args and ret), and map fields
where keys align (`collect_structural_subst` in `src/specs/match.rs`). A
variable can be determined by a nested position, not only a top-level
parameter:

```text
param   : (a, b) -> {:cont, b} | {:halt, b}
witness : (integer, {:not_found, int}) ->
            {:cont, {:not_found, int}} | {:halt, {:found, int}}
sigma   : a := integer
          b := {:not_found, int} | {:found, int}
```

This is the load-bearing case for higher-order functions such as
`Enum.reduce_while/3`: the accumulator variable is witnessed by the initial
accumulator and by the reducer's `{:cont, b}` / `{:halt, b}` continuation/halt
payloads. Binding only from top-level parameters would publish a partial fact
such as `b := {:not_found, 0}`, and native code would compile the wrong return
path.

The matcher keeps "witness evidence" (`Witness`) separate from ordinary runtime
projection:

```text
Known     this position produced usable substitution evidence
Unknown   this position produced no evidence; keep walking other positions
Invalid   this position is incompatible with the declared shape
```

The distinction matters because some runtime projection helpers return top as a
safe fallback. `ListHead(non_list)` can type as `any` for codegen, but a
non-list witness for `list(a)` is not proof that `a := any` — `has_list_shape`
gates the evidence so the fallback is not mistaken for it. Callback parameter
positions are checked for compatibility but do not bind result variables: they
are contravariant demand, not positive evidence.

The same matching serves `@spec foo(a, b) :: {a, b}` and callable arrow clauses
like `fn (a, b), do: {a, b}`. `instantiate_match` returns a `SchemeInstantiation`:

```text
Known(T)             all result variables were determined by witnesses
Underconstrained(T)  variables remain after substitution
Invalid              arity or constraint/subtype checks failed
```

`apply_spec_set` is the higher-level helper over a clause set; it returns a
`SpecApplicationOutcome` of `Known` / `Underconstrained` / `NoMatch`. An
`Underconstrained` outcome still contains variables; it is not a complete return
fact and stays paired with its underconstrained status until a caller supplies
more evidence or erases unresolved positions at an explicit boundary.

`NoMatch` is different from underconstrained: the call arguments are proved
disjoint from every declared arrow. A caller may turn that into `none()` or a
diagnostic for an unreachable arm. A proof *gap* (underconstrained) is not
`none()`.

The boundary rule is load-bearing: a scheme may contain free variables; a
complete executable/codegen fact may not. A `Ty` with free variables can live
in a declared spec, arrow clause, or underconstrained result, but it is never
published as a known return fact or ABI-driving spec key. Callsite shape is
structural and independent of return precision: a reachable `Term::Call`
contributes its direct edge and its continuation edge regardless of how precise
the return type is. When the return is still pending, the planner keeps the
continuation edge with an opaque slot and lets the worklist refine it rather
than encoding "unknown" as `none()` or dropping the edge.

## Brands And Opaques

`brands` and `opaques` are **nominal refinements** over structural
representations. A brand `B` is declared `@type B :: refines U`; the module
records `brand_inners[B] = U`. `utf8` is the canonical brand: `utf8 <: binary`,
while a plain `binary` is not a `utf8` — the refinement means something
precisely because the unbranded type excludes it. An opaque `T` declared
`@type T :: opaque U` records `opaque_inners[T] = U`, but unlike a brand an
opaque is *not* a subtype of its inner: two distinct opaque names are
lattice-disjoint.

Two construction forms put a brand into the lattice:

- `brand_of("utf8")` is the pure nominal tag: `brands = {utf8}`, every
  structural axis (including `basic`) empty. The representation lives in
  `brand_inners`, and `Descr::is_subtype_under` discharges the tag through that
  map to recognise `brand(name) ⊆ inner`.
- `mint_brand(inner, "utf8")` overlays the brand tag onto an already-known
  structural `inner` (it clones `inner` and sets `brands = {utf8}`). The result
  carries both the nominal tag and the structural axes.

```text
brand_of("utf8")     : { brands = {utf8} }          (all structural axes empty)
mint_brand(binary)   : { brands = {utf8}, basic = binary }
plain binary         : { basic  = binary }
brand_inners[utf8]   = { basic  = binary }          (the representation)
```

Brands carry no runtime witness. There is no brand `ValueKind` (see
[any-value](any-value.md) — the kinds are Bitstring/ProcBin/Struct/…). The
`brand_erase` pass (`src/ir_lower/brand_erase.rs`, entry `erase_brands`) runs in
lowering after brand-aware checks and before the lowered `Module` leaves
`ir_lower`: it drops every `Stmt::Let(dest, Prim::Brand(src, _))` and rewrites
references to `dest` as `src` (chains collapse transitively). The runtime
equality `fz_value_eq_ref` compares structure and bytes. A `utf8` value is
therefore indistinguishable from the binary it wraps.

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

`is_value_disjoint(a, b)` erases nominal tags from both operands and asks
whether the results intersect emptily — set-equal to
`is_disjoint(erase_nominal(a), erase_nominal(b))`. `Descr::erase_nominal`
discharges every brand and opaque tag to its inner representation
(`brand_inners` / `opaque_inners`) and recurses through every structural input
position — tuple elements, list element, resource payload, arrow args/ret, map
values — so a brand nested inside a tuple is discharged too. A tag is *replaced*
by its inner (a pure tag has empty structural axes, so merely clearing it would
collapse to `none`). An unknown tag or a cofinite ("any brand") axis
over-approximates to `any()`, so the erased set is never too small and
`is_value_disjoint` never folds a comparison unsoundly. `erase_nominal` is the
type-level twin of `brand_erase`: both express the single fact that the runtime
has no brand/opaque witness, so a new nominal axis is erased in both.

```text
erase_nominal(utf8)            = binary           (tag -> brand_inners[utf8])
erase_nominal({:ok, utf8})     = {:ok, binary}    (recurses into the tuple)
is_value_disjoint(utf8, binary)        = false    (overlap -> == runs)
is_value_disjoint(utf8, int)           = true     (a binary is never an int)
is_value_disjoint(:ok, :error)         = true     (distinct atom singletons)
```

## Struct Field Type Declarations

A struct schema has two separate source facts:

```text
defstruct [:first, :last, :step]              # field order
@type t :: %Range{first: integer, ...}        # field types
```

The record type expression is resolved during module type-env construction and
stored as `Program.struct_field_types`
(`BTreeMap<ModuleName, Vec<(String, Ty)>>`), keyed by the struct module name.
Resolve checks the record against the `defstruct` schema: the declared record
must name every schema field exactly once and may not name fields outside the
schema. It is not guessed from constructor expressions, because constructors are
use sites and may omit fields or carry narrower literals.

Lowering consumes the validated facts by registering an opaque inner type for
the struct implementation target (`struct_opaque_inners` in
`src/ir_lower/mod.rs`):

```text
impl-target::Range -> {integer, integer, integer}
```

The key is the same nominal tag used for protocol-implementation dispatch; the
value is a tuple whose slots are in `defstruct` order. A struct value is
therefore modeled as a nominal opaque tag over a structural field tuple:
`opaque(impl-target::Range) ∩ {first_type, last_type, step_type}`. Field
projection reads the tuple slot selected by the schema when the receiver is a
known singleton struct tag; unknown or ambiguous receivers remain `any`. The
planner does not invent field facts without the nominal tag plus its registered
underlying tuple, and the tag keeps `Range` distinct from any other
three-integer tuple.

## Which Predicate, Where

```text
codegen == / !=           descrs_value_disjoint  -> is_value_disjoint     value
pattern-literal matching  lowers to codegen equality                      value
guard == (when ...)       lowers to codegen equality                      value
dead-binop lint           !kinds_overlap && is_value_disjoint             value
parameter / arg checks    is_disjoint / is_subtype                        typing
FFI extern marshalling    is_disjoint                                     typing
runtime type test (T)     Prim::TypeTest, is_disjoint / is_subtype        typing
```

There is one runtime-equality relation, `is_value_disjoint`, and every value
site consults it. Codegen reaches it through `descrs_value_disjoint`
(`src/ir_codegen/type_pred.rs`) when lowering `==` / `!=`; pattern-literal
matching and guard equality lower to that same codegen path. The planner's
literal `compare_result` fold only collapses int/float singletons to
`true`/`false`, so a minted brand (its `basic` axis is `binary`, never an
int/float singleton) is never folded there; the only brand-sensitive fold is
the value-disjoint arm, which already consults the erased model.

A runtime type test (`x is T`, lowered to `Prim::TypeTest`, and the parameter
guards emitted by `emit_param_type_guards`) asks the typing question, so it uses
the brand-aware lattice: `x is utf8` distinguishes a branded value from a bare
binary.

`kinds_overlap` is a deliberately coarse "share a populated axis?" check used
only by the dead-binop lint. It lets the lint flag genuinely cross-kind
comparisons (`x == :ok` when `x: int`) while staying quiet on within-axis
literal-disjoint pairs (`:ok == :error`, which share the `atoms` axis). Pairing
it with `is_value_disjoint` also keeps it quiet on a brand against its
underlying type, which share a kind once erased.

When a comparison is brand-aware-disjoint but not value-disjoint
(`differs_only_nominally`, i.e. it looks disjoint only because of an erased
brand), the lint stays silent and the planner emits a `[fz, type,
brand_blind_eq]` telemetry event. The comparison runs; the signal records that
brands were the only thing separating the operand types.

## Proof Gates

```text
cargo test --lib types::conformance_tests
    implementation-agnostic Types semantics, defaults, seams, closure surface

cargo test --lib types::interned_types::
    interned handle representation tests (interned_types_test)

cargo test --lib types::concrete_types::concrete_types_test::
    concrete Descr / DNF / component representation mechanics

cargo test --lib
    full library regression suite

cargo test value_disjoint_soundness_table
cargo test value_disjoint_nested_in_tuple_is_false
cargo test dead_binop_diagnostic_observable_via_telemetry
cargo test brand_blind_equality_emits_telemetry_without_dead_binop_warning

cargo test --test fixture_matrix bsx_nested_eq   (and bsx_nested_match,
    bsx_guard_eq) — ==, case-match, and guard agree across jit/interp/aot/repl
```
