# Canonical Form

Two builds mean the same thing when their **canonical external form** is
byte-equal. That form is text: ordered, structural, and free of every interned
id. It lives in `compiler2/canon.rs` (the artifact) on top of
`compiler2/types/canon.rs` (the types), and it exists only to be compared.

## Why an id is not a comparand

A `Ty` is a position in one `World`'s arena. So are `ShapeId`, `LaneId`,
`CallableId`, `BoundaryId`, `FunctionId`, and `SourceOwner`. One extra incidental
intern anywhere shifts every later id without changing what the program means,
so id equality answers "is this the same *build*", never "do these mean the same
*thing*". Across two processes it answers nothing at all.

Rendering the ids away is bounded work, written once. Making every structure's
iteration order deterministic is not: each new `HashMap` can reintroduce the
wobble, and each compensating sort is a barrier that costs real work at runtime.
The canonical form sits at the sink/test boundary instead, so nothing on a
production path pays for it.

## Three properties, three comparands

Determinism is three separate claims, and no one of them implies another:

| question | comparand | where |
| --- | --- | --- |
| do two builds MEAN the same? | canonical form bytes | `canon.rs` |
| is this the SAME build? | `PartialEq` on `BackendProgram` | raw struct equality |
| did the compiler do the same WORK? | the ordered job sequence | the `fz.compiler2.job` span |

The canonical form is blind to renumbering — that is the point — so it cannot
see a defect that only permutes mint order, and raw equality is the only thing
that can. Raw equality in turn is sound only for two compiles of one input in
one process, where the code path is identical and renumbering therefore implies
nondeterminism. `PartialEq` on `BackendProgram` also carries the incremental
system's invalidation check, so the canonical form never replaces it.

## canon(Ty)

`TyCanon` renders a type so that

```text
canon(a) == canon(b)   iff   a and b are mutually subtype
```

`Types::display` cannot serve, because it is not injective: it renders
`list(int)` and `non_empty_list(int)` identically as `[int]`, and it renders a
clause from the factors it was built out of rather than from what it denotes.
For an equivalence oracle a false equivalence is far worse than a false
difference, so the canonical form distinguishes every shape the lattice does —
`empty_list()`, `list(T)` and `non_empty_list(T)` all render apart. A clause
with no factors denotes every value of ITS kind, which is not `any`, and both
surfaces say so — canon names the five axis tops
`tuple`/`list`/`fun`/`map`/`resource`, while `display` names each as the widest
type a user could write where there is one (`[any]`, `resource(any)`).

Getting there takes normalization, because one type has many descriptors. Each
step below rewrites a descriptor to a semantically EQUAL one, which is what
makes "same rendering implies equivalent" true by construction:

- **absorb a literal-free callable axis** — the shared rule (`types::axis`)
  collapses it to its top when its clauses cover it between them (`(X) -> any`
  constrains nothing, so it denotes every callable whatever `X` is) and
  otherwise drops every clause the union of the survivors already covers;
- **sort** — the axis lists this module BUILDS (the clauses left after its own
  drops, and every axis of a synthesized `Descr`) carry no canonical order, so
  their rendered texts are sorted before they are joined. That is a
  presentation-boundary sort, the one place sorting is free of consequence.
  Clause order and factor order inside an interned descriptor are already
  canonical (`order.rs`), so nothing here re-sorts them.

Dropping empty clauses, tuple carving, list normalization, and absorption of
every literal-free axis happen at the persistence boundary in `Types::intern`.
A literal-bearing clause retains its capture layout for transport. Its args and
result reset to the literal owner's deterministic template. A separately
observed surface travels with the activation input instead of giving the closure
value a second identity.

A `ListSig` denotes `[]` plus lists over an element type, so `list(T) &
not([])` and `non_empty_list(T)` are one thing. The boundary stores the clause
that way for a ground clause, and for a var-bearing clause that needs no element
arithmetic; a var-bearing clause that needs it is stored as it was built,
because the meet the kernel would compute reads a variable as disjoint from
everything and stops being true once the variable is substituted
(`.agent/docs/set-theoretic-types.md`). This module reads the denotation either
way, so `non_empty_list(α) \ non_empty_list(int)` renders as the
`non_empty_list(α)` it denotes. Intern is those rules' authority; this module
is their second caller for the list fragment it builds itself, which never
reaches the interner. A descriptor that did come from the interner is already
in the boundary's normal form. Callable clauses render exactly as stored: a
literal-free axis was absorbed before it received an identity, while a literal
axis keeps the capture layout transport must inspect.

A synthesized descriptor's clause list carries the order its `Descr::union`
folds produced, and absorption visits in index order, so two clauses that
cover EACH OTHER — two carvings of one set, neither inside the other's
containment rule — leave the survivor that position picked. The rendered parts
are sorted, so the order itself never reaches the output; only the choice
between two spellings of one set can. The one such pair reachable by
construction, the axis's widest signature beside the contentless clause, is not
a pair at all any more: the absorber rewrites an axis its clauses cover to the
contentless clause, which is its one spelling.

A free `TypeVarId` is nominal kernel content, not an alternate spelling of a
different free variable. The storage comparator's final raw-id tie-break can
therefore order a set of distinct variables without creating two identities for
one descriptor. Inputs that must compare across independently introduced
variables are alpha-normalized before they become activation coordinates.

Normalization runs on DESCRIPTORS rather than on interned `Ty`s alone: a list
clause's element fragment is a descriptor that was never interned, and interning
it would mutate the arena being described. Completed root forms are memoized by
`Ty`; a recursive body is rendered in its root's binding scope, so it is never
reused as if it were a closed form.

Completed regular components can point back to themselves. Both `Types::display`
and `TyCanon` carry a per-render stack of active `Ty`s: a path that re-enters an
active type is spelled with a binder, such as `μX. :start | {X}`, rather than
followed again. `TyCanon` applies the same binding when list denotation builds a
temporary descriptor equal to an active type's descriptor. The binding is only a
finite serialization of the already-completed component. It never compares types,
changes the interner, or grants a temporary descriptor an identity.

Every canonical form opens with a **fingerprint** — basic bits, the four nominal
sets, and which structural axes are inhabited. Every component is provably
invariant under type equivalence, because the axes are independent: `a ≡ b`
forces `a \ b = ∅` on each axis separately. Nothing finer is recorded; a clause
count or a clause arity is a property of one decomposition, not of the set. That
makes the fingerprint a sound grouping key, which is how a faithfulness sweep
over a whole arena stays affordable.

## canon(BackendProgram)

Built on `canon(Ty)`, by four rules:

- **only semantic artifact content renders**. Product generations and fact
  revisions own freshness, so the program and its canonical form carry no
  synthetic version line.

- **interned ids expand** to what they describe. A `ShapeId` becomes its
  descriptor tree, bottoming out in lanes (a type plus a class) and callables (a
  function label, source arity, and ordered capture layouts). Construction
  captures render their source type annotations beside those layouts.
  A `FunctionId` renders its typed
  `FunctionOrigin`: `Module.name/arity` for named functions, or the shared owner
  label followed by `#lambda@<source-occurrence>/arity` for generated lambdas.
  Both canonical artifacts and fixture call-edge reports use this same renderer;
  no consumer parses a generated display name back into identity.
  A `Span`'s exact source version resolves to the submitted display name.
- **program-wide positions are re-sorted** on an id-free key: an executable's
  function, input types and need; a wrapper's callable, arity, return form and
  member boundaries. The renderer assigns ordinals to `ExecutableKey` and
  `TransportPosition` identities in that order, then uses them for the program
  entry, call targets, wrappers, and construction references. These references
  remain typed keys in the retained bodies. Rendering neither renumbers nor
  rewrites the real structures; runtime ordinal lookups are a separate consumer
  projection of the persistent ordered program inventory. Updating a root
  contribution shares untouched collection branches; canonical rendering walks
  the snapshot only when a caller requests a dump.

  Two entries that render the same tie fall back to published order, so that
  order must also be semantic. `SemanticOrd<Types>` is the single typed owner
  for `ExecutableKey`, `ExecutableSymbol`, and `TransportPosition`; it compares
  activation coordinate records structurally through
  `Types::cmp_activation_signature` and their callable-observation sidecars
  through `Types::cmp_activation_callable_surfaces`, never by raw interner ids
  or rendered text. Packaging and wrapper enumeration consume
  that same relation. `Types::ComparisonCache` stores predicate and activation-
  order verdicts in one operation-tagged key → typed-outcome map; immutable
  interned `Ty` handles make each verdict reusable for the World lifetime, and
  symmetric/reversed queries normalize onto one entry. Before typed publication
  order, a schedule flip could swap two byte-identical construction wrappers on
  `enum_take_drop_split`.
- **body-local ids are re-densified**. `ValueId` and `CallSiteId` are sparse
  after pruning (entries are reindexed, values and callsites are not), so names
  are handed out at first appearance in the body walk: `v0`, `v1`, `cs0`. A
  value the body never mentions has no position to be named by and renders `v?`
  — its content still renders, so only an unreferenced identity is lost.
  `ControlEntryId` is already a dense DFS index and renders as `e{n}`.

Every unordered container is rendered as sorted rows: `HashMap`s keyed by a
body-local id follow the body's naming order, and `BTreeSet`s ordered by raw
`Ty` (callable surfaces and targets) are re-sorted on their rendered form.
`{:?}` appears only on field-free enums, where it is the variant name and
nothing else — never on a container, whose Debug order is per-instance
`RandomState` order and so differs run to run even between equal structs.

`--dump backend` emits this form, which is what makes it byte-identical across
repeated runs and across processes. The `types` and `activations` dumps stay on
`Types::display`: they are human diagnostics, not comparands.

## The ratchet

`compiler2/canon_test.rs` sweeps the full interned arena of two fixtures and
asserts the `iff` above for every pair. It stays affordable two ways, both
exact. Types with different fingerprints are inequivalent by construction and
skip the semantic check entirely. Inside a fingerprint group, equivalence is
transitive: group by canonical form, prove each class equivalent against its own
head, then prove distinct heads pairwise inequivalent.

That sweep is also the permanent guard on interner canonicalization.
`canon(a) == canon(b) && a != b` is exactly "one type, two identities", and the
test asserts the arena still contains such pairs — so it is measuring a real
collapse rather than passing vacuously.
