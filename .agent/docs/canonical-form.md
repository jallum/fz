# Canonical Form

Two builds mean the same thing when their **canonical external form** is
byte-equal. That form is text: ordered, structural, and free of every interned
id. It lives in `compiler2/canon.rs` (the artifact) on top of
`compiler2/types/canon.rs` (the types), and it exists only to be compared.

## Why an id is not a comparand

A `Ty` is a position in one `World`'s arena. So are `ShapeId`, `LaneId`,
`CallableId`, `BoundaryId`, `FunctionId`, and `CodeId`. One extra incidental
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
`list(int)` and `non_empty_list(int)` identically as `[int]`, and it renders
each axis's saturated clause as the bare word `any`. For an equivalence oracle a
false equivalence is far worse than a false difference, so the canonical form
distinguishes every shape the lattice does — `empty_list()`, `list(T)` and
`non_empty_list(T)` all render apart, and `tuple`/`list`/`fun`/`map`/`resource`
name the five axis tops.

Getting there takes normalization, because one type has many descriptors. Each
step below rewrites a descriptor to a semantically EQUAL one, which is what
makes "same rendering implies equivalent" true by construction:

- **drop empty clauses** — a clause denoting `∅` contributes nothing;
- **saturate** — clauses that between them cover a whole axis collapse to that
  axis's top. `(X) -> any` constrains nothing, so it denotes every callable
  whatever `X` is;
- **widen tuple coordinates** — replace coordinate *k* of a rectangle with the
  union of coordinate *k* across every same-arity rectangle, keeping the result
  only while it stays inside the axis union. This is what reconciles
  `{list(int), []} | {[], non_empty_list(int)}` with
  `{list(int), []} | {[], list(int)}`: one union carved two ways, where neither
  clause contains the other and so no pairwise subsumption can see it;
- **drop subsumed clauses** — a clause covered by the union of the survivors
  adds nothing;
- **normalize list clauses from their denotation** — a `ListSig` denotes `[]`
  plus lists over an element type, so `list(T) & not([])` and
  `non_empty_list(T)` are one thing and render as one thing;
- **sort** — clause order inside a DNF, and factor order inside a clause, follow
  the order facts arrived in. Sorting them on their rendered bytes is a
  presentation-boundary sort, the one place sorting is free of consequence.

Normalization runs on DESCRIPTORS rather than on interned `Ty`s alone: widening
builds descriptors that were never interned, and interning them would mutate the
arena being described. Rendering is memoized by `Ty`, so the cost is per
distinct type rather than per rendering site.

Every canonical form opens with a **fingerprint** — basic bits, the four nominal
sets, and which structural axes are inhabited. Every component is provably
invariant under type equivalence, because the axes are independent: `a ≡ b`
forces `a \ b = ∅` on each axis separately. Nothing finer is recorded; a clause
count or a clause arity is a property of one decomposition, not of the set. That
makes the fingerprint a sound grouping key, which is how a faithfulness sweep
over a whole arena stays affordable.

## canon(BackendProgram)

Built on `canon(Ty)`, by three rules:

- **interned ids expand** to what they describe. A `ShapeId` becomes its
  descriptor tree, bottoming out in lanes (a type plus a class) and callables (a
  function label plus capture types); a `FunctionId` becomes `Module.name/arity`;
  a `Span`'s code id becomes the submission's name.
- **program-wide positions are re-sorted** on an id-free key. The executable
  vector's published order settles on `Ty`-valued keys, so it moves with the
  arena; the canonical order is an executable's function, input types and need.
  Construction wrappers get the same treatment. Every index into either vector —
  the program entry, direct and closure call targets, wrapper identities, the
  `construction` field on a step — is remapped through that order. The remap
  lives in the RENDERING; nothing renumbers the real structures.
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
