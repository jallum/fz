# Type World

The compiler owns its own set-theoretic type kernel. A `Ty` is an interned integer
id, and one `Types` instance — held by `World` — is the single authority that mints
and interprets those ids. This is what makes type comparison cheap enough that the
fact engine can detect change by value equality instead of hashing.

## Representation, not naming

`Types` deals in **symbols**: it constructs them (`int`, `list`, `tuple`, `union`,
`mint_brand`, `opaque_of`), combines them (`intersect`, `difference`, `instantiate`,
`refine_widen`), and decides questions about them (`is_subtype`, `is_disjoint`,
`opaque_singleton`). Every method takes and returns symbols. None takes a
source-level type name and resolves it.

That boundary is the design. *What the language calls a symbol* is naming, and
naming is reference-and-definition work that lives in the namespace and the fact
graph (see [`type-naming`](type-naming.md)), not in the kernel. The string a
constructor like `opaque_of("Mod::t")` accepts is the symbol's own nominal identity,
not a key into a lookup table the kernel consults.

Source type expressions arrive as token payloads whose spans retain their exact
immutable `SourceVersion`; resolution uses those spans only for provenance and
diagnostics, never as type identity. The owner/version split is defined in
[`quoted-source`](quoted-source.md#source-identity-and-provenance).

The payoff of keeping the kernel name-blind: a `Ty` is **self-contained**. Every
question about it is answered from its own structure, with no external map threaded
in. A brand minted `mint_brand(integer, "Meters")` carries the integer kind axes
inside one correlated case of the symbol and narrows that case's brand set to
`{Meters}`, so
`is_subtype(Meters, integer)` reads the answer off the symbol; the kernel never
has to look up what `Meters` refines (see
[`set-theoretic-types`](set-theoretic-types.md)).

## Ty is an id, Types is the interner

```text
Ty(u32)                          a structural type, identified by an id
Types { interner, comparisons }  the arena + hash-cons index, plus a cache
Descr                            the private structural kernel behind an id
```

`interner.intern(descr)` returns the existing id for an equal `Descr` or mints a
new one. Two structurally equal types therefore get the **same** id: equality is a
`u32` compare, and a `Vec<Ty>` compares in O(arity). The structural kernel (`dnf`,
`conj`, `bits`, `emptiness`, `sigs`) is private; callers work through
`Ty` and the `Types` methods.

## Preserve an identity before constructing a descriptor

The interner is the only persistence boundary for a descriptor whose outer
structure may have changed. It is not a reason to rebuild a descriptor when an
operation has already proved its answer is an input handle. The laws
`union(t, t) = t`, `refine_widen(t, t) = t`, and refining a map field to the
field's existing `Ty` therefore return that `Ty` directly: no descriptor clone,
hash-table probe, or normalization pass is due.

Instantiation follows the same rule. An empty substitution cannot change any
type, and a concrete type contains no substitution site, so both return their
input `Ty` before traversing or cloning its descriptor. A type that may carry a
replacement still takes the ordinary recursive instantiation path.

Activation-key closure erasure follows it too. Its dispatch mask identifies the
parameters whose closure construction identity is freight. If no parameter is
marked `Ignore`, no identity can be erased, so the existing arrow `Ty` returns
before its parameter vector is cloned or its descriptor reaches the interner.

Pure binary algebra has one additional, handle-level result table. Its key is
the operation tag and its immutable operand `Ty`s; its value is the canonical
`Ty` the ordinary operation returned, whether that was an input handle or a
handle from `Types::intern`. A repeated pair therefore returns that handle
before it rebuilds a descriptor.
The table never compares, hashes, or normalizes a `Descr`, and it lives only for
the owning `Types` world. `union` normalizes its operand pair because its exact
result is order-independent. `difference` stays ordered; so does `intersect`
while distinct mutually-subtype ids remain an observable survivor choice.

This does not turn constructors into a descriptor cache. `tuple` and `arrow`
receive interned children, but their *outer* clause sets are newly built; only
the interner can decide whether that new descriptor names an existing type.
Likewise, transformations without either a local identity law or a pure
operation-plus-handle key must take the ordinary index-before-normalization
path. There is no second structural equivalence authority beside
`Types::intern`.

## One instance, threaded everywhere

Ids only mean anything against the interner that minted them, so there is exactly
one. `World` owns it as `self.types`; reads go through `world.types()`, writes
through `world.types_mut()`, and the fact engine receives `&mut Types` as a
parameter to `complete` rather than owning one. There is no transient `Types::new()`
in the hot path — a throwaway interner would mint ids that mean nothing against the
ids already stored in facts.

## Why the fact layer cares

`Activation` facts store `FactValue::Inputs(Vec<Ty>)`, and `ActivationKey` embeds
`Vec<Ty>`. Because equal types are equal ids:

- A slot's joined value is compared with `==`; the slot revision bumps only when the
  value truly changes. No content hash, no collision risk.
- Activation keys hash and compare in O(arity), so two callers with the same
  canonical input shape land on the same key automatically.

This is the payoff that lets `fact-engine` use revisions-on-change rather than
fingerprints.

## Cyclic reads stay inside the kernel

Completed regular types may contain a path back to an already-completed `Ty`.
Every reader that follows structural children therefore owns a traversal key:
`has_vars` and free-variable collection visit a `Ty` once; substitution
collection visits one `(pattern, witness, side, target)` relation once; and arrow
matching treats a re-entered in-flight relation as its coinductive hypothesis.
The emptiness calculator carries the same kind of descriptor-keyed hypothesis
while it evaluates temporary intersections and differences.

Rendering is another cyclic reader. `Types::display` and `TyCanon` bind an
active `Ty` on a repeated path (`μX. ... X`) so their output is finite. The
binder belongs only to that rendering; the component transaction remains the
only source of recursive type identity and equivalence.

Those guards make readers finite; they do not create a second type store or
license a temporary `Ty` to escape. A transformation that changes a recursive
component must still publish its complete canonical component through the one
interner boundary before a fact or caller can observe an id.

Component construction uses private local references until that boundary. The
interner identifies equivalent local nodes by their finite regular structure,
uses a rooted component key beside its ordinary descriptor keys, and commits a
miss as complete descriptors in one append. A local reference is never a `Ty`,
so there is no unfinished arena slot or later redirection for a reader to
observe.

Transport's `exclusive_tuple_root_arity` is a root-shape question owned by
`Types`. It reads only the root descriptor's runtime-observable axes and tuple
clauses; it never projects tuple children. A mixed root such as
`μX. :start | {integer, X}` therefore rejects tuple decomposition immediately,
while an exclusive tuple root still supplies its arity and ordinary field
projection remains the separate, demanded operation.

## The lattice operations

The keying and join logic lean on a few `Types` methods, each with a distinct job:

`Types` retains its operand-free core inventory when its world is created:
the lattice constants `any` and `none`, the fixed primitive and structural types,
and the three built-in opaques. They are already-normal-form descriptors, so later
requests return their known `Ty` directly instead of rebuilding and looking up a
descriptor. This also makes the exact law `difference(t, t) = none` a direct handle
return. A type with operands still goes through the sole interning boundary; the core
inventory is not a second normalization or result-cache authority.

`Ty` is issued only after that same interning boundary's bottom collapse, so an
interned type is empty exactly when its handle is the retained `none` handle.
`Types::is_empty` is therefore a handle comparison, not a cached or recursive
descriptor traversal. Descriptor-level emptiness still belongs to normalization,
before a `Ty` exists.

The same identity decides operand-empty constructions at the public construction
boundary: `resource(none)` and `non_empty_list(none)` return `none`, while
`list(none)` returns the retained `empty_list`. Their descriptor builders only
write an already-known non-empty operand; they do not re-inspect it or enter the
interner to rediscover a retained result.

It also resolves binary lattice laws before their operand-pair operation table:
`none ∪ t = t`, `none ∩ t = none`, `none \ t = none`, and `t \ none = t`.
These results are direct handles, not cache entries whose hashes repeat a fact the
world already established.

Likewise, public tuple construction checks each field's handle as it copies it.
If one is `none`, the product returns `none` without building a tuple descriptor
or asking normalization to rediscover that fact; inhabited tuples take no extra
pass over their fields.

Plain-map and nominal-struct construction do the same while they build an
ordered required-field map. They account for replacements, so duplicate keys
retain their last value; if a final required field is `none`, construction
returns `none` without a descriptor or a second pass over the fields.

- **`refine_widen(a, b)`** — finite-height least upper bound. Collapses literal axes
  to their base and merges list shapes (`[] ⊔ nonempty(t) = list(t)`), so a joined
  slot ascends a bounded chain and the fixpoint terminates. This is the join behind
  activation-input facts and return types.
- **`convergence_class(a)`** — the coarse identity class for an UNDEMANDED slot of
  a recursive activation key. The whole list family shares one class, including
  single shapes and joined empty/non-empty shapes; disjoint families (`int` vs a
  tagged tuple) stay distinct. "Undemanded" is transitive: a slot is freight only
  when neither this body nor any callee it forwards the slot to asks about it
  (`InputDemand::forwarded_dispatch`, fz-kdt.183). A demanded list keeps its
  element instead, at every depth — see
  [`type-specialization`](type-specialization.md).
- **`alpha_normalize_vars(a)`** — canonicalizes type-variable ids. Interning
  canonicalizes structure, not variable names, so inputs are alpha-normalized before
  they are stored, and alpha-equivalent shapes land on one id.

## Tiny walkthrough

```text
two callers contribute [list(int)] to one activation:
  refine_widen(list(int), list(int)) -> list(int)   (same id, equality short-circuits)
  joined value == previous value -> slot revision unchanged -> no subscriber wakes

empty evidence then contributes to that same list:
  union(empty_list(), list(int)) -> list(int)       (contained list clause is absorbed at intern)
  activation key == previous key -> no executable or revision is minted
```

## Ownership boundary

`World` owns the only `Types`. The structural `Descr` stays private to the kernel;
everything outside the type module — facts, keys, analysis — sees only `Ty` ids and
the comparisons the interner caches. Naming sits outside this boundary entirely: the
kernel is handed symbols and returns symbols, and the question "what does this source
name denote?" is answered before a `Ty` ever reaches it.

Callable literals follow that rule too. `World` registers the same immutable
typed `FunctionDenotation` allocation that its function interner owns before a
literal can name it. This type lives in `fz_runtime::function_denotation`;
compiler `FunctionRef` pairs its shared allocation with the compiler's `ModuleId`.
Clause and activation comparisons read that origin's module/name/arity or
generated owner/source-occurrence fields. These are source identity data, not
rendered labels; the kernel never decodes a display string to discover a callable.
Runtime `Node` retains the same typed origins for closure comparisons. Interpreter
closure creation registers each used origin from its existing shared allocation;
loading another backend program extends the registry without renumbering live
closures or scanning the program's construction inventory.
