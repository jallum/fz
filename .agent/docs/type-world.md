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
inside the symbol and narrows the same symbol's brand slot to `{Meters}`, so
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

## The lattice operations

The keying and join logic lean on a few `Types` methods, each with a distinct job:

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
