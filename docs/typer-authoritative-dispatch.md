# Typer-Authoritative Dispatch — Design Note

Status: **design**, pre-implementation. The "what and why" companion
to [dispatch-as-typer-output.md](./dispatch-as-typer-output.md)
(which stress-tests the design against concrete language shapes).

This doc walks through how the fz compiler should decide which
compiled version of each function to call, and why one shape is
significantly better than what we have today. Examples first;
nerdy implementation details in footnotes.

## The thing the compiler has to decide

When you write this in fz:

```fz
fn add(a, b), do: a + b
fn main() do
  print(add(1, 2))
  print(add(3.14, 2.71))
end
```

…the compiler has a choice. It could compile *one* version of
`add` that handles any input type (integers, floats, tagged values
generally), and dispatch every caller to that. Or it could compile
*two* versions: one specialized for two integers (returns an
integer directly), one specialized for two floats (returns a
float). Both calls in `main` would dispatch to the right version.

fz chooses specialization. The first `add(1, 2)` dispatches to the
integer-specialized `add`; the second `add(3.14, 2.71)` dispatches
to the float-specialized one. Each specialized version is smaller,
faster, and ABI-tight: integer arguments arrive as raw 64-bit
integers in registers, not as boxed/tagged values that need
unwrapping.

The compiler calls each specialized version a **spec**. A spec is
identified by *what function it specializes* (`add`) and *what
input types it assumes* (`[int_lit(1), int_lit(2)]` or
`[float, float]`).[^spec-key]

At every call site, the compiler picks: "for this call to `add`
with these argument types, which spec do I dispatch to?" That's
the **dispatch decision**. It's the central question this design
note is about.

## Today's contract: two analyses, mutually verifying

Today, the dispatch decision gets made twice.

**Once by the typer.** As the typer infers types, it walks each
call site and decides "given the caller's narrowed argument types,
the right callee spec is this one." It records this as it goes.

**Once by codegen.** When emitting code for a call, codegen takes
the argument types it observes at that moment and asks the spec
registry: "which spec covers these types?" The registry searches
by subsumption — any registered spec whose key is wide enough to
cover the query is a candidate; pick the narrowest.

Most of the time they agree. When they don't, codegen panics with
`no covering spec for FnId(X) with key [...]`.[^panic-history] The
fix-up over the years has been to add a "soundness floor" — keep
a wide any-key spec around for every function so codegen's query
can always find *something*. Then add a closure body picker so the
floor doesn't accidentally get used at the wrong site. Then add a
cont ABI scan so the floor's ABI doesn't break continuations. Each
patch protects against the previous patch's edge cases.

The whole stack exists because **the two analyses don't trust each
other to agree.** They have no choice — they have separate
implementations that can drift.

## The shape we want: one analysis, one answer

The design move is one sentence:

> The typer is the only authority on dispatch. Codegen reads what
> the typer wrote.

If the typer says "call site X dispatches to spec Y," codegen
emits a call to Y. It doesn't second-guess. It doesn't re-derive.
If the answer is wrong, the typer's the place to fix it.

This kills the floor, the closure body picker, the cont ABI scan,
and the resolve-fallback path that landed in [fz-rcp.5][rcp5].
Each was scaffolding around the disagreement; with the
disagreement gone, the scaffolding goes too.

## Where the typer's answer should live

The interesting question is: *where* does the typer write its
answer, so that codegen can read it without ambiguity?

The current attempt was a side table on the module:
`module.callsite_outcomes` keyed by `(caller_fn, block, slot)`.
That table has a real bug, surfaced by the stress test in the
companion doc. Take this program:

```fz
fn id(x), do: x

fn route(f, n), do: f(n)

fn main() do
  print(route(id, 5))           # route's f = id
  print(route(fn(x)->x*2, 5))   # route's f = a lambda
end
```

`route` gets two **specs**, because it's called with two different
`f` values. Both specs share the same IR body — there's only one
copy of `route`'s code — but the *meaning* of `f(n)` differs per
spec. Under spec #1, `f(n)` dispatches to `id`. Under spec #2, it
dispatches to the lambda.

The side table is keyed by `(caller_fn, block, slot)` — that key
doesn't distinguish spec #1 from spec #2. So when the typer writes
both entries, one overwrites the other. Whichever survives, the
other caller spec reads it and gets the wrong answer.

The right home for the dispatch decision is the place where the
caller-spec dimension is naturally available: **the per-spec data
the typer already keeps.**

The typer maintains a `FnTypes` struct per spec — variable types,
per-block environments, reachable blocks. The proposal adds one
more field:

```rust
struct FnTypes {
    vars: HashMap<Var, Descr>,
    block_envs: HashMap<BlockId, HashMap<Var, Descr>>,
    fn_constants: HashMap<Var, FnId>,
    reachable_blocks: HashSet<BlockId>,
    // New: per-callsite dispatch decisions, for THIS spec.
    dispatches: HashMap<CallsiteId, (FnId, Vec<Descr>)>,
}
```

Now `specs[(route, spec1_key)].dispatches[f_n_callsite]` says
"under spec #1, this call dispatches to `id` with key `[int_lit(5)]`."
And `specs[(route, spec2_key)].dispatches[f_n_callsite]` separately
says "under spec #2, this call dispatches to the lambda."

The two answers coexist. Neither overwrites the other. Codegen,
when compiling spec #1, reads spec #1's table; when compiling
spec #2, reads spec #2's. Right answer by construction.

## The invariant that makes the design hold

For "codegen reads what the typer wrote" to be reliable, the IR
the typer reasoned about has to be the IR codegen sees. If passes
between the typer and codegen reshape the IR — moving blocks,
deleting fns, rewriting call terminators — the typer's answers
can refer to things that no longer exist.

The design's invariant:

> All passes that mutate IR call shapes happen *before* the typer.
> After the typer runs, IR and dispatches are both immutable until
> codegen consumes them.

In picture form, today's pipeline:[^pipeline-now]

```
lower → reduce → type → branch_fold → fold → dce → inline_conts → dce → dce_module → codegen
                  ↑                                  ↑
                  publishes                          mutates call shapes
                  outcomes                           AFTER outcomes published
                                                    (drift zone)
```

Proposed:

```
lower → reduce → inline_conts → type → branch_fold → fold → dce → dce_module → codegen
                 ↑                ↑     ↑
                 moves before     types  fold prims + delete unreachable —
                 typer            once   neither touches call shapes
```

The move of `inline_single_use_conts` is the load-bearing change.
Its gating is all structural (count references, look for `Receive`,
look for self-calls) — none of it needs type info.[^inline-gating]
The only reason it runs post-typer today is convention. Moving it
pre-typer eliminates the worst drift case and removes a non-trivial
chunk of mutable state-tracking code (`&mut ModuleTypes` plumbing
inside the inliner).

`branch_fold`, `fold`, and `dce` stay post-typer. They mutate
prims, fold `If` terminators, and delete unreachable blocks —
none of which touch call shapes or invalidate dispatches.[^post-typer]

## How each long-standing problem dissolves

The fz-rcp epic identified five follow-on problems. Under this
design:

**MakeClosure body picker** (which compiled body does a closure
header point at?). Reads `specs[caller_spec].dispatches[MakeClosure_site]`
to get the lambda spec the typer chose. Closure header stores
that spec's compiled function id. ABI matches the captures by
construction.

**closure_shapes builder.** Walks dispatches once to catalog
shapes. No separate analysis.

**Tagged-slot-0 cont ABI scan.** A continuation's slot-0 ABI must
match the calling function's return-value ABI. The typer already
knows both — the spec's return descr lives in FnTypes; the cont's
dispatch lives in FnTypes.dispatches. The match falls out of one
lookup.

**Outcomes go stale across mutations.** The invariant says no
post-typer mutation reshapes calls. No staleness possible.

**The any-key blanket seed** (fz-aiz.7). Existed as insurance
against codegen's resolve missing. Codegen doesn't resolve at
dispatch sites anymore. Insurance is unneeded; seed drops.

Each of these has a P1 ticket today, framed as five separate
ports.[^rcp-tickets] All five collapse into "land the
dispatches-on-FnTypes design + delete the resolve fallback." One
arc, one shape, five problems gone.

## Beyond dispatch: the per-spec plan pattern

This doc has so far used "dispatch" as the lens, but the shape it
proposes is more general than dispatch. The actual move is:
**`FnTypes` becomes the typer's per-spec compilation plan, and
each kind of decision the typer makes about a spec lives in a
table keyed by the site that decision applies to.**

Dispatch is the first inhabitant. The natural second is
destination-passing style (DPS).[^dps-epic]

Destination-passing is the optimization where instead of allocating
a value and returning it:

```fz
fn make_pair(a, b), do: {a, b}
fn main(), do: print(make_pair(1, 2))
```

…the compiler arranges for `make_pair` to write directly into a
slot the caller already prepared — no intermediate heap object,
no copy. The decision "should this `MakeTuple` allocate, or write
into a destination?" is per-spec, just like dispatch:

- Under a spec where the tuple's value flows straight to
  `Term::Return`, plan = "write to the caller's return slot,
  skip heap alloc entirely."
- Under a spec where the tuple escapes into a closure capture,
  plan = "must allocate; return pointer."
- Under a spec where the tuple is consumed by a folded prim and
  never crosses a function boundary, plan = "elide; the consumer
  reads directly from the producer's vars."

Same IR node (`Prim::MakeTuple(a, b)`). Three plans across three
specs. The decision is per-spec just like dispatch is per-spec.

The structural mirror is exact:

```rust
enum AllocSlot {
    Tuple(usize),     // stmt_idx within the block
    Cons(usize),
    Struct(usize),
    Closure(usize),
    Map(usize),
    Bitstring(usize),
    Vec(usize),
}

struct AllocSiteId {
    fn: FnId,
    block: BlockId,
    slot: AllocSlot,
}

// And `FnTypes` grows a second per-site table:
struct FnTypes {
    // existing
    vars: HashMap<Var, Descr>,
    block_envs: HashMap<BlockId, HashMap<Var, Descr>>,
    fn_constants: HashMap<Var, FnId>,
    reachable_blocks: HashSet<BlockId>,
    dispatches: HashMap<CallsiteId, (FnId, Vec<Descr>)>,
    // new
    alloc_plans: HashMap<AllocSiteId, AllocPlan>,
}
```

Codegen, when compiling spec `k`, reads `specs[k].alloc_plans[asid]`
at every allocating prim and emits accordingly: write-to-dest,
allocate-and-return, or elide. The same phase-ordering invariant
applies — the typer publishes; the IR is frozen; codegen reads.

There's one interesting wrinkle worth being explicit about:
**`MakeClosure` has dual identity.** A `Prim::MakeClosure(lambda,
captures)` is both a dispatch site (which spec of `lambda` does
this closure's body pointer reference?) and an allocation site
(the closure header object on the heap). The same `(fn, block,
stmt_idx)` triple participates in both tables:

- `CallsiteId { …, slot: EmitSlot::MakeClosure(N) }` →
  `dispatches[...]` gives the lambda spec.
- `AllocSiteId { …, slot: AllocSlot::Closure(N) }` →
  `alloc_plans[...]` gives the DPS plan for the header object.

Two lookups, same underlying IR position. Not a problem to model
— the IR node has two natures, so it has two corresponding
plan-table entries.[^dual-identity]

### DPS plans form chains; chains resolve outside-in

There's one operational subtlety DPS introduces that dispatch
doesn't have, worth pinning down before any DPS ticket lands.

When the planner decides "this `MakeTuple` should fuse into its
consumer," the consumer is itself an alloc site that may also be
eligible for fusion. So an `alloc_plans` entry can point at
another `AllocSiteId`, which points at another, until the chain
reaches a *terminal plan* — one that doesn't reference a further
alloc:

- `Heap` — allocate normally.
- `WriteToReturn(slot)` — write directly into the caller's return
  slot at a `Term::Return` position.
- `WriteToCallerArg(slot)` — write into a destination the caller
  threaded in (future, for cross-fn DPS).

Chains are guaranteed acyclic by SSA — a producer's output Var
dominates its consumers, so a cycle would require a node to read
its own output. They're guaranteed linear (chains, not trees) by
DPS's single-consumer gating — fusion only applies when there's
exactly one user of the produced value.

The invariant the planner must hold:

> **DPS chain resolution invariant.** Plans are computed per spec
> in reverse-dataflow order: terminal plans (`Heap`,
> `WriteToReturn`, …) first; producers second. By the time any
> producer's plan is recorded in `FnTypes.alloc_plans`, its
> consumer's plan is already resolved, so the producer's recorded
> destination is the resolved root — not a chain pointer to be
> followed at codegen.

Codegen, as a consequence, never walks a chain. It reads one
entry per alloc site and gets the final destination directly.
Fusion lives entirely inside the planner; the table codegen reads
is post-resolution.[^lattice-roots]

The deeper principle:

> **`FnTypes` is the typer's contract with codegen.** Every per-spec
> compilation decision lives there, keyed by the site it applies
> to, immutable after the typer publishes.

Future inhabitants beyond dispatch and DPS are easy to imagine
— escape information, ABI choices per call site, inline-vs-call
decisions per site, register pinning, you name it. Each fits the
pattern: define a `SiteId` type for the positions where the
decision applies, add a `HashMap<SiteId, Plan>` field on
`FnTypes`, populate during the typer's walk, read at codegen.

The dispatch design isn't a one-off — it's the first realization
of a pattern the typer should follow for every per-spec decision
it ever wants to make. That makes the architecture forward-
compatible without further restructuring.

## What gets deleted vs what gets added

The honest accounting matters. Architecture work that *adds* code
to delete future bugs is a bad trade. Architecture work that
*removes* code is the right trade.

What deletes:
- `Module.callsite_outcomes` field.[^callsite-outcomes-field]
- `apply_callsite_outcomes` function.
- The split between `ModuleTypes.callsite_outcome_updates` (typer-side)
  and `Module.callsite_outcomes` (module-side); the dance between them.
- Codegen's `spec_registry.resolve` calls at every dispatch site
  (closure body picker, cont ABI, the existing two from fz-rcp.5,
  the closure_shapes builder).
- The fz-rcp.5 resolve fallback path.
- The any-key floor (fz-aiz.7 territory).
- The `&mut ModuleTypes` maintenance code inside
  `inline_single_use_conts`.
- The closure body picker's "fall back to any registered spec for
  this lambda" branch.

What adds:
- One `dispatches: HashMap<CallsiteId, (FnId, Vec<Descr>)>` field
  on `FnTypes`.
- One `ReducerLog` return value from `reduce_module` (replacing the
  reducer's writes into `callsite_outcomes`).
- Reads in codegen of the form `specs[k].dispatches[cid]` (replacing
  the resolve calls).

Net delta: heavily negative. The design simplifies the codebase
while making correctness sharper. That's the right trade.

## The shape of the migration

A reasonable arc:

1. **Move `inline_single_use_conts` pre-typer.** Drop the
   `&mut ModuleTypes` plumbing. Add a debug-build assertion that
   the lowerer mints one cont per callsite (so the worry the
   stress test surfaced can't bite).
2. **Add `dispatches` to `FnTypes`.** Populate during the typer's
   discovery walk. (Per-spec; no projection to lose information.)
3. **Migrate codegen dispatch sites** (cont resolve, direct callee,
   MakeClosure body picker, closure_shapes, cont ABI scan) to read
   from `dispatches`. Parity-asserted: keep resolve live with a
   `debug_assert_eq!`, run the matrix, swap reads, drop resolve.
4. **Delete `Module.callsite_outcomes`** and the
   `apply_callsite_outcomes` dance. Reducer returns `ReducerLog`;
   diagnostic dump reads from both.
5. **Promote the fallback panics in [fz-rcp.5][rcp5] to `.expect()`s.**
   With the invariant in place, "missing dispatch" is structurally
   unreachable.
6. **Drop the any-key blanket seed.** The fz-aiz.7 win finally
   lands — significant golden shrink, faster compiles.

Each step independently green; each step shrinks the surface area;
the final state has none of the long-standing complaints and a
much smaller codegen.

## Why this is beautiful

CLAUDE.md asks: *what am I not proud of?* The current dispatch
story has several things to not be proud of: codegen reimplementing
typer logic, an any-key floor that exists only because the
reimplementation might miss, a closure body picker whose fallback
exists only because the floor might fire when it shouldn't, a
cont ABI scan that re-derives information the typer has.

The proposed design replaces all of it with a single sentence's
worth of contract: *the typer is the authority; codegen reads.*
The IR is frozen during the read window so there's nothing to
drift against. Each fact in the compiler has one home. Mutability
is bounded in space (per-pass) and time (within the pass's lifetime).

Beauty in compilers is structural: the code reads top-to-bottom
and the reader can tell, by where they are in the pipeline, what's
allowed to change and what's already settled. This design earns
that beauty by enforcing a phase boundary the codebase has been
inching toward for years.

## Where to look in the code

- Pipeline order: `src/ir_codegen.rs:1871–1923` (`compile_with_backend`).
- The typer's discovery walk: `src/ir_typer.rs:1206–1530`
  (`walk_spec_for_discovery`).
- The projection that loses caller-spec dimension:
  `src/ir_typer.rs:705–731`.
- The current side-table dance: `src/ir_typer.rs:753–782`
  (`apply_callsite_outcomes`).
- The two codegen dispatch sites already migrated:
  `src/ir_codegen.rs:3988–4022, 4036–4068` (fz-rcp.5).
- `inline_single_use_conts` (the pass to move pre-typer):
  `src/ir_inline.rs:563–745`.

## Footnotes

[^spec-key]: Internally, a spec is identified by the pair
    `(FnId, Vec<Descr>)`. The `Descr` is fz's type-axis lattice
    value. See `src/types.rs` for the lattice; `src/spec_registry.rs`
    for the registry that maps these pairs to numeric `SpecId`
    handles used for codegen-time indexing.

[^panic-history]: The `.29.x` family of panic strings in
    `src/ir_codegen.rs` (`.29.11`, `.29.12.1`, `.29.12.2`) are
    different shapes of "codegen's resolve query found no matching
    spec." Each was the lived experience of the
    two-analyses-disagree problem. The fz-aiz branch (unmerged) and
    fz-rcp epic (mostly merged) chipped away at them; this design
    retires the class.

[^pipeline-now]: Sketched at a high level; the real pipeline has a
    few more passes (`ir_const_bs`, two `ir_dce` calls, etc.) that
    don't affect the argument. See the companion doc's audit table
    for the full list and which mutations each performs.

[^inline-gating]: Verified by reading `inline_single_use_conts_once`
    at `src/ir_inline.rs:563`. All checks count references, inspect
    terminator kinds, look for `Receive`, or check structural
    properties. The function takes `&mut ModuleTypes` solely to
    maintain type info after the inlining (clean up dead specs from
    `mt.specs`); no decision logic reads it. Move it pre-typer and
    the parameter deletes.

[^post-typer]: `ir_fold` folds `BinOp` / `TypeTest` prims and
    `If` terminators when the typer's view says they're singletons.
    `ir_branch_fold` folds `If` to `Goto` when one branch is dead.
    `ir_dce` deletes unreachable blocks (which may include dead
    dispatches — but a dead dispatch reading is itself dead, so
    harmless). None mutate call-shaped terminators. The post-typer
    epoch's only legal mutations are: prim folds, If folds, block
    deletions.

[^callsite-outcomes-field]: The reducer's writes (`Consumed`,
    `Stalled`) split out into a new `ReducerLog` returned from
    `reduce_module`. The typer's writes (`Emitted`) move onto
    `FnTypes.dispatches`. The `Inlined` variant of `CallsiteOutcome`
    has no current writer in the searched code — if it's used by
    some path I didn't find, it routes through whatever pass owns
    inlining, similarly to the reducer.

[^rcp-tickets]: The five tickets — MakeClosure picker port,
    closure_shapes port, tagged_slot0_cont_specs port, outcome
    freshness across mutations, fz-aiz.7 seed drop — were filed as
    separate follow-ons because they looked independent. Under this
    design they're symptoms of one cause, fixed by one arc.

[^dps-epic]: Destination-passing style is tracked in the `fz-q9g`
    epic ("fz-dps: destination-passing codegen + hybrid GC
    foundation"). At the time of writing, DPS work is sequenced
    after the dispatch refactor — partly because the natural home
    for DPS plans is the same `FnTypes` structure dispatch wants.
    See `bw show fz-q9g`.

[^dual-identity]: It is tempting to unify `EmitSlot` and `AllocSlot`
    into one giant `Slot` enum, since they share `(fn, block,
    stmt_idx)` and `MakeClosure` would appear once. Resist that
    temptation. Terminator-position slots (`Direct`, `Cont`,
    `ClosureLit(i,j)`, `CallClosureKnown`) and stmt-position slots
    (`Tuple(i)`, `Cons(i)`, …) are structurally different —
    terminators carry multiple slot kinds at one position
    (a `Term::Call` is both a `Direct` and a `Cont`), stmts carry
    one allocation per stmt. Unifying forces "which slots are valid
    at which positions" into documentation. Two coherent types
    keep it in the type system.

[^lattice-roots]: The terminal-plan set is small and worth keeping
    explicit, since any future plan kind added to `AllocPlan` either
    terminates a chain (joins this list) or references another alloc
    (extends the chain). If a future kind does neither — references
    something outside the alloc graph — the invariant catches it
    immediately: the planner's reverse-dataflow walk has nowhere to
    start. Growing the set is conscious; ungrowable plans are
    self-flagging.

[rcp5]: https://github.com/jallum/fz/pull/23
