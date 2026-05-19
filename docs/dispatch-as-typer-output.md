# Dispatch as Typer Output — Design Note

Status: **stress-test pre-implementation**. Working through concrete
language examples on paper to see whether the proposed
"typer-is-authoritative" rework holds up under realistic shapes.
The goal is to surface latent ambiguity *before* writing any code,
not to ratify a design.

## The thesis being tested

> One source of truth per piece of information. When that information
> is mutable, multiple representations invite trouble. Today, the
> dispatch decision at each call site is represented in several places
> (the IR, `module.callsite_outcomes`, `spec_registry`'s lookup, and
> codegen's flow-narrowed re-derivation) and at least one of those
> representations becomes stale under post-typer IR mutations.

The proposed shape: the typer is the *only* writer of dispatch
information; it lives per-spec on `FnTypes.dispatches`; codegen reads
it; everything else (any-key floor, resolve fallback, closure body
picker logic, cont ABI scan) deletes.

This doc walks through four concrete worries with hand-traced
examples. Each section: what the worry is, a small fz program that
exhibits the shape, what happens today, what would happen under the
proposal, verdict.

---

## Worry 1: `inline_single_use_conts` and "structural vs type-driven" inlining

### What the worry is

The proposal moves `inline_single_use_conts` from *after* the typer to
*before* it. The justification is that all its gating conditions are
structural (count callers, check for `Receive`, check for self-recursion)
— no type info needed.

But the pipeline today is:

```
… reduce → type → branch_fold → fold → dce → inline_single_use_conts → dce …
                  ───── post-typer mutations that affect structure ─────
```

`ir_branch_fold` collapses `Term::If` to `Term::Goto` when the cond
is statically true/false under the typer's view. That can eliminate
an entire branch, which **changes the structural count of references
to a cont fn `K`**. If `K` was referenced from both arms of an `If`
and one arm folds away, `K` becomes structurally single-use *after
branch fold*. Pre-branch-fold, it isn't.

So moving `inline_single_use_conts` pre-typer loses some inlining
opportunities — the ones that become structurally single-use only
after type-driven branch folding.

### Concrete example

```fz
fn step(x), do: x + 1

fn dispatch(flag, x) do
  if flag do
    step(x)         # k_then is the continuation; calls print(result)
  else
    step(x)         # k_else is a SEPARATE continuation
  end
end

fn main(), do: print(dispatch(true, 41))
```

`dispatch` is lowered to roughly (sketching the IR):

```
fn dispatch(flag, x):
  blk0:
    if flag → blk1 else blk2
  blk1:                            # then-arm
    call step(x) → k_then(_, ...)
  blk2:                            # else-arm
    call step(x) → k_else(_, ...)

fn k_then(result, ...):  # ← gets the step(x) result, hands to outer cont
  …
fn k_else(result, ...):  # ← same shape, different identity
  …
```

Two distinct cont fns (`k_then`, `k_else`). Each is referenced
exactly once.

Now `main` calls `dispatch(true, 41)`. The typer narrows `flag :: true`
within `dispatch`'s spec for that call site. `ir_branch_fold` sees
`if true → blk1 else blk2`, folds to `goto blk1`. Block `blk2`
becomes unreachable. The reference to `k_else` from `blk2` is gone.

After folding + DCE:
- `k_then` has 1 reference (from `blk1`). Single-use. Inline candidate.
- `k_else` has 0 references. Dead. DCE removes it.

Both conts simplify away. Pre-folding, neither would.

This is the type-driven inlining win: a branch was folded *because*
of type narrowing, which made a cont structurally single-use, which
let it inline.

### What the proposal would do

Moving `inline_single_use_conts` pre-typer means it runs *before*
branch fold. At that point, `k_then` and `k_else` are both
structurally single-use (each referenced from one block), so the
pre-typer pass inlines them both. After type narrowing, branch fold,
and DCE, the result is the same — `blk2` was unreachable anyway, and
inlining `k_else` into a soon-to-be-dead block costs nothing.

**Wait — is that actually the case?** Let me trace more carefully.

`inline_single_use_conts` checks: "K is referenced by exactly one
`Cont` site, no direct calls, no back-edges, no Receive, no
self-references."

Before any folding:
- `k_then` referenced from `blk1` (Cont of `Term::Call(step, [x], Cont(k_then, …))`). Count = 1. ✓
- `k_else` referenced from `blk2` (same shape). Count = 1. ✓

So both inline pre-typer. Then the typer types the post-inline body
of `dispatch` (which now has `k_then`'s body spliced into `blk1`,
`k_else`'s into `blk2`). Branch fold then sees `if true → blk1
else blk2`, folds, DCE removes the dead block.

Same end state. The pre-typer inlining didn't lose anything.

### When would pre-typer inlining lose?

It would lose if cont folding **introduced** new single-use cases
that didn't exist before. Specifically: a cont `K` that's referenced
TWICE pre-fold but only ONCE post-fold. That happens when one of K's
references is in a branch that folds away.

```fz
fn helper(x), do: x + 1
fn pick(flag, x) do
  if flag do
    helper(x)        # cont kk for the helper call (call site #1)
  else
    helper(x)        # cont kk for the helper call (call site #2)
  end
end
```

Wait — in this shape, the two `helper(x)` calls have **different**
continuations (the cont captures which block we're returning to).
The lowerer mints distinct `k_N` per call site. So `kk` isn't a
shared cont; each `helper` call has its own. This is the same case
as the prior example.

Can two distinct call sites share a continuation? Only if the lowerer
explicitly merges them — e.g., a phi-style join after an `if`.
Looking at how the lowerer works: each call site mints its own
continuation. Joins happen via `Goto` to a shared block, not via
shared cont fns. So shared conts across branches don't happen in
practice.

### Verdict

The "moving pre-typer loses type-driven inlining" worry doesn't
materialize for `inline_single_use_conts`'s specific gating
(structural reference count). The lowerer mints distinct cont fns
per call site, so the post-fold reference count for any given cont
is either 0 (its branch folded away → DCE removes it) or 1 (its
branch survived → still single-use). Pre-typer inlining of every
structurally-single-use cont gives the same end state as
post-typer inlining of only the ones that *became* single-use.

**Concrete check that would seal it:** find or construct a fixture
where the cont fns are NOT distinct per call site, and verify the
result is unchanged. If no such fixture exists, the lowering
invariant "one cont fn per call site" makes this worry vacuous.

Open work: explicit invariant in `ir_lower`'s docs saying conts are
not shared across call sites, with a debug-build assertion. Once
that's in place, this worry is settled by construction.

---

## Worry 2: Can the typer populate `FnTypes.dispatches` per-spec without restructuring?

### What the worry is

Today the typer collects dispatch decisions in a side map called
`produces: HashMap<EmitterSite, (FnId, Vec<Descr>)>` where
`EmitterSite` carries the caller spec key. Then it projects away the
caller spec via `callsite_id()` and writes to
`callsite_outcome_updates: HashMap<CallsiteId, CallsiteOutcome>`.

The projection is where multi-caller-spec divergence collapses. The
proposal: don't project — store per spec.

The worry: is the current code structured such that we have
`&mut FnTypes` available when we discover a dispatch, so we can
mutate `dispatches`? Or does the discovery walk run in a context
that doesn't have mutable access to the spec being walked?

### Concrete example showing the multi-spec problem

```fz
fn classify(x) do
  if x > 0, do: :positive, else: :negative
end

fn double(x), do: x * 2

fn route(f, n), do: f(n)

fn main() do
  print(route(classify, 5))   # route called with f = classify
  print(route(double, 5))     # route called with f = double
end
```

`route` is called twice with different `f`. The typer produces two
specs for `route`:

- `(route, [&fn[classify], int_lit(5)])` — spec R₁
- `(route, [&fn[double],   int_lit(5)])` — spec R₂

Inside `route`'s single IR body, there's one `Term::CallClosure(f, [n], cont)`
at, say, `blk0` (slot `ClosureLit(0,0)` for the lit-resolved target).

Under R₁, the typer narrows `f` to closure-lit `classify`, so dispatch
target is `(classify, [int_lit(5)])`.
Under R₂, target is `(double, [int_lit(5)])`.

Same `CallsiteId = (route, blk0, ClosureLit(0,0))`. Different targets
per caller spec.

### What happens today

The typer's `walk_spec_for_discovery` is called per spec. For R₁ it
emits `EmitterSite{caller=R₁, …} → (classify, …)`. For R₂ it emits
`EmitterSite{caller=R₂, …} → (double, …)`.

Both go into `produces`. Then `produces_sorted` sorts (currently by
target key string) and writes to `callsite_outcome_updates`. The
deterministic sort means one target survives — say `classify` (sorts
before `double` alphabetically). `(double, …)` is silently overwritten.

At codegen, when compiling R₂'s body, codegen reads
`module.callsite_outcomes[(route, blk0, ClosureLit(0,0))]` and gets
`(classify, …)`. Wrong. The fallback to `spec_registry.resolve`
(landed in fz-rcp.5) catches it when the IR's closure operand
narrowing produces a different (closure-lit) target — but only
because resolve happens to re-derive correctly per caller spec.

The fallback is patching a structural hole. Without it, multi-spec
divergent dispatch is silently wrong.

### What the proposal would do

The typer walks R₁ and R₂ separately. For each, it has the spec's
`FnTypes` under construction. When it discovers a dispatch, it
writes directly into that spec's `FnTypes.dispatches[cid]`. No
projection, no collision.

```rust
specs.get_mut(&R1).unwrap().dispatches.insert(cid, (classify_fn, key));
specs.get_mut(&R2).unwrap().dispatches.insert(cid, (double_fn,   key));
```

Codegen iterates specs. While compiling R₂, it reads
`specs[R2].dispatches[cid] = (double_fn, key)`. Right answer, by
construction.

### Code-shape check

Looking at the current typer (`ir_typer.rs`):

- `walk_spec_for_discovery` produces a `WalkResult` containing
  `emits: Vec<(EmitterSite, (FnId, Vec<Descr>))>`.
- The driver integrates `WalkResult.emits` into the module-level
  `produces` map.

To move dispatches into `FnTypes`, the integration step changes from
"merge into `produces`" to "merge into `specs[caller_spec].dispatches`."
Same data shape, different destination.

The walk itself doesn't need restructuring. The mutation of FnTypes
happens at integration time, when the driver has `&mut specs`.

**Side question:** does codegen need a separate `produces`-like map
for any reason? Look at the current consumers of `produces`:
reachability BFS (in `type_module`'s prune phase), the
outcome-publishing loop. The reachability BFS walks
`produces[site] → target` and enqueues target specs. That logic
still works if we read `specs[caller].dispatches.values()` instead.
One indirection more; one structure less.

### Verdict

Mechanical restructure. The information flow is unchanged; the
storage location moves from a module-level side map to per-spec
inside FnTypes. The multi-caller-spec collision goes away because
the storage is naturally per-caller-spec.

**Open work:** confirm there's no place in the typer that *needs*
the cross-spec view of `produces` (e.g., "for each callsite, what
are ALL the dispatches across all caller specs"). The Wspec-quality
diagnostic might want this for its narrowing reports. If so, expose
it as a method that iterates `specs` rather than storing it
authoritatively.

---

## Worry 3: Other readers of `module.callsite_outcomes`

### What the worry is

If `Module.callsite_outcomes` is to be deleted, every reader must
have a migration path. The worry: are there readers we haven't
catalogued?

### Inventory (from grep)

| Site | Purpose | Migrates to |
|------|---------|-------------|
| `ir_codegen.rs:1908` `apply_callsite_outcomes` | Merge typer updates into module | Deletes — typer's output is authoritative |
| `ir_codegen.rs:4001, 4049` | Codegen reads for dispatch (fz-rcp.5) | `specs[caller_spec].dispatches[cid]` |
| `ir_typer.rs:802` `assert_every_emitted_has_provenance` | Debug invariant | Rewrites to walk `specs[k].dispatches` |
| `ir_typer.rs:2657` `Wspec-quality` (fz-rcp.6) | Diagnostic walker | Walks `specs[k].dispatches` |
| `ir_reducer.rs:140, 335, 351, 1339, 1386` | Writes/reads Consumed/Stalled | Returns `ReducerLog` from `reduce_module` |
| `main.rs:801, 832, 849` | `fz dump --emit outcomes` | Reads `ModuleTypes.dispatches` + `ReducerLog` |
| `fz_ir.rs:538, 697` | Field declaration + initializer | Deletes |

Six callers, four migration patterns. Three of the four (codegen,
diagnostics, dump) read; one (reducer) writes. The reducer's write
shape is fundamentally different from the typer's — it logs
"call eliminated" events, not dispatch decisions — so its data
naturally separates into a different output type.

### Concrete example illustrating the reducer/typer split

```fz
fn double(x), do: x * 2
fn maybe(flag, x), do: if flag, do: double(x), else: x
fn main(), do: print(maybe(true, 21))
```

Trace through the pipeline:

1. **Lower** → IR with calls to `maybe`, `double`, `print`.
2. **Reducer.** `maybe(true, 21)` — `flag` is `true`, `x` is `21`.
   `if true, do: double(21), else: 21` folds to `double(21)`. The
   reducer attempts to fold `double(21)` further; `double(x)` body
   is `x * 2`, returns `42`. Fold succeeds: `maybe(true, 21)` →
   literal `42`.

   Reducer log entries:
   - `Consumed { result: int_lit(42) }` at `(main, blk0, Direct)` —
     the `maybe` call.
   - `Consumed { result: int_lit(42) }` at `(maybe_inlined_…, …, Direct)`
     for the recursive `double` fold — except this is internal to
     the reducer's walk, not in the surviving IR.

3. **Typer.** Now the IR has `print(42)` at main; `maybe` and `double`
   are unreachable from main's surviving IR. Type module:
   - `main` spec `(main, [])` — dispatches its `print` call.
   - `maybe`, `double` — DCE'd eventually; specs may or may not be
     reachable depending on closure dispatches elsewhere.

4. **Codegen** reads `specs[(main, [])].dispatches[(main, blk0, Direct)]
   = (print, [int_lit(42)])`. Emits the call.

The reducer's Consumed log is **never read by codegen**. It's read
by `fz dump --emit outcomes` to print: "the `maybe` call at main:1
folded to `42`."

The typer's dispatches are read by codegen. They're a different kind
of fact.

Splitting them out:

```rust
// What the reducer produces.
pub struct ReducerLog {
    pub consumed: HashMap<CallsiteId, Descr>,
    pub stalled: HashMap<CallsiteId, StalledReason>,
}

// What the typer produces (with `dispatches` inside FnTypes).
pub struct ModuleTypes { /* … */ }

// Pipeline:
let log = ir_reducer::reduce_module(&mut module);
let mt  = ir_typer::type_module(&module);
codegen::compile(&module, &mt);       // reads mt only
diag::dump_outcomes(&module, &mt, &log);  // reads both
```

### Verdict

All readers migrate cleanly. The reducer/typer split clarifies what
each pass actually contributes: reducer reshapes IR + logs why;
typer infers types + chooses dispatches. Today's blended
`callsite_outcomes` table conflates them, which is why the data
model feels brittle.

**Open work:** the `Inlined { fn_id }` outcome variant — does any
pass write it today? If yes, identify its owner (probably the inliner)
and route it through that pass's log output similarly.

---

## Worry 4: Why in-band annotations on the IR don't work for shared IR

### What the worry is

The fz-aiz branch tried a different approach: add an `Option<SpecId>`
field directly on `Term::Call` and friends. The typer populates it;
codegen reads it. No side table.

My previous proposal rejected this in favor of `FnTypes.dispatches`.
Worth being explicit about why.

### Concrete example

```fz
fn id(x), do: x

fn apply_twice(f) do
  print(f(1))
  print(f(:foo))
end

fn main() do
  apply_twice(id)
end
```

`apply_twice` is called with `f = id`. Inside, two distinct
`Term::CallClosure` sites:

- Site A: `f(1)` — at `blk0` (say), `ClosureLit(0,0)`
- Site B: `f(:foo)` — at `blk1`, `ClosureLit(0,0)`

These are distinct IR nodes. The typer narrows `f` to closure-lit
`id` (since `apply_twice` is called only with `id`). Each site
dispatches to a different spec of `id`:

- Site A → `(id, [int_lit(1)])`
- Site B → `(id, [:foo])`

Each Term::CallClosure can carry an annotation pointing at its spec.
This case works for in-band annotations. So far so good.

### Where in-band annotations break down

Add another caller:

```fz
fn id(x), do: x

fn apply_twice(f) do
  print(f(1))      # IR node N₁
  print(f(:foo))   # IR node N₂
end

fn main() do
  apply_twice(id)
  apply_twice(fn(x) -> x)  # different lambda, structurally identical
end
```

Now `apply_twice` has TWO specs:

- Spec A: `f` is closure-lit `id`.
- Spec B: `f` is closure-lit `<anonymous lambda>`.

Inside `apply_twice`'s body, IR nodes `N₁` and `N₂` are the same in
both specs (shared IR). But under Spec A, `N₁` dispatches to
`(id, …)`; under Spec B, `N₁` dispatches to `(<lambda>, …)`.

If `N₁` carries a single `callsite_sid: Option<SpecId>` annotation,
which spec's answer does it hold? Can only be one. Wrong for the
other.

The branch's workaround was effectively to compile the body separately
per spec (codegen iterates specs and walks the body, reading the
annotation — but the annotation reflects the LAST spec the typer
processed). Empirically this worked because the branch's typer
visited specs in a specific order and the annotation got the "right"
spec by luck of ordering. Subtle, fragile.

To make in-band annotations correct for shared IR, the annotation
must be:

```rust
Term::Call {
    callee: FnId,
    args: Vec<Var>,
    continuation: Cont,
    dispatches_per_spec: HashMap<SpecKey, SpecId>,  // ← side table embedded in node
}
```

This IS the side table; it's just been moved inside the IR node. No
structural win.

### What the alternatives look like

Two clean shapes that handle the multi-spec case:

**(A) Shared IR + per-spec dispatch table (the proposal).**

```rust
struct FnTypes {
    // …
    dispatches: HashMap<CallsiteId, (FnId, Vec<Descr>)>,
}
```

Each spec has its own table. The IR is one shape. Codegen, when
compiling a specific spec, reads that spec's table.

**(B) Specialized IR (MLton-style).**

Each spec gets its own copy of the body, with calls already pointing
at concrete target specs:

```rust
struct SpecBody {
    spec_key: (FnId, Vec<Descr>),
    blocks: Vec<SpecBlock>,  // calls already concrete
}
```

No table at all. The IR *is* the dispatch decision.

(B) is cleaner at codegen but expensive at typing (N copies of each
body). (A) is the right middle ground for shared-IR pipelines: the
IR stays one shape, per-spec data lives per-spec, codegen reads by
spec.

### Verdict

In-band annotations only work when the IR is per-spec. For shared
IR (which fz uses, and which the reducer + inliner depend on), the
dispatch decision must live per-spec — in `FnTypes`, not on the IR
node.

The branch's approach was right in spirit (typer authoritative,
codegen reads) but wrong in placement (annotations on a node that
serves multiple specs).

---

## Summary of where stress-testing landed

| Worry | Resolved? | Open work |
|-------|-----------|-----------|
| 1. inline_single_use_conts type dep | Yes (structural-only) | Document the "distinct cont per callsite" lowering invariant + add debug-build assertion |
| 2. produces → dispatches restructure | Yes (mechanical) | Verify no remaining cross-spec consumer of `produces` |
| 3. Other callsite_outcomes readers | Yes (six callers, four migration patterns) | Identify the writer of `Inlined { fn_id }` (probably the inliner) |
| 4. In-band annotations vs shared IR | Yes (structurally incompatible) | None — settled by example |

None of the worries derail the proposal. Two (1 and 3) have small
follow-on diligence items that should land alongside the
restructure. The restructure itself is mostly mechanical — moving
data from a module-level side table into `FnTypes`, and splitting
out the diagnostic log.

## What this design is willing to commit to

Before any code lands, the design says:

1. The typer is the only writer of dispatch information. Reducer
   writes a separate diagnostic log; inliner (if it writes outcomes
   at all) also writes diagnostics.
2. Dispatch information lives per-spec on `FnTypes.dispatches`. One
   entry per `(spec, callsite)`.
3. Codegen reads dispatches; never resolves at dispatch sites.
4. All IR-shape-mutating passes happen before the typer. After the
   typer, only deletions (DCE) and orthogonal mutations (prim folds,
   if-folds) are allowed; nothing that changes call shape or
   reachability of dispatches.
5. `Module.callsite_outcomes` deletes. The dance between
   "typer publishes" and "module-side-table merges" is gone.

What it doesn't commit to yet:

- The exact home of `effective_returns` (cache or method) — perf
  question, not a correctness one.
- Whether `ir_fold` and `ir_branch_fold` move *into* the typer or
  stay as post-typer passes (they're orthogonal to dispatches
  either way).
- Whether `SpecId` survives as a codegen-time index or gets folded
  into direct `(FnId, key)` lookups (perf question).

These remaining questions are local optimizations of the codegen
boundary, not architectural shifts. The core thesis — typer is
authoritative, IR is frozen after typing, one representation per
fact — is what this stress test set out to validate, and the
worked examples confirm it holds.
