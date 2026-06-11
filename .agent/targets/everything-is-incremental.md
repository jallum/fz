# Pull-Based Compiler2: Dissolve the Pass Barriers, Accumulate the Products

## Context — why

`qsort.log` telemetry showed the work graph behaving like a pass-based compiler wearing
an incremental costume:

- **Demand facts** (`Activation`, `Executable`, `RootEntry`) are scheduling signals routed
  through the fact table. Their content is their key; they exist only to wake
  `SealSemanticClosure`.
- **`SealSemanticClosure`** is a global sweep: woken by *every* intermediate fact change,
  it re-walks the whole frontier each time — 15 runs for 5 activations on quicksort.
  O(N²) by construction (root.rs:68-259 reads every `CallSiteSummary`/`ActivationAnalyzed`/
  `ReturnType` in the closure).
- **The snapshot ladder** (`MaterializedProgram → AbiReadyProgram → EmissionReadyProgram →
  BackendProgram → NativeProgram`) freezes the closure into a monolith, then derives four
  more monoliths. Every rung is a whole-program pass that exists *only* because its input
  is a snapshot (up-front FnId allocation, up-front atom collection, emission index sorting
  all exist solely to convert HashMap snapshots into stable order).

**The inversion:** products are world-owned **accumulations grown monotonically by
per-executable jobs** — like the `FunctionDefined`/`ModuleDefined` stores. Demand flows by
direct `follow_up` chaining from the entry executable outward; identity (executable ids,
FnIds, atom ids) is interned on first demand; `drive() == Resolved` is the completeness
proof, already checked at every surface call site (compiler.rs:73-88). Nothing assembles,
because nothing was ever disassembled.

**The model is a spreadsheet engine, not a pass-driven compiler.** The world is not a
cache of some authoritative build — the facts *are* the program state, and they change
when their dependencies change. `drive()` is the recalc: propagation runs exactly along
the dependency edges that observed a change (`changed=false` is the propagation cutoff,
not a cache-hit optimization), and unchanged facts never participate. When the fact graph
reaches executable code, "source changed" is just a cell edit: watch mode, REPL, and
incremental JIT are the *same operation* as the first build — propagation to quiescence.
`cranelift-jit 0.131`'s `finalize_definitions()` drains a batch queue, callable repeatedly
(verified in crate source) — additive incremental codegen is natively supported.
Redefinition is not (no hotswap in 0.131); mutation v1 = fresh `JITModule` over the live
IR accumulation (only codegen re-runs; the fact state upstream is already current).

## Goal / Signal / Strategy

- **Goal:** every compiler2 job is per-key work chained by demand; liveness is
  retraction-defined (the claimed set at quiescence *is* the program); the only
  whole-program operations left are (a) `drive()` itself and (b) Cranelift finalize
  batches. Watch-mode demo: edit a fixture → only the affected subgraph re-runs →
  program re-executes.
- **Signal:** telemetry. Per-job-kind run counts (seal 15→0 on quicksort; no job kind
  super-linear in activations), deterministic id assignment across identical runs, fixture
  matrix green, heap/spec counts unchanged.
- **Strategy:** convert the ladder bottom-up-from-semantics, one rung per ticket. Each
  ticket dissolves exactly one rung and rewrites exactly one **named bridge job** (the next
  rung down, temporarily consuming per-executable facts by pulling claim edges) — so
  every ticket lands green with no parallel mechanisms, and each bridge is deleted by the
  next ticket.

## Target architecture

### Identity (interned on first demand — same table-owned-counter move as fact revisions)
- `ExecutableId` — per-root dense intern of `ExecutableKey`. Replaces emission indices
  everywhere (interp call edges, callable entries, native fn mapping).
- `AtomDefined(name)` — fact; id = intern order at first publication. Replaces
  `collect_backend_atom_names` (backend.rs:972) and `NativeLowerer.atom_ids`.
- `FnId` — per-root intern keyed by lowering role (executable entry / clause helper /
  control entry / callable identity), assigned when first demanded. Replaces the up-front
  `fresh_fn_id` loops (native.rs:125-139).

### Per-executable facts (keyed by ExecutableId; jobs chained by follow_up)
| Fact | Job | Notes |
|---|---|---|
| `ExecutableMaterialized(E)` | `MaterializeExecutable(E)` | pruned body, **edges = callsite edges + latent edges** (`analysis.latent_executables`, need=Value — extern-boundary callables, semantic.rs:748-762), dispatch; waits on `ActivationAnalyzed`/`ReturnType`/`CallSiteSummary`/`LoweredBody`/`EntryDispatch`; computes callsite needs and follow_ups callee + latent `MaterializeExecutable` — this replaces the seal's BFS. Reads-based re-wake retargets edges when summaries change (scheduler wakes subscribers of changed facts, scheduler.rs:100-107). |
| `ExecutableEffects(E)` | same job | monotone: publish local effects immediately, union callee effects as their facts appear/change; `EffectSummary` is a finite bool lattice (artifact.rs:492-512) → converges; **no waits on callees** (publish-first; "unknown is not none") |
| `ReturnAbi(E)` + `ExecutableAbi(E)` | `DeriveExecutableAbi(E)` | extern/TupleFields settle eagerly (as today). Value-need derives from callee `ReturnAbi` via waits — but **cycle rule is discovery-order, not `Recursive`**: an edge whose callee `ExecutableId` ≤ caller's takes the conservative `ValueRef` ABI instead of waiting. Every cycle contains such an edge, so no deadlock; matches today's "stall → conservative_return_abi" outcome (artifact.rs:867-876) deterministically. (`Recursive` is unsound here: keying's static graph ignores closure/protocol/named edges, keying.rs:102-104, 218-227 — cycles exist with no member marked Recursive.) |
| `BackendExecutable(E)` | `LowerBackendExecutable(E)` | backend-form body; publishes `AtomDefined(name)`, `TupleArityUsed(n)`, struct-schema facts |
| (module entry) | `AddExecutableToModule(E)` | lowers into the root's accumulating `ModuleBuilder`; interns FnIds; registers callable identities + extern decls; fn replaced in place on change (fn_idx keyed by FnId) |

### Liveness: claims + retraction cascade — never enumeration
A caller's edges are **claims** on its callee executables (multi-publisher facts, the
machinery the fact table already has). When a widened `CallSiteSummary` retargets a call
edge to a new `ExecutableKey`, the caller's re-publication drops the old claim; the last
claim's retraction wakes exactly the orphaned executable's job, which re-runs, finds no
demand, publishes nothing — dropping *its* claims and unraveling the subtree by local
propagation. When the graph settles, the claimed set **is** the final set. No walk, no
sweep. (This is claims-as-liveness-data; scheduling still chains by follow_up — the
disease in today's demand facts was the global sweep they woke, not the claim.)

Two rules make this sound:
1. **Self-claims excluded** — a job never counts as a demander of its own key (otherwise
   every self-recursive function keeps itself alive after orphaning).
2. **Nothing ever enumerates the table** — every consumer pulls by key along edges.
   Mutual-recursion cycles (f claims g claims f) defeat refcounts — inherent; spreadsheets
   solve it by forbidding cycles, we can't — so orphaned cycles persist as facts. They are
   harmless *because* no consumer can reach them. The one enumerator in the system today
   is interp callable dispatch (`resolve_backend_callable_executable` scans + filters
   callable entries, ir_interp/backend.rs:1201-1265 — the source of false "ambiguous"
   errors from stale entries). It is replaced by **construction-site resolution**: a
   closure value carries the executable identity resolved when its `Lambda`/`FunctionRef`
   step was analyzed (native lowering already carries `callable_constructors`); dispatch
   becomes keyed lookup.

Orphaned cycles are then a pure memory leak (dead facts, dead fns in the module) — arc-E
ships a tracing cycle collector that is honestly a GC (file-compact, not recalc); its
timing can never affect behavior.

Transitional note: bridge jobs (B1/C1/C2) feed the surviving snapshot consumers by pulling
claim edges from the entry executable — keyed pull, not table enumeration — and die with
their rung.

### Back-edge classification (yield checks)
`annotate_back_edges` (whole-module Tarjan over emitted TailCalls, native.rs:1931-2010)
dissolves. Per-edge rule: callee `ExecutableId` ≤ caller's ⇒ yield check. Pure
over-approximation (every cycle has such an edge; some forward edges get a spurious
check); never under-approximates like a `Recursive`-based rule would (closure/protocol
cycles → zero yield checks → runtime livelock). Precision ticket at epic end, justified by
telemetry or closed.

### Identity permanence & fresh-world reproducibility
Ids are names of world cells: minted once at first reference, never reassigned. Facts
about an id activate, deactivate, and change revision; the identity is permanent. So
drive-over-drive stability (watch, REPL, JIT re-drives in one world) is inherent to
interning — nothing to engineer, no sorts needed.

The one residue is **fresh-world reproducibility**: a new process over the same source
must mint the same ids (AOT byte-reproducibility, cross-process comparison; also keeps
the discovery-order cycle rule's ABI choices identical run-over-run). First-demand order
= scheduler execution order, so discovery must be deterministic. Three HashSet-order
leaks, fixed once in A1:
1. Job-local `HashSet` accumulation of `follow_up`/`waits` (34 sites in jobs/*.rs) →
   insertion-ordered dedup.
2. Scheduler wake order: `DependencyIndex` subscriber/waiter sets and the fact-table
   `touched` set iterate HashSet-ordered (deps.rs:86-98, facts.rs:92-99) →
   insertion-ordered sets.
3. Type-intern order: HashMap iterations that call `types_mut()` (`merge_value_types`
   semantic.rs:777-789; alpha-normalization world.rs:312-315) → sort by `ValueId` first.

### Convergence & completeness
No `SemanticClosed`, no seal. `DriveOutcome::Resolved` (agenda empty + no unresolved
waits, drive.rs:135) is the completeness proof. Fixpoints ride the existing
publish-then-refine pattern (`ReturnType` precedent, semantic.rs:158-159).

## What gets ripped out

- **FactKeys:** `Activation`, `Executable`, `RootEntry`, `SemanticClosed`,
  `MaterializedProgram`, `AbiReadyProgram`, `EmissionReadyProgram`, `BackendProgram`,
  `NativeProgram`.
- **Jobs:** `SealSemanticClosure`, `MaterializeRoot`, `DeriveAbiReady`,
  `DeriveEmissionReady`, `LowerBackendProgram`, `LowerNativeProgram` (each as bridge
  first, then deleted).
- **Code:** `seal_semantic_closure` (root.rs:68-259), `SemanticClosure` +
  historical `DependencySnapshot` + `semantic_closure_is_current` + `wait_for_fresh_closure`
  (deleted by `fz-rh2.18.1`),
  `settle_effects` + `settle_return_abis` (artifact.rs:696-890), emission-index machinery
  (artifact.rs:192-267), `collect_backend_atom_names` (backend.rs:972-1071),
  `NativeLowerer` up-front allocation (native.rs:109-199), `annotate_back_edges`, the five
  snapshot structs + their `RootProjectionMap`s, whole-module codegen pre-passes
  (native_codegen/driver.rs:1072-1089) and positional `frame_sizes`.

## Ticket DAG (bw; one ticket = one commit, each lands green)

**Arc A — foundations**
- A1 `fresh-world-reproducibility`: all three fixes above (job-effect ordering, scheduler
  wake ordering, ValueId-sorted type interning). Test: two **fresh worlds** over identical
  source produce identical job-order telemetry and identical fact-publication sequences
  (quicksort fixture).

**Arc B — pull-based closure (kills the sweep)**
- B1 `executable-facts`: `ExecutableId` intern; `MaterializeExecutable(E)` +
  `ExecutableMaterialized(E)`/`ExecutableEffects(E)` facts (latent edges included),
  chained from `SeedRoot` outward; callers publish claims on callee executables
  (self-claims excluded), orphaning retracts and cascades. **Bridge:** `MaterializeRoot`
  rewritten — bootstraps like seal (RootEntry/FunctionDefined waits +
  `require_activation_key_facts` to compute the entry key), then pulls claim edges from
  the entry over `ExecutableMaterialized` facts (waits on missing with follow_up) and
  assembles `MaterializedProgram` for the untouched `DeriveAbiReady`.
  **Deleted:** manual seal freshness machinery, `settle_effects`, `DependencySnapshot`.
  Includes the seal-observing test estate rewrite (`SemanticClosedCapture` + ~10 tests +
  by-name assertions, drive_test.rs:799-929, 2400-2405, 4340-4996, 6210-7024). This is
  the epic's largest commit — budgeted as such.
- B2 `demand-fact-excision`: delete `Activation`/`Executable`/`RootEntry` FactKeys and all
  publications; `already_present` → intern presence; **`activation_inputs` rewired** to
  world-side activation interning (today it gates on the Activation fact, world.rs:298-301 —
  without rewiring every analysis silently no-ops), intern performed in
  `canonical_activation_key` so demander and analyzer agree. Test: zero demand-fact
  publications; analysis runs == activations + genuine type-driven re-wakes.

**Arc C — per-executable pipeline (each ticket: dissolve one rung, rewrite one bridge)**
- C1 `abi-facts`: `DeriveExecutableAbi(E)` with the discovery-order cycle rule.
  **Bridge:** `LowerBackendProgram` rewritten to consume per-executable ABI facts by
  pulling claim edges from the entry; callable-entries derivation (today inside `derive_abi_ready`,
  artifact.rs:1438-1451) moves into this bridge. **Deleted:** `MaterializeRoot`,
  `MaterializedProgram`, `DeriveAbiReady`, `AbiReadyProgram`, `DeriveEmissionReady`,
  `EmissionReadyProgram`, `settle_return_abis`.
- C2 `backend-facts`: `LowerBackendExecutable(E)`; `AtomDefined`/`TupleArityUsed`/schema
  facts; accumulated backend view; interp surface reads it post-Resolved (ir_interp access
  is already index-by-usize, mechanical rekey). **Construction-site callable resolution
  lands here**: closure values carry resolved executable identity; the
  `resolve_backend_callable_executable` scan is deleted. **Bridge:** `LowerNativeProgram`
  rewritten to consume the accumulated backend view. **Deleted:** `LowerBackendProgram`,
  `BackendProgram`, `collect_backend_atom_names`, the callable-entry scan.
- C3 `module-accrual`: `AddExecutableToModule(E)` into the per-root `ModuleBuilder`;
  FnId/callable-identity/extern interning; discovery-order back-edge rule; retraction
  removes a fn from the module when its executable is orphaned; JIT/AOT surface consumes
  the accumulated module post-Resolved. **Deleted:**
  `LowerNativeProgram`, `NativeProgram`, `annotate_back_edges`, up-front allocation phase.
  Quicksort telemetry re-measure vs the qsort.log baseline lands here (valid only once the
  bridges are gone).

**Arc D — codegen & live products**
- D1 `codegen-fact-feeds`: tuple/struct schemas + frame sizes from facts (FnId-keyed map,
  not positional Vec); codegen consumes registries instead of whole-module walks.
- D2 `jit-accrual`: per-root `JitModuleState` — declare on first reference, define as
  bodies land, batched `finalize_definitions` on execution demand. Additive incrementality
  (REPL: new function → define + finalize batch, no rebuild).
- D3 `code-resubmission`: world accepts changed source for an existing code identity;
  republication with changed=true cascades; retraction for vanished definitions
  (`submit_code` is append-only today, world.rs:187-203). Test: edit → redrive → telemetry
  proves only the affected subgraph re-ran.
- D4 `watch-mode`: CLI file watcher → resubmit → drive → fresh `JITModule` codegen (v1
  mutation story) → rerun. Demo + guide. AOT byte-compare determinism test lands here.

**Arc E — debt (filed at epic end, explicitly)**
- E1 cycle-collecting GC: trace claim edges from live roots, retract orphaned
  mutual-recursion clusters (memory + dead-fn reclamation only; correctness never depends
  on it — no consumer can reach unclaimed facts).
- E2 per-function redefinition (own GOT-style indirection; runtime bakes code addresses
  into `static_closure_targets`/continuations/`fn_ptrs` at finalize).
- E3 back-edge / conservative-ABI precision, justified by telemetry or closed.

## Verification

- TDD per ticket; tests observe telemetry (drive_test capture-handler pattern) and state
  intent: "materialization runs once per executable", "stable republication wakes nobody",
  "atom ids identical across identical drives", "orphaning an executable retracts its
  facts and cascades through its claims".
- Fixture matrix + lib suite `0 failed`, zero warnings, fresh uniquely-marked runs before
  every commit.
- Quicksort job-kind counts vs qsort.log baseline at C3 (seal 15→0; totals strictly down).
- A1: fresh-world telemetry equality. D4: AOT object byte-compare across fresh worlds.
- D3: edit-cascade test counts re-run jobs against the touched subgraph.

## Docs
- `.agent/docs.md`: compiler2 work-graph section rewritten (present-tense: pull chaining,
  accumulations, identity interning, retraction-defined liveness, drive-Resolved contract).
- Guides: watch mode / REPL incremental story (D4).
