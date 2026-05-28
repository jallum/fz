# Reduction Yielding Review Gate

## Goal

Make the reduction-driven yielding work correct by construction before treating
`fz-dz9` as ready to build on. The gate closes only when the five review
findings have executable acceptance checks and those checks pass in the normal
test suite.

## Signal

- Allocation pressure must expire the same budget cell that the active execution
  mode spends.
- JIT and AOT must report process reduction telemetry from the budget cell their
  generated code actually decrements.
- The continuation reserve must be either proven conservative for the emitted
  yield slow path or honestly exposed as a soft watermark with telemetry that
  measures the full slow-path allocation cost.
- `quiet_quanta` must mean scheduler-boundary quanta consistently across
  compiled, AOT, and interpreted execution.
- Heap-stat telemetry must separate ordinary budget exhaustion from
  allocation-pressure-triggered mid-flight yields.

## Strategy

The gate is intentionally split by contract boundary, not by file. Each child
ticket gets one failing acceptance check first, then the smallest runtime or
codegen change that makes the check pass. Do not merge these fixes into a broad
cleanup commit: each ticket should leave one crisp commit and close one review
finding.

## Gate Acceptance

The parent gate closes when all child tickets are closed and these checks pass:

- `cargo test reduction`
- `cargo test quiet_quanta`
- `cargo test --test fixture_matrix process_heap_stats`
- `cargo test`

## Plans

### 1. Interpreter allocation pressure spends the process budget

Goal: allocation pressure must make an interpreted process yield at the next
back edge without waiting for its normal budget to run out.

Current state: `Heap::alloc()` expires `fz_runtime::reductions`, but the
interpreter spends `Process.reductions_remaining` directly. The interpreter
scheduler only consumes runtime yield reasons after `InterpStep::Yielded`, so
allocation pressure can be latent until ordinary budget exhaustion.

Plan:

1. Add a test that sets a large interpreter quantum, forces the heap allocation
   watermark to trip, and proves the process yields/GCs before the large quantum
   would naturally expire.
2. Route interpreter back-edge spending through the same process/runtime sync
   boundary used by allocation pressure, or make `Process::spend_reductions`
   observe pending runtime expiration before decrementing.
3. Keep the interpreter hot path to one cheap branch and avoid adding allocation
   checks outside back edges.
4. Verify that allocation pressure sets the GC reason and that the scheduler
   clears it after boundary maintenance.

Acceptance check:

- A new interpreter test fails on the current branch because allocation pressure
  does not cause an early yield, and passes after the fix.

### 2. AOT reads the budget cell AOT decrements

Goal: AOT ordinary reduction yields must leave correct process telemetry.

Current state: AOT links generated code to exported
`FZ_REDUCTIONS_REMAINING`, but `Process::sync_reduction_budget_from_runtime()`
reads the JIT thread-local cell. The AOT code can still yield, but telemetry can
misreport `reductions_remaining` and `reductions_executed`.

Plan:

1. Add an AOT acceptance test that runs an allocation-light loop under a tiny
   quantum and asserts nonzero `reduction_yields` and nonzero
   `reductions_executed`.
2. Split the runtime budget API so sync can read the cell selected by the
   execution mode, or make AOT bind the same thread-local cell that sync reads.
3. Keep JIT's direct pointer binding intact; do not introduce an indirect call
   on compiled back edges.
4. Add a small unit test for the budget API so future JIT/AOT storage changes
   cannot drift silently.

Acceptance check:

- AOT heap/process stats for a tiny-quantum allocation-light loop show
  `reductions_executed > 0` and `reduction_yields > 0`.

### 3. Continuation reserve is measured against full slow-path cost

Goal: the heap reserve policy must cover the actual continuation materialization
work needed to hand a runnable closure to the scheduler, or the docs and
telemetry must stop claiming that it guarantees that.

Current state: the fixed `YIELD_CONTINUATION_RESERVE_BYTES` is 256 bytes and
telemetry records only the final continuation closure object size. The slow path
may also box scalar captures and materialize a continuation value.

Plan:

1. Add a compiled acceptance test that forces allocation pressure with a
   continuation shape containing scalar captures and a nontrivial continuation,
   then asserts the recorded margin never goes negative or unmeasured.
2. Measure full slow-path allocation delta, not just the closure object size.
3. Decide from observed maximum and emitted shape whether the reserve can be a
   conservative formula or should be documented as a soft watermark.
4. If the reserve remains fixed, encode the bound in one helper with tests for
   expected closure/capture shapes.

Acceptance check:

- A test observes full yield slow-path allocation bytes and asserts the minimum
  after-yield margin is positive for the worst continuation shape covered by the
  current compiler.

### 4. `quiet_quanta` is scheduler-boundary state

Goal: `quiet_quanta` must mean the same thing in interpreter, JIT, and AOT
schedulers: scheduler quanta completed without boundary GC.

Current state: the interpreter increments `quiet_quanta` inside the back-edge
hot path, so a long interpreted loop can inflate the value before the scheduler
boundary runs.

Plan:

1. Add an interpreter test with a tiny reduction quantum and assert
   `quiet_quanta` changes only when the scheduler handles the yielded process.
2. Remove `quiet_quanta` mutation from `ir_interp::run`.
3. Keep quiet-quanta updates centralized in scheduler post-step/post-quantum
   branches.
4. Re-run existing compiled quiet-quanta tests and add an interpreter analogue
   if one does not already cover the boundary behavior.

Acceptance check:

- Interpreted reduction-yield loops increment or reset `quiet_quanta` only in
  scheduler boundary code, never per back edge.

### 5. Yield telemetry separates cause from mechanism

Goal: heap/process stats must distinguish ordinary reduction exhaustion from
allocation-pressure-triggered yields, even though both use the same scheduler
mechanism.

Current state: `fz_yield_mid_flight()` always calls `note_reduction_yield()`.
That makes `reduction_yields` mean "mid-flight yield via reductions machinery",
not "ordinary budget exhaustion" as documented.

Plan:

1. Add telemetry assertions for two cases: pure budget exhaustion and
   allocation-pressure expiration.
2. Split counters or rename the existing counter so cause and mechanism are not
   conflated. Prefer additive telemetry to preserve existing user-facing stats
   unless a rename is unavoidable.
3. Ensure `yield_reasons` remains a bitfield for boundary decisions, while
   cumulative counters expose cause-specific totals.
4. Refresh only the affected fixture baselines after the contract is explicit.

Acceptance check:

- A pure loop increments ordinary reduction exhaustion telemetry.
- An allocation-pressure yield increments allocation-pressure telemetry without
  being counted as ordinary reduction exhaustion.
