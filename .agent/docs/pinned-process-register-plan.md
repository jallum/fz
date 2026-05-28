# Pinned Process Register Plan

Goal: make compiled code use a Cranelift pinned register as the base pointer for
the current `Process`, then remove the compiled reductions/yield-reason hot path
from thread-local mirror cells.

Signal: compiled back-edge CLIF reads and writes `Process.reductions_remaining`
through `get_pinned_reg`, no longer references the reductions global/data
symbol, and JIT/AOT/interpreter reduction, allocation-pressure, quiet-quanta, and
fixture suites continue to pass.

Strategy: keep phase one narrow. Pin `Process*` for generated code, preserve the
existing Rust `CURRENT_PROCESS` TLS for runtime helpers, and only move the
already-proven compiled reductions path onto direct `Process` offsets. Heap fast
paths and Rust helper TLS removal are follow-ups after the mechanism is proven.

## Current facts

- The repo uses Cranelift `0.131.1`.
- Cranelift has an `enable_pinned_reg` ISA setting.
- With that setting enabled, CLIF can use `get_pinned_reg` and
  `set_pinned_reg`.
- The pinned register is architecture-selected, not caller-selected:
  - x64: `r15`;
  - aarch64: `x21`.
- Cranelift removes the pinned register from normal allocation when enabled.
- The current compiled reduction path uses a process-independent reductions
  global/data cell. The scheduler installs that mirror state before running a
  process and accounting is reconciled later at the yield boundary.

## Non-goals for phase one

- Do not inline heap allocation yet.
- Do not replace Rust `current_process()` with pinned-register reads.
- Do not expose arbitrary `Process` layout to codegen.
- Do not delete the thread-local reductions/yield-reason module until compiled
  paths no longer depend on it and interpreter/runtime users have an explicit
  replacement.

## Design

Generated code should treat the pinned register as the current process base:

```text
p = get_pinned_reg.i64
remaining = load.i32 p + PROCESS_REDUCTIONS_REMAINING_OFFSET
remaining = remaining - 1
store remaining, p + PROCESS_REDUCTIONS_REMAINING_OFFSET
brgt remaining, 0, fast
```

The scheduler still installs Rust TLS before entering generated code, because
runtime helper calls still use `current_process()`. The new invariant is that
every Rust-owned generated-code call boundary also sets the pinned register to
the same `Process*` and restores Rust's host register before returning.

```text
CURRENT_PROCESS = process_ptr
save host_pinned_reg
host_pinned_reg = process_ptr
call fz_entry(...)
restore host_pinned_reg
```

This makes process switching cheaper and cleaner for compiled code: switching
processes changes one generated-code base pointer instead of synchronizing a
bundle of process-local mirror cells.

## Process ABI surface

Codegen must depend on a small explicit ABI, not on the whole Rust `Process`
layout. Add one runtime-owned module for generated-code offsets, likely
`runtime/src/process_abi.rs`, with constants such as:

```rust
pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 = ...;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 = ...;
```

Tests must assert each offset equals the actual Rust field offset. If this uses
a crate such as `memoffset`, add it deliberately and keep it scoped to these ABI
tests/constants.

Only fields listed in this ABI module are fair game for CLIF direct access.

## Entry coverage

Every SystemV-to-tail shim that can start or resume fz code must set the pinned
register before transferring control:

- main entry;
- spawn entry;
- scheduler resume closure entry;
- AOT entry/shim equivalents;
- destructor-drain entry if it invokes generated fz code under a process.

The safe first implementation is intentionally redundant: set the pinned
register in every scheduler-facing generated entry, then remove redundant sets
only if later measurement shows they matter.

## Ticket DAG

### pinned-process.1: enable and prove pinned register support

Goal: Cranelift JIT/AOT builders accept pinned-register CLIF and emit it on the
architectures we support.

Acceptance:

- ISA setup enables `enable_pinned_reg` for JIT and AOT.
- A focused codegen/CLIF test proves `set_pinned_reg` / `get_pinned_reg`
  verifies and appears in emitted CLIF.
- Existing compiled smoke tests still pass.

### pinned-process.2: define generated-code Process ABI offsets

Goal: generated code has a tiny, tested offset contract for process fields.

Acceptance:

- `PROCESS_REDUCTIONS_REMAINING_OFFSET` exists and is tested against actual
  `Process` layout.
- If phase-one direct yield-reason writes are included, add
  `PROCESS_YIELD_REASONS_OFFSET` with the same coverage.
- No codegen module hand-computes `Process` offsets.

### pinned-process.3: set pinned Process at scheduler entry boundaries

Goal: every generated-code entry sees the correct `Process*` in the pinned
register.

Acceptance:

- Main, spawn, resume, AOT, and destructor-drain entry paths enter generated
  code through Rust-owned call wrappers that save the host pinned register, set
  it to the scheduler-supplied/current `Process*`, call generated code, and
  restore the host register before returning to Rust.
- A native JIT test crosses at least one runtime helper call and then reads
  `get_pinned_reg`, proving the pinned register survives ordinary helper calls
  while the wrapper preserves Rust's ABI at the scheduler boundary.
- Existing scheduler, receive, spawn, and AOT fixture tests pass.

### pinned-process.4: spend compiled reductions through pinned Process

Goal: compiled back edges mutate `Process.reductions_remaining` directly.

Acceptance:

- Back-edge CLIF contains `get_pinned_reg`.
- Back-edge CLIF no longer references the reductions global/data symbol.
- JIT and AOT pure reduction-yield tests pass.
- Boundary accounting still reports signed remaining reductions and burned
  reductions correctly.

### pinned-process.5: remove obsolete compiled reductions mirror plumbing

Goal: delete the compiled-only reductions global/data wiring made unnecessary by
the pinned process base.

Acceptance:

- `reductions_remaining_data_id` and compiled references to the reductions
  global are gone, unless a remaining non-compiled user is documented.
- Thread-local reductions support remains only for paths that still genuinely
  need it.
- `rg` checks prove no stale compiled global plumbing remains.
- Full suite passes.

## Follow-up guideposts

After phase one lands, the next natural plans are:

- inline compiled heap bump allocation from pinned `Process.heap`;
- move allocation-pressure yield-reason writes directly into generated code
  when allocations are codegen'd;
- reduce or remove Rust TLS `CURRENT_PROCESS` only where helper boundaries can
  read process state without target-specific fragility;
- collapse any remaining temporary thread-local reductions scaffolding with
  removal tickets.
