---
purpose: "fz-cty.6 — sending a >64-byte bitstring via spawn-and-send rounds through ProcBin/SharedBin under JIT and AOT"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 9
budget.codegen.instructions: 776
budget.specs.count: 8
budget.planner.worklist_pops: 8
budget.planner.walk_calls: 8
budget.planner.type_fn_calls: 8
budget.planner.matcher_specs: 0
budget.planner.vars: 90
budget.planner.blocks: 8
budget.planner.stmts: 76
budget.planner.dispatches: 7
---

# shared_heap_send_large_bitstring

A parent process builds a 70-byte bitstring (well above the
`SHARED_BIN_THRESHOLD_BYTES = 64` cutoff). It spawns a child whose
closure captures the bitstring; the child sends the captured bitstring
back to the parent; the parent prints it.

The bitstring crosses the 64-byte threshold. As of fz-q8d.2 the
const-fold pass collapses the byte-literal fields into a single
`Prim::ConstBitstring`; codegen emits both a bytes payload and a
40-byte static `SharedBin` struct in `.data` (refcount=1 anchor plus
relocations for `bytes_ptr` and the noop destructor), then a single
call to `fz_alloc_procbin_from_static`. Each `spawn` / `send` retains
the static SharedBin — no heap allocation, no byte copy at any step.

Three-path notes:
  * JIT, interp, and AOT all exercise the full code path. The fixture
    matrix asserts identical stdout. Interp does not emit Cranelift
    `.data` and continues to route through `Heap::alloc_bitstring`,
    which yields a runtime-allocated ProcBin for above-threshold
    payloads. Output is identical because the dispatch helpers
    (`procbin::bitstring_bit_len` / `procbin::bitstring_byte_ptr`)
    abstract over the two storage modes.

The refcount invariant — at most one heap-allocated SharedBin across
the whole run; the static SharedBin's anchor stays ≥ 1 — is verified
in `runtime/src/procbin.rs` and `runtime/src/heap.rs` unit tests via
`procbin::live_count()`.
