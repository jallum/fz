---
purpose: "fz-cty.6 — sending a >64-byte bitstring via spawn-and-send rounds through ProcBin/SharedBin under JIT and AOT"
paths: [jit, aot]
---

# shared_heap_send_large_bitstring

A parent process builds a 70-byte bitstring (well above the
`SHARED_BIN_THRESHOLD_BYTES = 64` cutoff). It spawns a child whose
closure captures the bitstring; the child sends the captured bitstring
back to the parent; the parent prints it.

The bitstring crosses the 64-byte threshold, so its payload is routed
through the shared zone: a single `SharedBin` is allocated and both the
parent's and the child's heaps hold a `ProcBin` stub referencing it.
Deep-copy at spawn (capture) and at send (mailbox delivery) goes
through `shared_bin_retain`, not byte-copy.

Three-path notes:
  * JIT and AOT both exercise the full code path. The fixture matrix
    asserts identical stdout.
  * Interpreter omitted — the legacy `ir_interp` does not yet implement
    the `Bitstring` IR prims (Discriminant(17)); that gap predates this
    epic and is out of scope. The runtime-level behaviour (deep_copy
    via retain, MSO sweep across GC) is asserted directly in
    `runtime/src/heap.rs` unit tests, which is the codepath the
    interpreter would invoke once it lands bitstring support.

The refcount invariant — exactly one SharedBin allocation across the
whole run, zero at the end — is asserted in the
`runtime/src/shared_bin.rs` and `runtime/src/heap.rs` unit tests via
`shared_bin_live_count()`.
