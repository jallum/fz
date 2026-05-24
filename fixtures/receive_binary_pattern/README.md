---
purpose: "receive with utf8 binary literals — locks SwitchKind::Binary three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 20
budget.codegen.instructions: 1025
budget.specs.count: 17
budget.typer.worklist_pops: 42
budget.typer.walk_calls: 42
budget.typer.type_fn_calls: 17
budget.typer.matcher_specs: 0
budget.typer.vars: 68
budget.typer.blocks: 20
budget.typer.stmts: 27
budget.typer.dispatches: 7
---

# receive_binary_pattern

fz-puj.45 (X4) — receive matcher implementing SwitchKind::Binary.

Three messages (two utf8 binary literals + an atom) drained by three
receives whose clauses use `"hello"`/`"world"`/wildcard. The matcher
dispatches via `fz_matcher_eq_bytes` against per-clause `.data` byte
payloads pre-declared at matcher emit time, so the comparison is
constant-time vs the literal without allocating a heap object for the
RHS. Interp mirrors the JIT semantics via `procbin::bitstring_bit_len`
and `bitstring_byte_ptr`.
