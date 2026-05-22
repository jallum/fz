---
purpose: "receive with utf8 binary literals — locks SwitchKind::Binary three-path parity"
paths: [jit, interp, aot]
budget.codegen.functions: 27
budget.codegen.instructions: 530
budget.specs.count: 11
budget.typer.worklist_pops: 24
budget.typer.walk_calls: 24
budget.typer.type_fn_calls: 11
budget.typer.matcher_specs: 0
budget.typer.vars: 59
budget.typer.blocks: 14
budget.typer.stmts: 27
budget.typer.dispatches: 1
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
