---
purpose: "fz-swt.12 — resource lifecycle (make_resource + .value + dtor) is observably identical across interp, JIT, AOT"
paths: [interp, jit, aot]
budget.codegen.functions: 4
budget.codegen.instructions: 61
budget.specs.count: 4
budget.typer.worklist_pops: 7
budget.typer.walk_calls: 7
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 61
budget.typer.blocks: 12
budget.typer.stmts: 31
budget.typer.dispatches: 4
---

# resource_lifecycle

fz-swt.12 — three-path parity smoke for the resource subsystem.

A single fz program exercises every observable piece of the resource
mechanism added by fz-swt.5 through fz-swt.11:

- `make_resource(payload, &dwrap/1)` produces an opaque handle whose
  destructor is a thin wrapper closure around the C extern
  `fz_resource_test_print_dtor` (exported by the runtime crate; bound
  into interp and JIT via direct symbol table entries, and resolved
  in AOT through the linker).
- Three resources are allocated with payloads 10, 20, 30.
- Resource `c` is aliased into a second binding. Aliasing must not
  double-fire the dtor — both bindings point at the same off-heap
  allocation; the MSO chain holds it once, the dtor fires once.
- `R.unwrap/1` calls `h.value` from inside the declaring module `R`
  (the opaque-visibility gate accepts in-module access). This proves
  the `.value` accessor's read path on all three legs.
- After `:before` is printed, `main/0` returns; the process heap
  drops, the MSO sweep walks the chain in LIFO push order, and the
  three dtors fire in reverse-allocation order.

Expected output:

  10
  20
  30
  :before
  dtor:30
  dtor:20
  dtor:10

The `before`/`dtor:*` ordering is the same observable contract pinned
by the per-leg fixtures (`resource_aot_dtor`, the interp lifecycle
tests in `ir_interp.rs::resource_bif_tests`, and the JIT lifecycle
tests in `ir_codegen_tests.rs::resource_jit_tests`). This fixture
proves all three paths converge on identical output for the same
source — the three-path-parity acceptance demanded by the fz-swt
epic.
