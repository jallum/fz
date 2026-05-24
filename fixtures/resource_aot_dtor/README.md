---
purpose: "AOT-compiled binary fires user-supplied resource dtors at heap drop"
paths: [aot]
budget.codegen.functions: 2
budget.codegen.instructions: 46
budget.specs.count: 2
budget.typer.worklist_pops: 2
budget.typer.walk_calls: 2
budget.typer.type_fn_calls: 2
budget.typer.matcher_specs: 0
budget.typer.vars: 25
budget.typer.blocks: 3
budget.typer.stmts: 13
budget.typer.dispatches: 0
---

# resource_aot_dtor

fz-swt.11 — AOT leg of the refcount-+-dtor acceptance, mirroring the
interp (`fz-swt.9`) and JIT (`fz-swt.10`) tests.

`make_resource/2` produces an opaque handle whose dtor closure is a
thin wrapper around a single C extern. AOT codegen scans every zero-
capture closure body for that shape, bakes a static `(fn_id, fn_ptr)`
table into the emitted object (function-address relocations against
each extern's symbol), and the runtime hook installed by
`fz_aot_setup` looks each closure up at `make_resource` time.

The dtor used here is `fz_resource_test_print_dtor`, exported by the
runtime crate — it unboxes the payload as an `FzValue::Int` and prints
`dtor:<n>`. Three resources are allocated; aliasing one of them
shouldn't add a fire. Expected output:

  before
  dtor:30
  dtor:20
  dtor:10

The dtor lines arrive after `before` because the heap drops (and runs
its MSO sweep) at process exit, not at let-binding scope end. Order
within the dtor block reflects the MSO chain's LIFO push order — the
last `make_resource` is at the head of the chain and sweeps first.
