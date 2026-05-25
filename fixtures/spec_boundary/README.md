---
purpose: "fz-jg5.12 (RED.9) — @spec is a reduction boundary; fact has 1 body, not 0"
paths: [jit, interp, aot]
budget.codegen.functions: 6
budget.codegen.instructions: 38
budget.specs.count: 6
budget.typer.worklist_pops: 13
budget.typer.walk_calls: 13
budget.typer.type_fn_calls: 6
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 8
budget.typer.stmts: 12
budget.typer.dispatches: 5
---

# spec_boundary

fz-jg5.12 (RED.9) — declaring `@spec fact(integer) :: integer` tells
the reducer to honor `fact` as a contract. Without the spec, the
reducer would fold `fact(5)` to the literal `120` and emit no body;
with the spec, `fact` survives as a single emitted body and `main`
calls it.

Compare against `multi_clause`, which `fact`s without an `@spec` and
demonstrates the reducer collapsing the call.

## Notes

         runs identically on interp, jit, aot
