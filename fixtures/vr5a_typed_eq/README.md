---
purpose: "VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 20
budget.specs.count: 3
budget.typer.worklist_pops: 6
budget.typer.walk_calls: 6
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 38
budget.typer.blocks: 7
budget.typer.stmts: 20
budget.typer.dispatches: 4
---

# vr5a_typed_eq

VR.5a — int-int / atom-atom equality lowers to a single icmp, no fz_value_eq dispatch

## Notes

`1 == 2` and `:ok == :err`: ir_typer narrows both operands to int / atom
monomorphic Descrs. VR.5a's lower_eq fires the same-kind scalar arm:
tagged FzValues for a given scalar kind compare by bit equality, so the
emit is a single icmp eq + bool_to_fz. No both_ptr tag dispatch, no
fz_value_eq call site.
