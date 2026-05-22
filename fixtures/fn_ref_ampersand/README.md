---
purpose: "&name/arity parses as an explicit function reference, disambiguating overloaded names by arity"
paths: [jit, interp, aot]
budget.codegen.functions: 3
budget.codegen.instructions: 13
budget.specs.count: 6
budget.typer.worklist_pops: 9
budget.typer.walk_calls: 9
budget.typer.type_fn_calls: 6
budget.typer.matcher_specs: 0
budget.typer.vars: 37
budget.typer.blocks: 9
budget.typer.stmts: 21
budget.typer.dispatches: 2
---

# fn_ref_ampersand

fz-swt.5 — Elixir-style `&name/arity` syntax for first-class function
references. Today a bare name lowered to a zero-capture closure picks
"first defined wins" for overloaded names; `&pick/1` vs `&pick/2` makes
that choice explicit.
