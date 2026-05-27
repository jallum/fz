---
purpose: "&name/arity parses as an explicit function reference, disambiguating overloaded names by arity"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 9
budget.specs.count: 4
budget.planner.worklist_pops: 4
budget.planner.walk_calls: 4
budget.planner.type_fn_calls: 4
budget.planner.matcher_specs: 0
budget.planner.vars: 29
budget.planner.blocks: 4
budget.planner.stmts: 18
budget.planner.dispatches: 0
---

# fn_ref_ampersand

fz-swt.5 — Elixir-style `&name/arity` syntax for first-class function
references. Today a bare name lowered to a zero-capture closure picks
"first defined wins" for overloaded names; `&pick/1` vs `&pick/2` makes
that choice explicit.
