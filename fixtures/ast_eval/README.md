---
purpose: "tagged-tuple AST evaluator — first fixture to exercise multi-clause tuple-pattern dispatch end-to-end"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 1
budget.codegen.instructions: 14
budget.specs.count: 1
budget.planner.worklist_pops: 1
budget.planner.walk_calls: 1
budget.planner.type_fn_calls: 1
budget.planner.matcher_specs: 0
budget.planner.vars: 44
budget.planner.blocks: 1
budget.planner.stmts: 40
budget.planner.dispatches: 0
---

# ast_eval

Classic Erlang/Elixir teaching shape: a tiny expression interpreter
defined by pattern-matching `fn` clauses over tagged tuples.

```fz
fn eval({:num, n}), do: n
fn eval({:add, a, b}), do: eval(a) + eval(b)
fn eval({:mul, a, b}), do: eval(a) * eval(b)
```

First fixture to combine:

- multi-clause `fn` dispatch on a tuple subject (resolved at runtime
  via `Prim::TypeTest` reading `descr.tuples`, landed in fz-ul4.36),
- tuple construction (`Prim::MakeTuple`) and field projection
  (`Prim::TupleField`) on every execution path (interp arms landed
  in fz-ul4.35; AOT schema registration in fz-ul4.38),
- self-recursion through the runtime `TypeTest` (the planner can't
  fully specialize because the recursive arguments are typed `any`
  inside each clause body),
- multiple sequential `dbg(eval(...))` calls in `main` — the
  original demo shape, unblocked once fz-i82 was fixed in PR #12.
