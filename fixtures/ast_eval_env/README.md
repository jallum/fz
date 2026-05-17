---
purpose: "AST evaluator extended with variables and `let` — tagged-tuple dispatch + cons-list environment + recursive lookup + binding shadow"
paths: [jit, interp, aot, repl]
---

# ast_eval_env

`ast_eval`'s next step. The interpreter grows two new forms:

- `{:var, name}` — atom-keyed variable reference
- `{:let, name, expr, body}` — binds `name` to `expr`'s value, then
  evaluates `body` under the extended environment

The environment is a cons list of `{name, value}` tuples; `lookup`
walks it recursively and stops at the first matching atom.

```fz
fn lookup(name, [{n, v} | rest]) do
  if name == n do v else lookup(name, rest) end
end

fn eval({:let, name, expr, body}, env) do
  v = eval(expr, env)
  eval(body, [{name, v} | env])
end
```

What it exercises that nothing else does end-to-end:

- multi-clause tuple-pattern dispatch with **five** arms (one of which
  is a nested-tuple pattern, `{:num, n}`), where the recursive arms
  call `eval` again with values typed `any`,
- tuple destructuring inside a **cons pattern head** (`[{n, v} | rest]`)
  — pattern matching nested two levels in one clause,
- atom equality (`name == n`) inside an `if`, driving lookup-loop
  termination,
- binding shadowing across nested `let`s (case three: inner `:x`
  beats outer `:x`),
- list-of-pair env construction via cons (`[{name, v} | env]`) on
  the recursive call — every `let` allocates one cell.

The three sample expressions cover the basics, the recursive case
where a variable is read twice in different sub-trees, and shadowing.
