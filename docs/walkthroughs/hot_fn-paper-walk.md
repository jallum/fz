# hot_fn — paper walk under the proposed reducer

## The reducer rules

See `red-0-ast-eval-paper-walk.md`.

## The source

```
fn hot(n), do: n + 1

fn main() do
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
  print(hot(0))
end
```

Expected output: `1` repeated 10 times.

## Program roots

Only `main`.

## Root: `main`

Each of the 10 `print(hot(0))` callsites is independent. Walk one;
the others are identical.

| Step | Rule | Detail |
|---|---|---|
| 1 | dispatch | `hot(0)` — one clause, head `(n)`. Binds `n := int_lit(0)`. |
| 2 | substitute | body becomes `int_lit(0) + 1`. |
| 3 | fold-prim | both inputs literal → `int_lit(1)`. |
| 4 | extern | `print(1)` — leave. |

Memoization: the reducer keys on `(hot_fn_id, [int_lit(0)])`. After
the first reduction, the remaining 9 callsites hit the **memo cache**
and reuse the result `int_lit(1)`. Effective work: 1 reduction, 10
substitutions.

**Reduced main:**

```
print(1); print(1); ... (x10)
```

## Bodies emitted

| Fn | Bodies |
|---|---|
| `main` | 1 |
| `hot` | **0** |

## Findings

**Memoization shines here.** Ten identical callsites collapse via the
`(fn_id, input_descrs)` memo table (called out in
`bodies-are-boundaries.md` § "Scope of analysis"). Worst-case work
stays linear in distinct (fn, inputs) tuples, not callsite count.

**No `@hot` attribute exists.** Per README: "historical JIT tier-up
trigger; today every call is JIT." Same observation as cold_fn — the
naming is historical, not an attribute the reducer must honor.

**The reducer makes the JIT tier-up question moot for this fixture.**
There is no `hot` body to tier up; the 10 calls are 10 literal
`print(1)`s. Whatever tiering policy the JIT has, it operates on a
program that no longer contains `hot`.

**No judgment calls.** Trivial walk.
