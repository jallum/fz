# cold_fn — paper walk under the proposed reducer

## The reducer rules

See `red-0-ast-eval-paper-walk.md`.

## The source

```
fn cold(x), do: x * 3
fn main(), do: print(cold(14))
```

Expected output: `42`.

## Program roots

Only `main`.

## Root: `main`

| Step | Rule | Detail |
|---|---|---|
| 1 | dispatch | `cold(14)` — one clause, head `(x)`. Binds `x := int_lit(14)`. |
| 2 | substitute | body becomes `int_lit(14) * 3`. |
| 3 | fold-prim | both inputs literal → `int_lit(42)`. |
| 4 | extern | `print(42)` — leave. |

**Reduced main:** `print(42)`. `cold` dissolved.

## Bodies emitted

| Fn | Bodies |
|---|---|
| `main` | 1 |
| `cold` | **0** |

## Findings

**"cold" is a name, not an attribute.** I scanned the source and the
README — `cold` is just an identifier for "a fn that gets called
once." There's **no `@cold` / `@hot` / `@no_inline` attribute** in
fz today on this fixture. The historical purpose (per README) was
JIT tier-0 vs tier-1 — "today every call is JIT," so it's now a
smoke test.

**Attribute design space (forward-looking, NOT in scope for v1):**
- If `@cold` were added later, the natural reducer interpretation
  would be "**do not** inline the body into callers" — keep the call
  in place even when reduction could proceed. Equivalent to making
  the call a forced boundary.
- `@hot` would be the dual: hint to allow inlining over `INLINE_BUDGET`
  even at large body size.
- `@no_inline` already tracked under `fz-ul4.11.26` and explicitly
  **deferred** in the Bodies-Are-Boundaries design.

None of these attributes are present in cold_fn. The reducer reduces
the call fully.

**No judgment calls** — trivial walk.
