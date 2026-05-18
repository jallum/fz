# vr1_int_arith — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
fn main() do
  print(40 + 2)
  print(100 - 7)
  print(6 * 7)
end
```

Expected output:
```
42
93
42
```

## Call 1 — `print(40 + 2)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | fold-prim | `40 + 2` → `int_lit(42)` | 1 |
| 1.2 | stop-opaque | `print` extern; leave in place | 1 |

**Reduced form:** `print(42)`.

## Call 2 — `print(100 - 7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | fold-prim | `100 - 7` → `int_lit(93)` | 1 |
| 2.2 | stop-opaque | `print` extern; leave in place | 1 |

**Reduced form:** `print(93)`.

## Call 3 — `print(6 * 7)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | fold-prim | `6 * 7` → `int_lit(42)` | 1 |
| 3.2 | stop-opaque | `print` extern; leave in place | 1 |

**Reduced form:** `print(42)`.

## main, after reduction

```
fn main() do
  print(42)
  print(93)
  print(42)
end
```

## Findings

The walk is mechanical — three `fold-prim`s and three `stop-opaque`s.

**Expected user-function body count:** 0. No user functions defined.
`main` is always emitted; `print` is extern.

**Boundaries:** only `print` (three times).

**Feature surfaced — `int + int`, `int - int`, `int * int` are the
arithmetic prims `fold-prim` needs.** Already in scope per the
template (`fold-prim` handles literal-int Prims). No gap.

**Note relating to the fixture's purpose.** The README describes
*runtime codegen* wins (tag-check elision, fast/slow path). Those are
downstream of the reducer. The reducer's job here is far simpler:
constant-fold the three Prims. Whether the resulting `print(42)` then
codegens via a typed-FFI fast path (`fz_print_i64`) or the boxed
fallback is a downstream codegen decision, orthogonal to reduction.

**Nothing to call out as a gap.**
