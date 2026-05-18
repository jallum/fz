# vr5b_typed_print — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
fn int_main() do
  print(42)
end

fn float_main() do
  print(1.5 + 2.5)
end

fn main() do
  int_main()
  float_main()
end
```

Expected output:
```
42
4.0
```

## Call 1 — `int_main()`

`int_main/0` is a single-clause zero-arity function. Body is
`print(42)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | sole clause head `()` matches the empty arg list | 1 |
| 1.2 | substitute | body is `print(42)` (no bound names to substitute) | 1 |
| 1.3 | stop-opaque | inner `print` extern; leave in place | 1 |

Result: the body inlined into `main` is `print(42)`.

## Call 2 — `float_main()`

`float_main/0` is a single-clause zero-arity function. Body is
`print(1.5 + 2.5)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | sole clause head `()` matches | 1 |
| 2.2 | substitute | body becomes `print(1.5 + 2.5)` | 1 |
| 2.3 | fold-prim | `1.5 + 2.5` → `float_lit(4.0)` | 2 |
| 2.4 | stop-opaque | inner `print` extern; leave in place | 2 |

Result: the body inlined into `main` is `print(4.0)`.

## main, after reduction

```
fn main() do
  print(42)
  print(4.0)
end
```

Both `int_main` and `float_main` dissolve.

## Findings

The walk is mechanical.

**Expected user-function body count:** 0. Both helpers are
zero-arity, single-clause, and called once each — fully reducible.
`main` is always emitted; `print` is extern.

**Boundaries:** only `print` (twice, once per helper).

**Feature surfaced — zero-arity dispatch.** Pattern matrix must
match an empty arg list against an empty clause head. Trivial case;
worth flagging only because it's the empty-matrix degenerate case
(matrix has one row, zero columns).

**Feature surfaced — statement-position calls (calls used for their
effect).** `int_main()` and `float_main()` in `main` are not used as
expressions whose value flows somewhere — they're sequenced for
their `print` side effects. After substitution, `main`'s body is a
sequence of `print` effects. The reducer needs to understand that
inlining a void/unit-returning callee at statement position **splices
the callee's effect sequence into the caller's sequence**, not
"returns a value to nowhere." This is mundane IR mechanics but worth
naming: substitute-and-splice for effects, substitute-and-bind for
values.

**Tangential observation (cf. the README).** The README is about
the *typed FFI fast path* for `print` — `descr_is_int` /
`descr_is_float` routing `print` to `fz_print_i64` / `fz_print_f64`
instead of the boxed `fz_print_value`. That's a codegen decision
downstream of reduction. The reducer's output here is `print(42)`
and `print(4.0)`; codegen decides which extern variant to call based
on the literal Descr's narrow type. Orthogonal to reduction.

**Nothing to call out as a gap.**
