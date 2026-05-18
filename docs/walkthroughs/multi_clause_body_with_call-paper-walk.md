# multi_clause_body_with_call — paper walk

Fixture: `fixtures/multi_clause_body_with_call/input.fz`. Expected
stdout:

```
7
99
```

This fixture exercises **multi-clause dispatch where one clause body
contains a Call** (`helper()`). The original codegen interest is in
the CPS-split path; for the reducer it's a simple sequence of
dispatch → substitute → recurse-into-callee.

## Source

```
fn helper(), do: 7

fn classify(0), do: helper()
fn classify(_), do: 99

fn main() do
  print(classify(0))
  print(classify(5))
end
```

## Call 1 — `classify(0)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | clause 0 head `0` matches → no bindings | 1 |
| 1.2 | substitute | body is `helper()` — no pattern bindings to apply | 1 |
| 1.3 | recurse | reduce `helper()` — zero-arg call, trivially "non-larger" than parent | 2 |
| 1.3.1 | dispatch | `helper` has one clause, no args, no head to match → trivially matched | 2 |
| 1.3.2 | substitute | body → `7` | 2 |

**Reduced form:** `7` (literal int). No residual calls.

## Call 2 — `classify(5)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | clause 0 rejects (`5 ≠ 0`); clause 1 head `_` matches | 1 |
| 2.2 | substitute | body → `99` | 1 |

**Reduced form:** `99`. No residual call.

## main, after reduction

```
fn main() do
  print(7)
  print(99)
end
```

Zero `classify` bodies. Zero `helper` bodies.

## Findings

**Recurse into a zero-arg call needs explicit handling.** The
structural-decrease check (Descr smaller than parent's input) doesn't
apply cleanly to a *different callee* with no arguments. `helper()`
isn't a recursive call to `classify`; it's a *new* callsite encountered
during substitution. The natural reading of `recurse` covers this —
"any Call/TailCall in the substituted body becomes a new reducible
callsite" — but the rule as stated is phrased around recursive calls
of the *same* function with smaller inputs.

**Recommendation:** clarify that `recurse` fires in two distinct
cases:

1. *Same-callee recursion* — requires structural decrease (the case
   the spike walked).
2. *Cross-callee call* in a substituted body — always fires (it's
   just another callsite, walk it as you would any callsite from
   main). No decrease check needed; if the cross-callee is itself
   recursive, the decrease check applies *within its own walk*.

This isn't a hopeless issue but it is an unspoken extension of the
seven rules. Worth surfacing in the RED.3 docs.

**Zero-arg callees are degenerate-but-valid for the matrix.** A
zero-arg fn has a 0×0 pattern matrix; dispatch is trivially "matched".
The reducer should handle this without special-casing.

**Bodies emitted by main:** **zero**. Both `classify` callsites
dissolve and the single inlined `helper()` also dissolves.
</content>
</invoke>