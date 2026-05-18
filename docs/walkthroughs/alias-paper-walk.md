# alias — paper walk

Drives every top-level callsite in `main` through the seven reducer
rules (see [red-0-ast-eval-paper-walk.md](red-0-ast-eval-paper-walk.md)
for the rule table).

## The source

```
defmodule Long do
  defmodule Path do
    fn greet(x), do: x + 1000
  end
end

defmodule User do
  alias Long.Path
  alias Long.Path, as: LP

  fn nick_name(x), do: Path.greet(x)
  fn renamed(x), do: LP.greet(x)
end

fn main() do
  print(User.nick_name(40))
  print(User.renamed(41))
end
```

Expected output:
```
1040
1041
```

`alias Long.Path` and `alias Long.Path, as: LP` are name-resolution
syntactic sugar: inside `User`, `Path.greet` and `LP.greet` both
resolve to `Long.Path.greet`. The reducer sees only the resolved
`FnId`s.

## Call 1 — `print(User.nick_name(40))`

`User.nick_name/1` is `fn nick_name(x), do: Path.greet(x)`. After
name resolution, that's `fn nick_name(x), do: Long.Path.greet(x)`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `nick_name` sole clause matches; bind `x := 40` | 1 |
| 1.2 | substitute | body → `Long.Path.greet(40)` | 1 |
| 1.3 | recurse | reduce `Long.Path.greet(40)` — input is the same literal (no decrease needed; non-recursive callee) | 2 |
| 1.3.1 | dispatch | `greet` sole clause matches; bind `x := 40` | 2 |
| 1.3.2 | substitute | body → `40 + 1000` | 2 |
| 1.3.3 | fold-prim | `40 + 1000` → `int_lit(1040)` | 2 |
| 1.4 | stop-opaque | outer `print` is extern; leave in place | 2 |

**Reduced form:** `print(1040)`.

(Aside on "recurse" rule wording: the template's `recurse` rule
phrasing is about *recursive* calls needing structural decrease. For
non-recursive callee inlining the same descent happens but no
decrease check is needed — it's just "dispatch and substitute on a
nested call." The rule table covers this implicitly under
`dispatch`+`substitute` on the new callsite; we mark the step as
`recurse` for clarity of nesting depth.)

## Call 2 — `print(User.renamed(41))`

Same shape as call 1, with the alias `LP` resolving to the same
`Long.Path.greet`.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | dispatch | `renamed` sole clause matches; bind `x := 41` | 1 |
| 2.2 | substitute | body → `Long.Path.greet(41)` | 1 |
| 2.3 | recurse | descend into `greet(41)` | 2 |
| 2.3.* | (same shape as 1.3.*) | yields `int_lit(1041)` | 2 |
| 2.4 | stop-opaque | `print` extern; leave in place | 2 |

**Reduced form:** `print(1041)`.

## main, after reduction

```
fn main() do
  print(1040)
  print(1041)
end
```

`User.nick_name`, `User.renamed`, and `Long.Path.greet` all dissolve.

## Findings

The walk is mechanical.

**Expected user-function body count:** 0. All three user functions
reduce away from their respective callsites. `main` is always
emitted; `print` is extern.

**Boundaries:** only `print` (twice).

**Feature surfaced — aliases are reducer-transparent.** `alias
Long.Path` and `alias Long.Path, as: LP` are pure name-resolution
sugar. They resolve before IR. The reducer never sees the alias; it
sees `Long.Path.greet` as a `FnId` in both `nick_name` and `renamed`.
Not a gap.

**Feature surfaced — nested module definitions.** `defmodule Long do
defmodule Path do ... end end` is module-path namespacing. Same
story: it affects the `FnId` namespace, not reduction.

**Subtlety worth noting:** in step 1.3 / 2.3 we used the `recurse`
label for a non-recursive nested call (calling `greet` from inside
`nick_name`'s body). The template's `recurse` rule is phrased around
recursive calls + structural decrease. For non-recursive callees,
descent has no termination concern; it's "just another dispatch." The
reducer implementation will want to disambiguate these cases (or
fold them under a single "descend into call" mechanism — the
recursive case adds the decrease check, the non-recursive case
skips it). **Not a gap; a wording clean-up for RED.3/RED.4 docs.**
