# actor_ring — paper walk under the proposed reducer

A non-trivial paper walk — multi-clause `relay/2`, recursion that
spawns its successor, `self()` captured into a closure, all under
opaque-input recursion.

## The reducer rules

See `red-0-ast-eval-paper-walk.md`. Plus boundary rules.

## The source

```
fn relay(0, home) do
  send(home, receive() + 1)
end

fn relay(n, home) do
  next = spawn(fn() -> relay(n - 1, home))
  send(next, receive() + 1)
end

fn main() do
  home = self()
  head = spawn(fn() -> relay(4, home))
  send(head, 0)
  print(receive())
end
```

Expected output: `5`.

## Process graph (runtime view)

```
   main (pid=home)
     |
     | home = self()
     | spawn lambda1 -> pid_a
     v
   relay(4, home) at pid_a
     | spawn lambda2 -> pid_b
     v
   relay(3, home) at pid_b
     | spawn lambda3 -> pid_c
     v
   relay(2, home) at pid_c
     | spawn lambda4 -> pid_d
     v
   relay(1, home) at pid_d
     | spawn lambda5 -> pid_e
     v
   relay(0, home) at pid_e
     receive() -> 4   (the cumulative increments)
     send(home, 5)

token: 0 -> pid_a (+1) -> pid_b (+1) -> ... -> pid_e (+1) -> home
                 1            2                      5
```

## Program roots

`main` plus every fn passed to `spawn`. Three spawn sites in source,
but two of them are **inside `relay/2`'s recursive clause** —
discovered during `main`'s reduction.

## Root 1: `main`

```
fn main() do
  home = self()
  head = spawn(fn() -> relay(4, home))
  send(head, 0)
  print(receive())
end
```

| Step | Rule | Detail |
|---|---|---|
| 1.1 | extern | `self()` — extern returning a pid Descr (opaque). Bind `home := <pid_any>`. |
| 1.2 | spawn with **opaque captures** | the lambda `fn() -> relay(4, home)` captures `home`. `home` is opaque (a runtime pid). Per design: opaque-capture spawn **emits a body for the lambda** with `home` as a free var. The lambda body is `relay(4, home)`. Reduce *inside* the lambda body with `4 = int_lit(4)` known, `home = opaque pid`. |
| | | (See "Inside lambda1" below.) |
| 1.3 | extern | `send(head, 0)` — both args available; `head` is an opaque pid Descr, `0` literal. Extern call; leave. |
| 1.4 | receive boundary | `receive()` opaque; into `print` extern. |

### Inside lambda1: `relay(4, home)` with `home` opaque

This is a recursive-fn reduction with one literal input and one
opaque. The reducer's dispatch query is: which clause of `relay/2`
matches `(int_lit(4), pid_any)`?

| Step | Rule | Detail |
|---|---|---|
| L1.1 | dispatch | clause 0 head `(0, home)` — first arg pattern is literal `0`; input is `int_lit(4)`. **Rejects.** Clause 1 head `(n, home)` — `n` binds to `int_lit(4)`, `home` binds to `pid_any`. `MatchedClause(1, {n: 4, home: pid_any})`. |
| L1.2 | substitute | body becomes `next = spawn(fn() -> relay(4 - 1, pid_any)); send(next, receive() + 1)`. |
| L1.3 | fold-prim | `4 - 1` → `3`. Body: `next = spawn(fn() -> relay(3, pid_any)); send(next, receive() + 1)`. |
| L1.4 | spawn (opaque-capture lambda) | the inner lambda captures `pid_any`. Reduce its body `relay(3, pid_any)` — recursive call into the reducer with smaller `n` (literal-decrement: `int_lit(3) < int_lit(4)` qualifies as structural decrease). counter += 1. |
| L1.5 | (recursion into relay(3, pid_any)) | same shape, body becomes `next = spawn(...relay(2, pid_any)...); send(...)`. counter += 1. |
| L1.6 | … | `relay(2, pid_any)` → `relay(1, pid_any)` → `relay(0, pid_any)`. counter += 3. Total ~5 steps. Well under budget. |
| L1.7 | clause 0 hits at relay(0, pid_any) | dispatch: first arg `int_lit(0)` matches literal `0` in clause 0 head; `home` binds. Body: `send(home, receive() + 1)`. |
| L1.7.1 | receive boundary | `receive()` opaque. |
| L1.7.2 | fold-prim? | `receive() + 1` — mixed; does not fold. |
| L1.7.3 | extern | `send(pid_any, <add>)` — leave. |

**Outcome of lambda1's reduction:** a fully-unrolled chain of 4
`spawn`s followed by the terminal `send(home, receive() + 1)`. Each
intermediate level still has its own `send(next, receive() + 1)`.

Wait — that's not right. Re-examine.

At level `relay(n, home)` the body is:

```
next = spawn(fn() -> relay(n - 1, home))
send(next, receive() + 1)
```

That `receive() + 1` and `send(next, ...)` is **per level**. The
reducer recursing on `relay(n-1, home)` reduces the *inner spawned
lambda's body*, not the current frame's tail. The current frame keeps
its own `send` and `receive`.

So lambda1's reduced body is:

```
next1 = spawn(<reduced relay(3, home) lambda>)
send(next1, receive() + 1)
```

…where `<reduced relay(3, home) lambda>` is itself a lambda whose
body is `next2 = spawn(<reduced relay(2, home) lambda>); send(next2, receive() + 1)`,
and so on down to `relay(0, home)` which is
`send(home, receive() + 1)`.

That's **5 distinct lambda bodies emitted** (one per literal `n` value
0..4), each containing one `receive()` boundary and one outbound `send`.

## Bodies emitted

| Fn | Bodies | Notes |
|---|---|---|
| `main` | 1 | always |
| lambda_relay_4 | 1 | reduced from outer spawn |
| lambda_relay_3 | 1 | reduced from inner spawn |
| lambda_relay_2 | 1 | |
| lambda_relay_1 | 1 | |
| lambda_relay_0 | 1 | (clause 0 — terminal) |

Six user bodies total. **No `relay/2` user body** survives — every
relay-spawned lambda has its `n` literal at compile time and gets
fully specialized.

If `n` were opaque (e.g. `spawn(fn() -> relay(some_runtime_n, home))`),
the reducer would hit `stop-non-decrease` on `n - 1` (opaque int
decrement is not provable decrease) and emit a single `relay/2` body
instead.

## Findings

**Literal-int countdown qualifies as structural decrease.** This is
the case flagged in RED.0's findings: `n_0 - 1` where `n_0` is a
literal `int_lit(k)` constant-folds to `int_lit(k-1)`, which is
strictly smaller than `int_lit(k)` by the literal-value measure. So
the recursion unrolls. Five levels, budget 32 — comfortable.

**Opaque pid captured into a closure is the "opaque captures" case.**
`home` is a runtime value (result of `self()`). Each spawned lambda
gets a heap closure object with `home` baked in. The lambda body is
emitted as a boundary body — but a *specialized* one (literal `n`).

**The reducer must distinguish the inner spawn's body from the outer
frame's tail.** At each `relay(n, home)` level, the body has two parts:
the recursive setup (`next = spawn(...)`) and the local tail
(`send(next, receive() + 1)`). The reducer reduces the inner lambda
**as its own root** (because spawn is a value-flow site that exposes
a new reduction root). The outer frame's tail is reduced separately
and includes its own `receive()` boundary. **Each level keeps its own
`receive` boundary** — boundaries are per-process.

**Multi-clause dispatch on literal-vs-opaque mix.** `relay(int_lit(4),
pid_any)` — clause 0 rejects on arg 0 (literal `0` vs `int_lit(4)`),
clause 1 matches. The matrix dispatcher handles per-arg matching
independently; no judgment call needed.

**Subtle: the closure for `fn() -> relay(n - 1, home)` captures
`home`, not `n`.** `n` is in the *enclosing* frame's binding. At the
spawn site, `n` is already a literal (the reducer is operating with
`n := int_lit(k)`), so the substituted lambda is
`fn() -> relay(int_lit(k-1), home)`. The closure heap object captures
only `home` (one slot). This is the **partial closure capture
substitution** discussed in `bodies-are-boundaries.md` Issue 4.

**No judgment calls surfaced.** The walk is mechanical, just deeply
nested.
