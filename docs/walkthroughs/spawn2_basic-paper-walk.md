# spawn2_basic — paper walk

Ticket: `fz-jg5.1` (SPIKE — verify the reducer on the spawn/receive
boundary cases).

This walkthrough drives every callsite in `main` through the reducer
rules by hand. The fixture exercises the **spawn-with-static-closure**
case (an anonymous zero-capture lambda) plus an **untyped receive**.

## The reducer rules, in one place

| Rule | When | Effect |
|---|---|---|
| **dispatch** | callee is a multi-clause fn; try clause heads against input Descrs | yield `MatchedClause(idx, bindings)` |
| **substitute** | a `MatchedClause` is in hand | replace pattern-bound names with bound Descrs |
| **fold-prim** | a `Prim` whose inputs are all literal Descrs | evaluate to literal |
| **recurse** | substituted body has a `Call`/`TailCall` with strictly smaller input Descr | reduce it too |
| **stop-opaque** | dispatch reports no clause statically matches | leave call in place; emit body |
| **stop-non-decrease** | recursive call's input not provably smaller | leave call in place |
| **stop-budget** | counter exceeds `UNROLL_BUDGET` | abandon partial work |

## The source

```
fn child(tag) do
  send(1, tag)
end

fn main() do
  spawn(fn () -> child(42), 4096)
  print(receive())
end
```

## Pre-reducer call graph from main

```
main
├── spawn(λ, 4096)            (extern/primitive)
│     └── λ : () -> child(42) (anonymous zero-capture closure)
│           └── child(42)
│                 └── send(1, 42)   (extern/primitive)
├── receive()                  (extern/primitive — boundary)
└── print(...)                 (extern/primitive)
```

Note: `send`, `receive`, `spawn` are **primitives / externs** at the
IR level. They are not user `fn` clauses and so do not go through
`dispatch`. They enter the reducer rules as "unknown opaque callee"
unless special-cased.

## Call 1 — `spawn(fn () -> child(42), 4096)`

`spawn` is an extern that takes a closure-value plus an opaque
integer hint. By the design note (§ "How closures and spawn fit in"):
when `spawn`'s closure argument is a `closure_lit` with **all captures
literal** (here: zero captures), the reducer reduces the lambda's body
in isolation, producing a **static thunk**.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | (closure_lit reduce, RED.5) | the lambda has captures `[]` — all literal trivially. Substitute captures into λ body → body is `child(42)` unchanged. | 1 |
| 1.2 | recurse | reduce `child(42)`. Input `42` is a literal Descr — strictly known. | 2 |
| 1.2.1 | dispatch | `child/1` is a single-clause fn with head `tag` (no pattern guard) → bind `tag := 42` | 2 |
| 1.2.2 | substitute | body `send(1, tag)` → `send(1, 42)` | 2 |
| 1.2.3 | (extern call) | `send(1, 42)` is a primitive — does NOT reduce. It is the boundary inside the lambda body. Leave in place. | 2 |
| 1.3 | (spawn rewrite) | the lambda now has body `send(1, 42)` with no free captures. spawn target becomes a **static thunk** referring to that residual body. The `4096` hint flows through unchanged. | 2 |

**Reduced form of call 1:** `spawn(THUNK_send_1_42, 4096)` where
`THUNK_send_1_42` is a top-level zero-capture function whose body is
`send(1, 42)`. Heap closure allocation: **none** (zero captures).

**Boundary inside the thunk:** `send/2` is an extern. Its output type
is `any` / unit. Body emitted: the static thunk wrapping `send(1, 42)`.
This is the one user-visible body produced by call 1.

## Call 2 — `receive()`

`receive` is an extern primitive. The reducer rule fires:
**stop-opaque** (the mailbox message Descr is `any` until typed
mailboxes ship — `fz-ul4.19` defers typed receive).

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | stop-opaque | `receive()` has output Descr `any`. Cannot fold, cannot substitute downstream. Leave the call. | 1 |

**Reduced form:** the `receive()` call stays. Its result flows into
`print(...)` (also an extern) as an opaque value.

**What body gets emitted for the receive cont?** The CPS shape of
`main` has `receive()` as a Term::Call whose Cont takes the received
value and feeds it to `print`. Because the cont's body is
`print(received)` and `print` is an extern, the cont **is itself the
boundary body**: a tiny function `λ msg -> print(msg)` with no
captures. The reducer cannot dissolve it because `msg :: any`.

## Call 3 — `print(receive())`

The `print` call is downstream of `receive`. Under CPS this is the
receive-cont's body. By call 2, the cont body cannot be reduced past
the `print` extern. Both calls stay.

## main, after reduction

```
fn main() do
  spawn(THUNK_send_1_42, 4096)   # static thunk, zero captures
  print(receive())               # boundary: untyped receive
end
```

Plus one residual top-level function:

```
fn THUNK_send_1_42() do
  send(1, 42)
end
```

The user-written `child/1` function is **gone** — fully inlined at
its single call site inside the lambda. No `child` body is emitted.

## Findings

**Boundary count: 2.** Both are externs:

1. **`receive()` in main** — *boundary type:* untyped receive
   (mailbox is `any`). *Annotation that would narrow:* typed
   mailbox / typed receive (`fz-ul4.19`). With `@mailbox int`,
   receive's output is `int`, and the print cont can stay typed
   through to the print extern.
2. **`send(1, 42)` inside the spawned thunk** — *boundary type:*
   primitive/extern call. *Annotation that would narrow:* typed
   extern declaration (the design note's third user knob). For this
   fixture the extern's output is irrelevant (it's discarded), so
   no narrowing changes the body count.

**Capture handling is clean.** The anonymous lambda has zero
captures, so closure_lit reduction (RED.5) trivially substitutes the
empty capture set into the body. The lambda becomes a top-level
static thunk with no heap object at the spawn site. `4096` flows
through as a literal hint.

**`spawn` itself is an extern primitive.** It does not enter the
seven rules as a `dispatch` candidate. The reducer's behavior at
spawn is governed by the **"closures with static captures dissolve"**
rule from § "How closures and spawn fit in", which is operationally
a closure_lit reduction (RED.5) followed by extern-call passthrough
of the residual thunk pointer.

**Receive's cont absorbs the boundary.** The CPS receive-cont is the
body that gets emitted. Because its body trivially forwards to
another extern (`print`), the cont is one statement. With typed
receive, the cont would receive a typed value but still emit because
`print` is an opaque sink.

**Judgment call surfaced — fn-name vs anonymous lambda passed to
spawn.** The task asked whether `spawn(some_fn)` (top-level name) and
`spawn(fn () -> ...)` (anonymous zero-capture) reduce identically.
For this fixture the lambda is anonymous; the reducer treats it as a
closure_lit with empty captures and produces a top-level thunk.
**The two forms should reduce identically** — both are zero-capture
function values, and the reducer should canonicalize them through the
same closure_lit path. This is verifiable against the
`concurrency_ping_pong` fixture (which uses the top-level-name form)
in this same batch.

**Spike outcome for this fixture: GO.** Every step is one of the
seven rules, modulo the special-cased `spawn` extern (covered by the
design note). No hopeless issue.
