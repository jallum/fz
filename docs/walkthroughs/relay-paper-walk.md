# relay — paper walk

Ticket: `fz-jg5.1` (SPIKE — verify reducer on send-then-receive
inside a spawned task; the stress test for receive-feeding-reducer).

This walkthrough is the canonical **receive-feeding-into-reducer**
case from the design note. The spawned `relay` function calls
`receive()`, adds `1`, and sends the result to pid 1. The reducer
must stop at the receive, emit a body for relay, and emit a body for
the receive-cont that contains the arithmetic + send.

## The source

```
fn relay(), do: send(1, receive() + 1)

fn main() do
  spawn(relay)
  send(2, 41)
  print(receive())
end
```

## Pre-reducer call graph from main

```
main
├── spawn(relay)              (extern; arg is fn-value)
│     └── relay : () -> send(1, receive() + 1)
│           ├── receive()      (extern — boundary)
│           ├── (+1 prim)
│           └── send(1, _)     (extern)
├── send(2, 41)                (extern)
├── receive()                  (extern — boundary)
└── print(...)                 (extern)
```

`send`, `receive`, `spawn`, `print` are extern primitives. `+` is a
binary `Prim`. `relay/0` is the only user function.

## Call 1 — `spawn(relay)`

Same shape as concurrency_ping_pong: `relay` is a named zero-capture
fn-value. The reducer resolves it to a static target.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | (fn-value reduce) | `relay` is top-level; no captures. | 1 |
| 1.2 | recurse | reduce `relay`'s body: `send(1, receive() + 1)`. | 1 |
| 1.2.1 | stop-opaque | `receive()` is an extern returning `any`. **Cannot reduce past it.** This is the canonical receive-feeding-reducer stop. | 1 |
| 1.2.2 | (residual) | `receive()` stays. Its CPS cont is `λ msg -> send(1, msg + 1)`. | 1 |
| 1.2.3 | fold-prim attempt | `msg + 1` — `msg :: any`, not a literal. **fold-prim does not fire.** Leave the prim. | 1 |
| 1.2.4 | (extern call) | `send(1, msg + 1)` — extern, opaque-input. Leave. | 1 |

**Reduced form of `relay`'s body:** unchanged — `send(1, receive() + 1)`.
Structurally the same as the source, but now we know **why** the
reducer left it alone: the receive boundary blocks all downstream
folding.

## Call 2 — `send(2, 41)`

Extern primitive with literal args. Reducer doesn't fold externs by
default (their effects are observable). Leave in place.

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | (extern call) | leave | 1 |

## Call 3 — `receive()` (in main)

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 3.1 | stop-opaque | untyped mailbox | 1 |

The receive-cont in main is `λ msg -> print(msg)`.

## Call 4 — `print(receive())`

Receive-cont body. `print` is an extern; leave.

## main, after reduction

```
fn main() do
  spawn(relay)
  send(2, 41)
  print(receive())
end

fn relay() do
  send(1, receive() + 1)
end
```

User function bodies emitted: **one** — `relay`. Its body is
**unchanged from source**: the receive boundary inside it stopped all
internal reduction.

## Findings

**Boundary count: 2 user-visible receive sites + 3 send/print
externs.**

1. **`receive()` inside `relay`** — *boundary type:* untyped receive
   inside a spawned task. *Annotation that would narrow:* typed
   mailbox on `relay`'s pid. With `@mailbox int`, the cont's `msg ::
   int`, the `+ 1` is a typed int prim (no `any` widening), and the
   downstream `send(1, msg + 1)` carries a typed int payload.
2. **`receive()` in main** — *boundary type:* untyped receive.
   Annotation as above (different mailbox).

**The receive-cont's body is what carries the arithmetic.** In CPS,
`send(1, receive() + 1)` lowers to: `receive(cont = λ msg ->
let x = msg + 1 in send(1, x, cont = λ _ -> halt))`. The reducer
walks into the receive-cont and tries to fold `msg + 1`. Because
`msg :: any`, **fold-prim does not fire**. The prim survives, and
the cont body is emitted as the residual body of the receive
continuation.

**With typed receive, the cont body becomes typed.** If the mailbox
were declared `int`, the cont would still emit (extern boundary
downstream), but `msg + 1` would type-check at compile time and
codegen would pick the unboxed int `+` instead of the boxed-any
fallback. **The body count stays 1; the body's contents are
sharper.** This matches the table at the bottom of
`bodies-are-boundaries.md` — relay typed vs untyped differ only in
allocation character, not body count.

**Capture handling.** The receive-cont inside `relay` captures
nothing. The receive-cont in main captures nothing. No closure heap
objects arise. The cont's bound variable `msg` is the
receive-supplied value, not a capture.

**Send is an extern, not a reducer primitive.** `send(2, 41)` in
main has literal args but the reducer leaves it alone because
externs have side effects. This is the right default — we do not
want compile-time message sends. The stop rule here is implicit
("externs are leaves") rather than one of the seven named rules.

**Order-of-evaluation concern observed (out-of-scope but noted).**
The README flags that this fixture currently runs only under the JIT
because the cooperative scheduler runs `main` first and parks the
child on receive. The reducer doesn't see scheduling — it produces
the same residual IR regardless of scheduler. The scheduling
difference is a runtime concern (fz-sched.1 / .3); the reduced IR
is the same.

**Judgment call — extern-with-literal-args policy.** `send(2, 41)`
has two literal args. The reducer does **not** fold it (would
require a "pure extern" annotation, which we don't have). Likewise
`print` (probably also effectful in some configurations) is left
alone. This is consistent with the design note's stop list: extern
calls are leaves whose output is `any` or declared. **No new rule
needed**; the existing "extern = leaf" treatment covers it.

**Judgment call — does `send` count as a primitive that the reducer
special-cases, or just an extern?** From this fixture, treating it
as an extern is sufficient: extern calls stay, their args reduce
normally to literals (here `2`, `41`, or `msg + 1`), and codegen
emits the extern invocation. There is no benefit to special-casing
`send` at the reducer level. Same for `receive` (always stop-opaque
on output) and `spawn` (special handling of the fn-value argument
only, not of `spawn` itself). **The reducer rules cover
send/receive/spawn via the general extern path plus closure_lit
reduction.** No new primitives needed.

**Spike outcome: GO.** The receive-feeding-reducer stress test
behaves as the design note predicts:
- `receive()` halts reduction inside `relay`'s body.
- The CPS cont becomes the residual body that the reducer cannot
  shrink further (downstream is extern `send`).
- Typed mailbox annotation would sharpen the body without changing
  its structure.
- `relay` is emitted once as a body; `main` calls it via
  `spawn(relay)`; no closure heap object materialises.

Every step is one of the seven rules (with extern leaves treated
implicitly). No new mechanism surfaced.
