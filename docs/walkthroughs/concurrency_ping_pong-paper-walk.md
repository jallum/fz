# concurrency_ping_pong — paper walk

Ticket: `fz-jg5.1` (SPIKE — verify reducer on spawn-of-named-fn + receive).

This walkthrough exercises **`spawn` with a top-level fn name** (no
lambda, no captures) and the canonical send/receive pair across two
processes.

## The source

```
fn child(), do: send(1, 42)

fn main() do
  spawn(child)
  print(receive())
end
```

## Pre-reducer call graph from main

```
main
├── spawn(child)              (extern; argument is a fn value)
│     └── child : () -> send(1, 42)
│           └── send(1, 42)   (extern)
├── receive()                 (extern — boundary)
└── print(...)                (extern)
```

`child` is a top-level zero-arity fn (a named first-class function
value). Passing its name to `spawn` produces a fn-value reference —
operationally identical to a `closure_lit` with empty captures
pointing at `child`'s body. (See "judgment call" in Findings.)

## Call 1 — `spawn(child)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | (fn-value reduce) | `child` is a top-level fn — already a static identity. No captures to substitute. | 1 |
| 1.2 | (closure_lit reduce, RED.5) | Treat fn-value as a zero-capture closure. λ body = `send(1, 42)`. | 1 |
| 1.3 | recurse | reduce `child`'s body: it has no calls into other user fns — only `send(1, 42)`. | 1 |
| 1.3.1 | (extern call) | `send/2` is an extern primitive. Leave in place. | 1 |
| 1.4 | (spawn rewrite) | `spawn`'s argument is a static fn-value with empty captures and a residual body of `send(1, 42)`. Spawn target = `child` directly (no thunk synthesis needed — `child` already serves). | 1 |

**Reduced form of call 1:** `spawn(child)` unchanged at the IR level
— `child` is already the static target. No closure heap object is
needed because there are no captures.

## Call 2 — `receive()`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 2.1 | stop-opaque | mailbox is untyped; `receive()` returns `any`. | 1 |

`receive()` stays. The cont is `λ msg -> print(msg)`.

## Call 3 — `print(receive())`

The receive-cont's body. `print` is an extern; nothing to reduce.

## main, after reduction

```
fn main() do
  spawn(child)
  print(receive())
end

fn child() do
  send(1, 42)
end
```

User function bodies emitted: **one** — `child`, because it's the
spawn target and `spawn` is an extern boundary. Even though `child`'s
body fully reduced to a single extern call, the body must exist as a
top-level entry point for the spawned task to run.

## Findings

**Boundary count: 2.**

1. **`receive()` in main** — *boundary type:* untyped receive.
   *Annotation that would narrow:* typed mailbox (`fz-ul4.19`); with
   `@mailbox int`, receive's output is `int`.
2. **`send(1, 42)` inside `child`** — *boundary type:* extern
   primitive. *Annotation that would narrow:* typed extern declaration.

User bodies emitted: **1** (`child` survives as the spawn entry
point).

**Judgment call — spawn(named_fn) vs spawn(anonymous_lambda).** This
fixture passes the **name** `child`; spawn2_basic passes
`fn () -> child(42)` (an anonymous lambda that *calls* child).

The reducer should treat these uniformly: both produce a zero-capture
fn-value at the spawn site. The difference is purely syntactic — a
named top-level fn is its own "thunk" (no synthesis needed), whereas
an anonymous lambda body must be lifted to a synthetic top-level
function. In both cases the heap object at the spawn site is **none**
(zero captures, statically resolvable target).

**spawn2_basic's lambda `fn () -> child(42)` further reduces inside**:
the reducer recurses through `child(42)` and substitutes to produce
a residual body `send(1, 42)`. The synthetic thunk inlines `child`.
That means **spawn2_basic emits zero `child`-named bodies** (the
lambda subsumes `child`), whereas concurrency_ping_pong **emits one
`child` body** because it's the direct spawn target.

This is a subtle but important distinction: passing the name
preserves the named function in the residual program; passing a
lambda that calls the name allows the reducer to inline the name's
body into the lambda and emit only the synthetic thunk. **Both
shapes are correct; they just produce different residuals.** The
user-facing rule from the design note still holds: bodies are emitted
at boundaries, and the spawn target is a boundary.

**Receive-cont in main is trivial.** `λ msg -> print(msg)`. No
captures, no further reduction possible (print is opaque sink).

**Capture substitution does not arise.** Zero captures throughout.
This is the simplest spawn shape in the batch — useful as a
calibration point against spawn_with_captures (where substitution
does the work).

**`spawn` is an extern with a fn-value argument.** It enters the
reducer as an extern call whose argument happens to be statically
resolvable. The reducer's job at this site is:
1. Resolve the fn-value to a concrete callee (here: `child`).
2. Reduce that callee's body in isolation (it's a separate process —
   the caller's environment doesn't flow in).
3. If reduction empties captures and produces a residual body, the
   spawn target is just a function pointer. If not, a closure heap
   object survives.

For concurrency_ping_pong, captures are empty by construction.
Outcome: function pointer, no heap object.

**Spike outcome: GO.** No new rules surfaced. The fn-name-vs-lambda
distinction is mechanical and reduces to "is the spawn target
synthetic or pre-existing."
