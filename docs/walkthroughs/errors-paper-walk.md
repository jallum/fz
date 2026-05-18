# errors — paper walk under the proposed reducer

## Context

`fixtures/errors/` contains **diagnostic fixtures**, not runtime
fixtures. Each subdirectory exercises a compile-time error in a
specific pipeline phase:

| Subfixture | Phase | What fails |
|---|---|---|
| `lex-bad-char` | lexer | backtick in source — `error[lex/unexpected-char]` |
| `lower-unbound` | lower | reference to undefined `missing_var` — `error[lower/unbound]` |
| `macro-not-a-defmacro` | macro | item-level `test(:foo) do … end` — `error[macro/not-a-defmacro]` |
| `resolve-alias-outside-module` | resolve | top-level `alias` — `error[resolve/alias-outside-module]` |
| `unreachable-then` | type | `if x == 1` where `x :: :atom` — unreachable then-branch |

## Where the reducer sits in the pipeline

Per `bodies-are-boundaries.md`:

```
parse → lower → resolve → macro → typer ← (reducer here, Module → Module) → backends
```

The reducer runs **after** lex, lower, resolve, macro, **and** typer.
It consumes a typed Module.

## Reducer participation per subfixture

| Subfixture | Phase that fails | Reducer runs? |
|---|---|---|
| `lex-bad-char` | lex | **no** — pipeline aborts before reducer |
| `lower-unbound` | lower | **no** — pipeline aborts before reducer |
| `macro-not-a-defmacro` | macro | **no** — pipeline aborts before reducer |
| `resolve-alias-outside-module` | resolve | **no** — pipeline aborts before reducer |
| `unreachable-then` | type | **no** — pipeline aborts before reducer (or: warning, but if it errors before reduction begins) |

**For every subfixture in this batch, the reducer never runs.** The
diagnostic is produced by an earlier phase; compilation halts; the
backends (and therefore the reducer) are never reached.

## What this means for the reducer design

**The reducer must not affect error reporting.** Since it doesn't
run on the error path, this is trivially satisfied — there's no
interaction.

**For non-error programs, the reducer must not introduce new
diagnostics.** Reduction is a Module → Module rewrite that preserves
program semantics. It must not:

- Drop user-visible types from being checked (typer runs first).
- Resurrect dead-code paths that the typer flagged as unreachable.
- Change span attribution for runtime diagnostics on residual code.

The `unreachable-then` case is the most interesting: if the typer
flags the then-arm as unreachable and the program is a hard error
(not a warning), compilation halts before reduction. If it's a
warning, the reducer would see a Module with that arm marked
dead — `ir_dce` (or its successor) would strip it. **Span
preservation** is what the reducer must respect.

## Walk

There are no `eval` callsites to walk, no `fold-prim` to apply, no
boundaries. **The seven reducer rules are not exercised by any
fixture in this batch.**

## Bodies emitted

N/A — compilation fails.

## Findings

**These fixtures are reducer-invisible.** Compilation halts in lex /
lower / macro / resolve / typer. The reducer pass never executes on
them.

**Implication for testing:** the RED.6 ticket ("re-bless every
fixture golden") should **explicitly skip** the `errors/` directory.
There's no `expected.clif` to re-bless; the diagnostic is the only
output. Adding the reducer pass cannot change the diagnostic surface
of these fixtures (modulo bugs that crash the pipeline).

**Implication for the reducer's diagnostic obligations
(`--explain-bodies`, RED.7):** the diagnostic only makes sense when
the reducer ran. On error fixtures it should be silent / absent.

**One forward-looking concern:** if the reducer ever drives
type-directed errors (e.g. "this body would never reduce; declared
`@spec` says it must"), those would need their own diagnostic codes
and own fixture subdirectory under `errors/`. Not in scope for the
v1 reducer.

**No judgment calls.** No reducer rules applied. The fixture batch
is a "negative space" exercise — confirming the reducer's domain
boundary.
