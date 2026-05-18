# Bodies, Boundaries, and Reuse — Design Note

Status: **design discussion**, pre-implementation. A teachable picture of
how fz should decide what to compile, and how the compiled code should
allocate. Not yet tied to tickets.

## The puzzle

Here is the entire `ast_eval` fixture (`fixtures/ast_eval/input.fz`):

```
fn eval({:num, n}), do: n
fn eval({:add, a, b}), do: eval(a) + eval(b)
fn eval({:mul, a, b}), do: eval(a) * eval(b)

fn main() do
  print(eval({:num, 42}))
  print(eval({:add, {:num, 2}, {:mul, {:num, 3}, {:num, 4}}}))
  print(eval({:mul, {:add, {:num, 1}, {:num, 2}}, {:add, {:num, 3}, {:num, 4}}}))
end
```

Nine lines. Prints `42`, `14`, `21`.

Today this produces **13 specializations of `eval`**, more for each
helper, a cascade of CPS continuations, and **~1400 lines of CLIF** —
for a program whose entire output is three integers. Every recursive
call inside `eval` is also allocating cons cells, struct slots, and
closure objects on the heap, most of which the runtime then traces and
reclaims.

Two questions worth answering for fz:

1. **What should the compiler compile?**
2. **For the code it does compile, how should it allocate?**

Today fz answers both questions by accident — compile every shape we
see at every callsite, allocate fresh memory for every constructor.
This note proposes principled answers to both, drawing on 50 years of
lore.

The two answers compose: when the first cuts the right amount, the
second has much less to do; when the first stops at a boundary, the
second decides how the boundary code mutates rather than allocates.

---

# Part 1: What gets compiled

## Functions are templates, not specs

Look at clause 1:

```
fn eval({:num, n}), do: n
```

This isn't a function from "some type" to "some type." It's a
**rewrite rule**: whenever you see `eval({:num, N})`, replace it with
`N`. Whatever `N` was — `42`, `1.5`, `:hello` — that's what comes out.

Clause 2 is the same shape:

```
fn eval({:add, a, b}), do: eval(a) + eval(b)
```

`eval({:add, X, Y})` rewrites to `eval(X) + eval(Y)`.

Every fz function is a stack of rewrite rules. The compiler's job is
to **apply the rewrites until it can't**.

For ast_eval:

```
eval({:add, {:num, 2}, {:mul, {:num, 3}, {:num, 4}}})
  ⇒ eval({:num, 2}) + eval({:mul, {:num, 3}, {:num, 4}})     (clause 2)
  ⇒ 2 + eval({:mul, {:num, 3}, {:num, 4}})                   (clause 1)
  ⇒ 2 + (eval({:num, 3}) * eval({:num, 4}))                  (clause 3)
  ⇒ 2 + (3 * 4)
  ⇒ 14
```

That whole chain happens **at compile time**, on the source program.
The output is `14`. No `eval` body need exist.

Apply this to all three callsites in `main` and we have:

```
fn main() do print(42); print(14); print(21) end
```

**Zero `eval` bodies.** Three `print` calls with literal arguments.
This technique has a name: **partial evaluation** (Futamura 1971;
Jones, Gomard, Sestoft 1993). It's been in the lore for fifty years.

## Where reduction stops

Reduction has limits. When it stops, the compiler emits a real body —
the version of the function that performs the work at runtime. We
call this a **boundary body**, because the boundary is between what
the compiler can know and what the runtime must decide.

Reduction stops when *any* of these is true:

### 1. The value's shape is opaque

```
fn main() do
  msg = receive()
  print(eval(msg))
end
```

`msg` is whatever an external process sent us. The compiler can't pick
a clause, can't substitute, can't fold. Boundary.

### 2. The unroll budget is exceeded

```
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main() do print(count(100000, 0)) end
```

In principle, `count(100000, 0)` reduces in 100,000 small steps. In
practice nobody wants 100,000 unrolled cons cells of CLIF. The
compiler picks a budget (say 32 steps) and stops when hit. A single
`count` body is emitted; `main` calls it once with `(100000, 0)`.

That's a **cost-model knob**, with a sane default.

### 3. Recursion without provable structural decrease

If reducing `f(x)` requires reducing `f(g(x))` and `g(x)` isn't
provably smaller than `x` in any measure the compiler tracks: stop.
Boundary. Avoids infinite expansion.

## How closures and spawn fit in

Closures are values that carry a function and zero or more captured
variables. They reduce normally:

**Static captures.** `add_to(10, 20)` produces a closure with captures
`[10, 20]` — literals. Inline the captures into the body: it becomes
`10 + 20 + z`. When called with `12`: `42`. **No closure heap object
is allocated at runtime.** The captures dissolved into literals; the
call dissolved into arithmetic.

**Opaque captures.** `parent(some_runtime_value)` produces a closure
whose captures aren't statically known. The closure must be
heap-allocated; the lambda body parameterizes over `tag`. Boundary
body for the lambda.

`spawn` is the same machinery. `spawn(fn () -> child(42))` reduces the
lambda body in isolation (`child(42)` → `send(1, 42)`) and the runtime
spawns a static thunk. `spawn(fn () -> send(1, tag))` where `tag` is
opaque keeps the closure on the heap.

## Polymorphic library functions

The interesting case — a function exported for general use, called
from many places.

```
defmodule L do
  fn map(_, []), do: []
  fn map(f, [h | t]), do: [f(h) | map(f, t)]
end

fn user_a() do L.map(fn(x) -> x * 2, [1, 2, 3]) end
fn user_b(lst) do L.map(fn(x) -> x + 1, lst) end   # lst opaque
fn user_c(f, ys) do L.map(f, ys) end               # both opaque
```

- **user_a:** both args static. Full reduction → `[2, 4, 6]` as a
  constant. **Zero `map` bodies.**
- **user_b:** `f` static, `lst` opaque. Reduction stops at the call.
  **One specialized `map` body** with `+1` inlined into the loop. No
  `f` parameter.
- **user_c:** both opaque. **One polymorphic `map` body** with `f` as
  a parameter, invoked through a closure call per cell.

Total `map` bodies: **2**. One per equivalence class of *boundary
stops*, not one per callsite.

## What today's pipeline already does, partially

Several existing passes are doing pieces of this:

- `ir_inline` — non-recursive inlining (leaf-up pass).
- `ir_fold` — constant folding post-inline.
- `ir_dce` — dead code cleanup.
- `ir_fuse` — block fusion.
- `ir_typer`'s `narrow_for_cond` — pattern-vs-Descr narrowing.
- `closure_lit` — function identity through values.
- `fn_constants` — known-function propagation.

A coherent reducer pass would absorb these into one driver: walk from
program roots, reduce at each callsite, emit boundary bodies where
reduction stops. The current per-callsite spec-fanout shrinks
dramatically.

## Scope of analysis

Reduction is driven from **program roots**: `main`, every function
passed to `spawn`, and any function exported as a runtime entry point.
From each root the reducer walks the call graph; at each callsite it
reduces; results are memoized by `(fn_id, input_descrs)`. The memo
table is structurally today's spec table — but used as a cache for
reduction results, not as a registry of bodies to emit.

Bodies are emitted only at stops, not per public function. Public-vs-
private doesn't change the analysis; it changes what's reachable.

Whole-program compilation (one source tree, one `main`) is what fz
does today and what this design assumes. Separate compilation is a
larger change that's compatible in principle — libraries would ship
reducible IR plus types, and a final-link pass would specialize — but
it's out of scope here.

---

# Part 2: How the compiled code allocates

Reduction handles "should this code exist." But for the boundary
bodies that do exist, there's a separate question: when they
construct a cons cell, a tuple, a closure — does the runtime allocate
fresh memory, or can it reuse memory it was already going to free?

This question is largely orthogonal to reduction. The lore for it is
**Perceus**: precise reference counting with reuse analysis (Reinking,
Xie, de Moura, Leijen, ICFP 2021). Lean 4 and Koka use it in
production. Pure functional code over linked lists, trees, and structs
compiles to in-place updates without changing the source.

## The shape of the win

Take user_b's specialized `map` body:

```
fn map_specialized_for_user_b([]), do: []
fn map_specialized_for_user_b([h | t]), do: [h + 1 | map_specialized_for_user_b(t)]
```

Naive implementation: at every cons cell of the input, allocate a
fresh cons cell for the output. For an N-element list that's N
allocations on the way down (and N decrefs / GC traces on the way out).

With reuse analysis: at each step, the compiler observes that the
input cons cell is **about to be dropped** (its refcount reaches zero
right after we read `h` and `t`). Instead of freeing it and allocating
a fresh cell, **mutate the head slot in place** and reuse the cell as
the output. Same machine code shape as a hand-written destructive
loop. Same source as a pure functional definition.

This is the offer. It's the same offer Lean 4 makes today.

## How it composes with CPS

fz's IR is in CPS form: every `Term::Call` carries an explicit
`Cont { fn_id, captured }`. The cont's slot 0 *is* the destination for
the call's result. That's already half of **destination-passing style**:
the compiler always knows where the result of any call goes next.

Reuse analysis extends this: the cont can carry not just "where to put
the result" but "into which pre-allocated slot of which structure."
The producer writes directly into the destination. CPS makes this
information first-class in the IR — fz doesn't have to invent a new
calling convention to express it.

This generalizes what fz already does at `Term::TailCall`: when callee
and caller share frame shape, the frame is reused in place. Reuse
analysis applies the same idea to heap-allocated values, not just
stack frames.

## When is it safe?

Reuse is safe when the value being mutated is **unique** — no other
reference exists or will exist to it. Three traditions for proving
uniqueness:

- **Linear types** (Linear Haskell, Granule). The user declares
  linearity in types; the compiler checks. Most precise, most user
  burden.
- **Uniqueness types** (Clean, Mercury, Idris 2's `*`). The compiler
  infers from usage patterns; types carry a `*` qualifier.
- **Reference counting + reuse analysis** (Perceus, in Lean 4 and
  Koka). The compiler tracks refcounts at compile time; when it can
  prove RC=1 at a drop site, it rewrites to in-place mutation.
  Automatic, no user annotation.

**Perceus-style reuse analysis is the right fit for fz.** It's
automatic (no source change), composes with reduction without coupling
to it, and is validated in production. fz's set-theoretic Descrs give
it sharper handles than plain RC — uniqueness can be carried as a
property in the type lattice when it matters.

## What this does for the example programs

For the fully-reduced cases (ast_eval, fib_tailrec, list_primitives on
static lists, the closures-with-literal-captures cases), reuse
analysis has nothing to do. **The allocations were already dissolved
by reduction.** Reduction is the cheapest possible optimization for
allocation: don't have any.

For boundary bodies, reuse analysis pays:

- `map_specialized_for_user_b` over an opaque list: **zero
  allocations per step** if the list is unique (it usually is, fresh
  from the caller). In-place mutation; same code as a destructive
  loop.
- `count` over runtime integers: no heap allocations to optimize
  (everything is unboxed); reuse analysis has nothing to do.
- The receive boundary in `relay`: if the received message is unique
  (it is, fresh from the mailbox), `msg + 1` can write into wherever
  the result is destined without intermediate boxing.
- Closures with opaque captures: the closure heap object is fresh and
  unique; downstream code that reads its captures and produces a
  same-shape value can reuse the same memory.

The combined picture: **almost no runtime allocations survive the
combination of reduction and reuse.** The ones that do are the ones
that *have to* — genuinely shared data, GC-traced structures with
multiple live references, mailbox messages with multiple readers.

---

# Part 3: How the two compose

The pipeline:

1. **Reduce** from program roots. Static callsites collapse to
   constants; boundary bodies emerge with explicit Descrs.
2. **Linearity analyze** the boundary bodies. Mark each allocation
   site as unique or shared. fz's Descrs help here: set-theoretic
   types can carry uniqueness as a property.
3. **Reuse-rewrite.** Where producer-allocations and consumer-drops
   match shape and uniqueness, rewrite to in-place mutation. The
   cont's destination slot becomes a write target rather than a fresh
   alloc.
4. **Codegen.** Emit the now-rewritten bodies.

Each pass is local:

- Reduction doesn't need to know about linearity.
- Linearity doesn't need to know about reduction's choices.
- Reuse-rewrite doesn't add new shapes; it just turns
  alloc-then-write into write-through-pointer.

The interaction that matters: **reduction shrinks the surface area
that linearity has to be precise about.** A reduced program has fewer
allocation sites, and the ones it has tend to be in tight loops where
reuse wins are largest. Each pass makes the next pass's job easier.

---

# The user contract

Two predicates the user can keep in their head and reason about their
code's compiled shape from:

> **Number of bodies = number of opacity boundaries (after
> annotations).**

> **Number of allocations = number of (boundary-body × non-unique
> values) (after reuse analysis).**

Both are responsive to user input:

- **Annotations narrow opacity.** `@spec` on functions, typed receive,
  typed externs. Each is a firewall: code without annotations flows
  in whatever type inference can prove; code with annotations treats
  the annotation as ground truth downstream callers can rely on.
- **Sharing controls reuse.** Code that doesn't share values gets
  in-place mutation for free. Code that does share allocates;
  reference-counting paths apply.

Programs with no opacity and no sharing reduce to constants and
allocate nothing. Programs with both produce a body per boundary, an
allocation per shared value. **All of this is mechanically derivable
from source — no surprises, no per-program tuning.**

This is the user-facing offer:

- BEAM can't make it (no specialization, polymorphic everywhere).
- Erlang's dialyzer can't make it (under-approximate types, no
  specialization).
- Haskell-with-stream-fusion can make it for some idioms but requires
  user pragmas and rewrite rules.
- Lean 4 makes the allocation half (Perceus) cleanly.
- **fz can make both halves cleanly**, because the IR is already CPS,
  the type lattice is set-theoretic, and the closed-world assumption
  holds.

---

# Knobs

## Three the user gets

1. **`@spec` on functions.** A contract: "this function returns `T`."
   The compiler verifies the body satisfies it; downstream callers
   treat it as ground truth.
2. **Typed receive / typed mailbox.** "This process accepts messages
   of type `T`." Sends are type-checked; receives produce values of
   type `T` rather than `any`.
3. **Typed externs / FFI.** Same idea at the language boundary.

All three are firewalls that stop opacity (and therefore boundary
bodies) from propagating.

## Two the compiler gets

1. **Unroll budget.** Maximum reduction steps at a single callsite
   before emitting a body call. Default around 32. Caps explosion on
   large literal inputs.
2. **Inline budget.** When `f` is statically known but inlining it
   would produce a large body, prefer to emit a closure invocation.
   Mostly a future concern; default "always inline known `f`" works
   for current fz programs.

Both have sane defaults. Most programs never touch them.

## A possible fourth knob

Uniqueness annotations / hints (`@unique`, `@shared`) for cases where
the compiler can't infer linearity but the user knows the answer.
Probably optional, probably rare. Listed here only so the design
admits it.

---

# Where reduction stops, mechanically

A bullet list of the stop conditions, for reference:

- **Argument value is opaque** — Descr too wide to dispatch a clause.
- **Recursive call where structural decrease cannot be proven** —
  avoids infinite expansion.
- **Recursive call where structural decrease *is* provable but the
  unroll budget is exceeded** — cost-model cap.
- **`receive`** — always; output is the mailbox type (`any` if
  untyped).
- **Extern / FFI call** — output is declared, or `any` if undeclared.
- **Spawn of a value-flow closure where the captures aren't all
  static** — opaque-capture spawn emits a body; static-capture spawn
  reduces.

Everything else: the reducer continues, applying pattern dispatch,
substitution, arithmetic constant folding, and recursive reduction.

---

# What success looks like

For each fixture, a predicted shape — *body count* (user functions
only; `main` and externs are always emitted) and *allocation
character* (whether boundary-body allocations survive reuse analysis):

| Fixture | Bodies | Allocations |
|---|---|---|
| `polymorphic` | 0 | none |
| `higher_order` | 0 | none |
| `closure_typed_captures` | 0 | none (static captures dissolve) |
| `curried_add` | 0 | none |
| `ast_eval` (static AST) | 0 | none (full reduction) |
| `mutual_recursion(10)` | 0 | none |
| `fib_tailrec(20)` | 0 | none |
| `list_primitives` (static list) | 0 | none |
| `tail_recursion` (`count(100000, 0)`) | 1 | none (int loop, unboxed) |
| `concurrency_ping_pong` | 1 | message in mailbox (shared) |
| `relay` (untyped) | 1 | message + arithmetic box |
| `relay` (typed `int`) | 1 | none (unboxed int through) |
| `L.map(static_f, opaque_list)` | 1 | reuse cons cells in place |
| `L.map(opaque_f, opaque_list)` | 1 | reuse cons cells in place; closure dispatch per cell |

The CLIF for `ast_eval` drops from ~1400 lines to under 100. The
allocation count for any reduced program is zero. The boundary cases
match what a hand-tuned destructive implementation would produce.

These are **reviewable predictions, not numeric ones.** An agent
reading the generated CLIF and the per-fixture entry above can assess
whether the output is "reasonable for the source program" — the bar
the user can keep in their head.

---

# Prior art

The technique has 50 years of lore behind it.

## Part 1 (reduction)

- **Partial evaluation (PE).** Yoshihiko Futamura, 1971. The Futamura
  projections. Jones, Gomard, Sestoft's textbook *Partial Evaluation
  and Automatic Program Generation* (1993) is the canonical reference;
  free online.
- **Supercompilation.** Valentin Turchin, 1980s. PE pushed harder;
  drives reduction through branches.
- **Stalin** (Jeffrey Mark Siskind, 1990s, Scheme). Whole-program flow
  analysis + closure elimination. Close cousin to what we're
  describing.
- **MLton** (SML). Whole-program defunctionalization + per-call
  monomorphization. Production-grade example of aggressive
  specialization paying off on idiomatic functional code.
- **GHC's simplifier + specializer + stream fusion.** Less aggressive
  than Stalin / MLton; driven by `INLINE` / `SPECIALIZE` pragmas plus
  rewrite rules. The `list_primitives` payoff is what GHC's stream
  fusion delivers in production.
- **Truffle / Graal** (JVM). First Futamura projection applied at
  runtime: PE over an AST interpreter as a JIT strategy.

## Part 2 (reuse)

- **Perceus** (Reinking, Xie, de Moura, Leijen, ICFP 2021). Precise
  reference counting with compile-time reuse analysis. The seminal
  paper. Implemented in Lean 4 and Koka.
- **Linear Haskell** (Bernardy et al., POPL 2018). Linear types as a
  language extension for in-place updates.
- **Clean / Mercury** uniqueness types. Earlier (1990s) tradition of
  type-system-tracked uniqueness for in-place mutation.
- **Granule** (Orchard et al.). Modern research on graded modal types
  for resource-aware programming.
- **Destination-passing style** (DPS) as a compilation technique
  appears in several systems; see Shaikhha et al.'s work on
  DPS as a functional intermediate language for numerical code.

## What's specifically less well-trodden

- **Combining set-theoretic types (CDuce / modern Elixir) with PE-style
  specialization** to drive both. Set-theoretic types have a rich
  type-checking literature; using them as the binding-time lattice
  for a PE is not standard.
- **Combining whole-program PE with Perceus-style reuse.** Lean 4
  has Perceus but not aggressive PE; Stalin/MLton have aggressive PE
  but no reuse analysis. The combination is the prize.
- **Typed mailboxes as a PE input.** Erlang punts; Pony / Akka Typed
  have typed mailboxes but no aggressive specialization. The
  combination is the prize.
- **The user-facing contract.** "Body count = opacity boundaries;
  allocation count = boundary × non-unique" as teachable properties.
  Most existing systems do something like this but don't expose it
  as a property the user can reason about.

fz is a recognizable point in the design space — every individual
ingredient is published and validated. The combination, with this
user-facing contract, is novel as a coherent package.

---

# Status

This document captures **design intent** as agreed in discussion. No
tickets are committed. The intended next step is a tractable prototype:

> Write `effective_return_for(fn, input_descrs) -> Descr` as a pure
> query that uses the canonical body's typing rules to answer "what
> does `fn` return for input `D`" without minting a body. Implement
> on ast_eval only. Compare against today's per-spec returns. If it
> matches everywhere, the load-bearing piece of Part 1 works and the
> rest of the epic is engineering.

If that prototype succeeds, a rough ticket DAG follows:

## Part 1: reduction

1. Codegen-equivalence relation for Descrs / specs (pure analysis).
2. Reducer at callsites; spec-minting gated on stops.
3. Decouple per-callsite return queries from body-spec existence.
4. Typed receive (surface syntax + typer integration).
5. Send-site mailbox-type check.
6. `@spec` parse / verify / consume.
7. Diagnostic: "function `f` has N bodies because…"

## Part 2: reuse

8. Reference-count tracking through the typed IR (RC-aware lowering).
9. Reuse analysis (Perceus algorithm adapted to fz IR).
10. DPS rewrite (turn alloc-then-write into write-into-destination).
11. Diagnostic: "allocation at `f:L` was reused because the source at
    `g:M` is unique" / "could not be reused because…"

Parts 1 and 2 can land in either order; they're independent in
implementation. Landing Part 1 first is preferred because it shrinks
the surface area Part 2 has to analyze.

If the Part 1 prototype fails — if there's a case where the
return query can't be answered without minting a body — that's the
hopeless issue worth finding before any code lands. The cost of
finding it that way is one focused experiment.
