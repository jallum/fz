# Type Specialization

## Model

The engine gives every reachable function its type by **inferring it from the
body**, one call-contract at a time, as a **monotone worklist fixpoint** over the
CPS-lowered IR. Argument types flow in, the body's operations propagate
constraints, a return type flows out, and recursion converges by **widening** in a
finite-height lattice.

A parameter carries no type of its own. It does **not** start at `any`; an
activation supplies its input fact. Return cells start at **`Pending`** — no
callee result has been produced yet — and the first legal value lifts them into
the value lattice. A `@spec` is an optional pin on that inference, not its source:
the engine reaches the same types without one, just with fewer constraints to
lean on.

## The cell: information vs value

Each slot holds an `Info`, which separates *what we know* from *what the value
is*. A known value has two parts:

```text
Info      = Pending                   -- dependency has not produced a fact yet
          | Unknown                   -- live value, no determination yet
          | NoReturn                  -- path contributes no return value
          | Known(ValueFact)

ValueFact = { ty: Ty, proof: ValueProof }

ValueProof = Unproven
           | Exact(Ty)                -- exact witness in the existing type model
           | TupleFields([ValueProof])
           | MapFields({key => ValueProof}, complete?)
           | StructFields(module, {field => ValueProof})
           | MatcherMapHit(ValueProof)
           | MatcherMapMiss
```

`ty` is the visible type that flows out of inference. `proof` is temporary
branch-selection proof used by the pattern matcher and guard tests. Proof is not
the public type of the value and is erased by ordinary joins unless both inputs
prove the same fact. `Exact(Ty)` is deliberately a witness in the existing
`Types` model: the inference engine records it, but questions like "is this
witness a singleton int?", "does it fit this refined type?", and "is it
disjoint?" are delegated back to `Types`.

These are separate axes, and conflating them is the classic bug. Five roles,
only two of which live in the value ordering:

- **`Pending` is worklist latency** — a dependency has not produced its first
  fact yet. It is the activation-cell initialization identity and the recursive
  seed that lets a base case lift a return cell before the back-edge settles.
- **`Unknown` is live uncertainty** — a value may exist, but the engine has not
  proved its type yet. It is not "in" the value ordering; it is the absence of a
  point in it. In a control-flow join, a live `Unknown` arm must survive so the
  product boundary can consume it explicitly.
- **`NoReturn` is control-flow neutrality** — a path that produces no return value
  (`Halt`, proved-dead matcher arm). It contributes nothing to a sibling return
  arm, and if every path is `NoReturn`, the function boundary can report `none`.
- **`none` is the value-lattice bottom (⊥)** — the empty, uninhabited set. A
  *fact*: "no value, ever."
- **`any` is the value-lattice top (⊤)** — every value (dynamic). Also a fact —
  and one that must be **earned** (by a spec/type that explicitly declares top,
  by a join of real uses that genuinely reaches ⊤, or by final erasure of a
  residual `Pending`/`Unknown` at a product boundary), **never defaulted inside
  inference**.
  Seeding an undetermined slot at `any` is the same category error as seeding it
  at `none`: both assert a fact where the truth is "not yet determined."

```text
                    Known(any)            ⊤  value top      (earned, never defaulted)
                   /    |     \
               int    float   {:cont, int} …
                   \    |     /
                    Known(none)           ⊥  value bottom   (empty / uninhabited)

       Pending   ── worklist latency; activation-cell identity
       Unknown   ── live uncertainty; off to the side
       NoReturn  ── control-flow join identity; no produced value
```

## The join

There are two joins, because "pending inference" and "this path does not return"
are different:

```text
cell_update(Pending, x)         = x                 -- first result initializes the cell
cell_update(Unknown, x)         = Unknown           -- live uncertainty is sticky
cell_update(NoReturn, x)        = x
cell_update(Known(a), Known(b)) = Known({
  ty: refine_widen(a.ty, b.ty),
  proof: a.proof if a.proof == b.proof else Unproven
})

branch_join(Pending, x)         = x                 -- recursion seed / not ready yet
branch_join(Unknown, x)         = Unknown           -- a live unknown arm is still live
branch_join(NoReturn, x)        = x                 -- a non-returning arm contributes nothing
branch_join(Known(a), Known(b)) = Known(a ⊔ b)
```

So a slot only ever ascends: `Pending ⊑ Known(int) ⊑ Known(int | float) ⊑ …`. The
first value carries it *from the information-neutral up into the value lattice*;
subsequent values union in.

The value-union stays **precise** — it does not invent a coarse supertype. There
is **no `number` rung**: `int ⊔ float = int | float`, kept discriminated, never
widened to `number` or `any`. Unions form only over **legal** states; a
rule/spec violation does not join into a wider union, it produces `none` (see
Operators).

## Two lattices for termination

Within `Known` types there are two lattices. The exact set-theoretic lattice
(`set-theoretic-types.md`), whose join is `union`, is exact but **infinite
height** (`1 | 2 | 3 | …` never stops), so a fixpoint run directly over it need
not terminate. Widening therefore uses a second, **finite-height** refinement
lattice — int and float are siblings, with no rung between them:

```text
int_lit(1)            ⊑ int      ⊑ any
float_lit(2.0)        ⊑ float    ⊑ any
[] | nonempty_list(a) ⊑ list(a)  ⊑ any
&fnN[c…]:(A…)->R       ⊑ (A…)->R  ⊑ any
```

`refine_widen(a, b)` is `union(a, b)` collapsed to this finite height
(`widen_for_recursive_spec_key`): literal axes drop to their base
(`int_lit(42) → int`) and recursive structure is bounded. Because every chain is
bounded, repeated widening of a slot steps up only finitely often. This is the
sole termination mechanism for *slots*; there are no per-slot heuristics and no
special case for "recursive" or "callback" parameters.

## Operators are functions with signatures, applied strictly

Every operation is a **call against a signature** — including the ones that look
like syntax. The engine does not invent operator semantics; it applies the
operator's real clause set to the operand types. `+` is the four-clause Elixir
signature, not a coarse `(number, number) -> number`:

```text
+ : (int,   int)   -> int
  | (int,   float) -> float
  | (float, int)   -> float
  | (float, float) -> float
```

Application is **strict** and three-way:

```text
apply(+, a, b) =
  Pending                                         if a or b is Pending
  Unknown                                         if a or b is live Unknown
  ⋃ { C.ret : clause C whose domains a, b inhabit }   if a, b are in-domain
  none                                            otherwise (an operand escapes)
```

- **`Pending` in ⇒ `Pending` out; `Unknown` in ⇒ `Unknown` out.** You cannot pick
  a clause without the operand, and you must not guess `any` or `none`; recompute
  when a pending dependency arrives, or carry live uncertainty to the boundary.
- **In-domain ⇒ the union of the returns of the clauses the operands hit** — so
  `int + int = int`, `int + float = float`, and `(int | float) + int = int |
  float`. Precise, no `number` collapse.
- **Out-of-domain ⇒ `none`.** `{:cont, int} + int` matches no clause — an illegal
  state. The result is `none`; it is *not* laundered into a partial `int`. The
  domain check is *consistent*-subtyping, so a dynamic `any` operand is still
  allowed; it is a *concrete* type outside the domain that fails.

Because an operator's result is bounded by its declared return set, operator
results have **finite height by construction** — they can never carry operand
structure forward and grow without bound. This is the second, complementary bound
to slot-widening: **operators bound their returns; slots bound their accumulated
unions.** Both are needed for the fixpoint to settle.

## The non-answers

`none`, `Pending`, `Unknown`, and `NoReturn` are not usable values, and they mean
different things:

- **`Known(none)` reached where a value is required** = a *proved* contradiction
  (e.g. `+` on operands outside its domain, or projecting a tuple field no
  feasible tuple value has). The program is ill-typed *there*. The production
  transplant must surface this as a diagnostic stop; it must not be laundered
  into a later wider result.
- **`Pending` at the settled fixpoint** = a dependency cycle never produced a
  first fact. That is an analysis gap for supported code.
- **`Unknown` at the settled fixpoint** = the engine *could not determine* a type:
  no constraint and no spec ever reached the slot. It is the absence of an answer.
- **`NoReturn` at a control-flow join** = a path that produces no value for the
  current continuation. It is neutral beside a returning sibling, and only becomes
  `none` at a function/product boundary if no returning path remains.

`Pending` and `Unknown` are inference scaffolding, never public types. At a
settled fixpoint a surviving `Unknown` is either under-specification (needs a
spec), an engine coverage gap (a construct not yet modeled), or an intentionally
dynamic edge that cannot be represented more tightly. The product boundary must
consume it explicitly: diagnose/stop for unsupported required knowledge, mark a
proven inaccessible path dead, or erase the still-live value to `any`. It must
not silently become `none`; `none` requires proof that no value exists.

A callee whose return has not been computed stays `Pending` while the worklist is
running. A fallback or fail arm becomes `NoReturn` when proved unreachable; if it
is still live but unsupported, it stays `Unknown`. A declared-spec lookup follows
the same rule: if the matcher cannot prove a matching arrow, the spike keeps the
result `Unknown`; it does not invent `none` from an underconstrained or
unsupported scheme match.

`any` follows the same discipline from the other end of the lattice. It is not a
projection fallback. Reading a tuple field projects across feasible tuple clauses;
clauses that are contradictory (for example, a conjunction that would require the
same value to be both a 2-tuple and a 3-tuple) contribute no proof. If no
feasible tuple has the field, the projection is `none`; if the input is still
pending or live-unknown, the projection preserves that state.

## Pattern proof

The pattern matcher is a proof producer. Its lowered tests (`type_test`,
`is_nil`, `is_list_cons`, equality against constants) attach facts to condition
vars. An `if` over such a condition does not blindly walk both arms under the
same environment: the true and false environments are refined by the predicate,
and a branch whose refinement is empty contributes no return information.
Constructors must preserve the facts those tests consume: for example, a list
literal with at least one explicit element is `nonempty_list(T)`, not merely
`list(T)`, so the top of the decision tree can prove `is_nil` false and
`is_list_cons` true.

For a multi-clause function, each activation is processed against the same
decision tree, but with that activation's input facts. A direct call
`pick(:left)` and a direct call `pick(:right)` are two activations of the same
`FnId`; the matcher proof lets them select different leaves. A deliberate
union-input activation, such as calling one function value at `:left | :right`,
may still join both leaves and widen the result.

Guards consume the same proof channel. Numeric literals are visible as
`int`/`float` in `ty`, but retain an exact proof witness long enough for lowered guard
predicates such as `x > 0` to become `true` or `false` when the matched payload
came from a literal.

Tuple construction stores proof per field. Each field is `Unproven` until that
field has its own proof, so a tuple with one proven payload does not become a
fully proven tuple literal. Projection carries the selected field's proof
forward: a source value like `{:ok, 1}` has visible type `{:ok, int}`, while the
projected payload still carries proof `1` for guard selection. Returning that
payload still returns visible type `int`; proof is not reanimated as a public
singleton type.

Map construction follows the same key-wise rule. A static-key map literal stores
proof per key and marks the key set complete; map update preserves or replaces
only the updated key proofs. The matcher-only `MatcherMapGet` consumes that key
proof and produces either `MatcherMapHit(value-proof)` or `MatcherMapMiss`.
`IsMatcherMapMiss` consumes that private control proof to select the decision
tree arm. The miss sentinel is never a public type; ordinary field type and key
semantics still come from `Types::map`, `map_field_lookup`, and `map_top`.

Schema-backed struct construction follows the same field-wise rule. The visible
type is the existing opaque impl-target type (`impl-target::Range`, etc.), so
protocol dispatch and nominal checks still go through `Types`; the proof stores
only per-field facts keyed by the declared schema name. `StructField` projects
the visible field type through `Module::struct_schemas` plus `opaque_inners`, and
projects the matching field proof if it still fits that visible type. A struct
with one proven field is not a proven aggregate; it is an aggregate whose one
field can help the matcher or guard reducer choose a branch.

## Closures are functions with capture parameters

A closure is an ordinary function whose first *k* parameters are **captures**,
bound at creation to the values in scope:

```text
fn (entry, inner) -> g.(entry, inner)     is     λ(g ; entry, inner) -> g.(entry, inner)
```

Captures are inputs like any other — bound to **known-typed values** at the
`MakeClosure` site — so a closure's type is inferred from its body exactly as a
named function's is, and is as concrete as its captures are. A closure value
carries its captures' types:

```text
&fnN[5]:(α, α) -> α                        capture is int        — concrete
&fnN[(int,int)->int]:(int,int) -> int      capture is a closure  — also concrete
```

A captured closure is therefore *not* a special case: it is a concrete-typed
capture, indistinguishable from a captured `int`. Nesting depth is fixed by the
source — a closure can only capture the finitely many closures written above it —
so capture types have bounded structure, and the leaves inside them widen on the
same finite chains as everything else.

A named-function reference (`&Mod.fn/2`) is the degenerate case: a closure with
**no captures**. It is just another call edge, specialized by the argument types
it is eventually applied with — nothing special, and nothing that grows.

## Specialization is a worklist fixpoint

`FnId` is the body/callable identity. It owns the code being analyzed and remains
the runtime target for direct calls, closure bodies, and protocol impl bodies. It
is **not** the inference instance: one `FnId` may be called at several concrete
input shapes without those callers sharing one joined return cell.

An **activation** is the monomorphic inference instance for one reachable
call-contract. It is keyed by `FnId` plus a canonical input tuple of
`ValueFact`s: widened visible type plus any still-live proof. For ordinary
direct calls the tuple corresponds to the parameter values. For closure bodies
the internal tuple is `capture-values ++ parameter-values`, because captures are
leading entry parameters in the lowered body. That internal tuple is for
inference only: the closure's callable surface remains its ordinary parameters,
with captures loaded from the closure environment after this phase.

The worklist holds activations whose return estimate may have changed:

- A call instantiates the callee's signature against the incoming argument types
  and records a return-read dependency from caller to callee.
- A recursive function's parameter slots are the **join, across every call site
  including the back-edge**, widened in the refinement lattice. Slots that shrink
  (`nonempty_list(int)` then `[]`) ascend to their LUB (`list(int)`); slots that
  never change (the accumulator's type, the reducer) stay put.
- When a callee's return ascends, its readers are rescheduled. When a capture's
  type changes — because the engine learned more about the function that built the
  closure — the closure activation is rescheduled, and its readers with it.
- A protocol-dispatch stub is **devirtualized on its receiver's type** before the
  call: the single impl whose target type the receiver is a subtype of. Until the
  receiver is `Known`, the call yields `Pending` and is retried as the receiver
  ascends.

The fixpoint halts when no activation's inputs or return are still moving.

## Why it terminates

The worklist is a standard monotone fixpoint, and the premises hold:

- **Monotone** — a slot's type only ascends (`Pending ⊑ Known(t) ⊑ Known(t ⊔ t')`);
  it never oscillates down.
- **Finite height (slots)** — every leaf rides a bounded refinement chain
  (`int_lit ⊑ int ⊑ any`), and recursive structure is bounded by
  `widen_for_recursive_spec_key`.
- **Finite height (operators)** — an operator returns within its declared return
  set, so it cannot carry operand structure forward.

Recursion is safe for the same reason: in `go(t, f.(h, acc), f)`, `f` is passed
unchanged, so `join(f, f) = f` — a loop-invariant concrete closure is already a
fixpoint, and only the data and accumulator slots move, each by a bounded number
of rungs.

## Worked example

```fz
fn go(list, acc, f) do
  case list do
    [] -> acc
    [h | t] -> go(t, f.(h, acc), f)
  end
end

fn myreduce(list, acc, g) do
  go(list, acc, fn (entry, inner) -> g.(entry, inner) end)
end

myreduce([1, 2, 3], 0, fn (x, a) -> x + a end)
```

```text
U = fn (x,a) -> x + a       body ⇒ +(x,a) with x,a : int ⇒ (int, int) -> int   — concrete
g = U                        myreduce's capture-source is U
W = fn (e,i) -> g.(e,i)      captures concrete g ⇒ (int, int) -> int
go(nonempty_list(int), int, &W[U]:(int,int)->int)
   f.(h, acc) : int          acc joins int ⊔ int = int   (fixpoint, no rung needed)
   list slot  : nonempty_list(int) ⊔ [] = list(int)      (one rung)
   f          : unchanged — fixpoint
go : int  ⇒  myreduce : int
```

If instead the reducer returned `{:cont, x + a}` (the `Enumerable.reduce` /
`reduce_while` contract, misapplied to `Enum.reduce`), `acc` would join
`int ⊔ {:cont, int}`, and the next `acc + entry` would evaluate
`{:cont, int} + int` — outside `+`'s domain ⇒ `none`. The accumulator settles at
`int | {:cont, int}` and the `+` site is `none`: a *proved* contradiction, the
seam for a located diagnostic, not a divergence.
