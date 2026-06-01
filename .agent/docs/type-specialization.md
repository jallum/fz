# Type Specialization

## Model

The engine gives every reachable function its type by **inferring it from the
body**, one call-contract at a time, as a **monotone worklist fixpoint** over the
CPS-lowered IR. Argument types flow in, the body's operations propagate
constraints, a return type flows out, and recursion converges by **widening** in a
finite-height lattice.

A parameter carries no type of its own. It does **not** start at `any`; it starts
at **`Unknown`** — the absence of a determination — and the first legal value it
receives lifts it into the value lattice. A `@spec` is an optional pin on that
inference, not its source: the engine reaches the same types without one, just
with fewer constraints to lean on.

## The cell: information vs value

Each slot holds an `Info`, which separates *what we know* from *what the value
is*. A known value has two parts:

```text
Info      = Unknown                   -- neutral: no determination yet
          | Known(ValueFact)

ValueFact = { ty: Ty, proof: ValueProof }

ValueProof = Unproven
           | Exact(Ty)                -- exact witness in the existing type model
           | TupleFields([ValueProof])
           | MapFields({key => ValueProof}, complete?)
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

These are separate axes, and conflating them is the classic bug. Three roles,
only two of which live in the value ordering:

- **`Unknown` is neutral** — the *identity* of the join, not a least element.
  `widen(Unknown, x) = x`: it contributes nothing and is *displaced* by the first
  legal value. It is not "in" the value ordering; it is the absence of a point in
  it. (Pedantically it is the bottom of the *information* semilattice, but we say
  "neutral" to refuse overloading "bottom" across two lattices.)
- **`none` is the value-lattice bottom (⊥)** — the empty, uninhabited set. A
  *fact*: "no value, ever."
- **`any` is the value-lattice top (⊤)** — every value (dynamic). Also a fact —
  and one that must be **earned** (by a spec/type that explicitly declares top,
  or by a join of real uses that genuinely reaches ⊤), **never defaulted**.
  Seeding an undetermined slot at `any` is the same category error as seeding it
  at `none`: both assert a fact where the truth is "not yet determined."

```text
                    Known(any)            ⊤  value top      (earned, never defaulted)
                   /    |     \
               int    float   {:cont, int} …
                   \    |     /
                    Known(none)           ⊥  value bottom   (empty / uninhabited)

       Unknown   ── neutral; off to the side, the join identity
```

## The join

One operator does both the information-lift and the value-union, because
`Unknown` is the value-join's identity:

```text
widen(Unknown, x)         = x                       -- first legal value lifts the slot
widen(x, Unknown)         = x
widen(Known(a), Known(b)) = Known({
  ty: refine_widen(a.ty, b.ty),
  proof: a.proof if a.proof == b.proof else Unproven
})
```

So a slot only ever ascends: `Unknown ⊑ Known(int) ⊑ Known(int | float) ⊑ …`. The
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
  Unknown                                         if a or b is Unknown
  ⋃ { C.ret : clause C whose domains a, b inhabit }   if a, b are in-domain
  none                                            otherwise (an operand escapes)
```

- **`Unknown` in ⇒ `Unknown` out.** You cannot pick a clause without the operand,
  and you must not guess `any` or `none`; recompute when it arrives.
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

## The two non-answers

`none` and `Unknown` are the two results that are not a usable value, and they
mean opposite things:

- **`Known(none)` reached where a value is required** = a *proved* contradiction
  (e.g. `+` on operands outside its domain, or projecting a tuple field no
  feasible tuple value has). The program is ill-typed *there*. The production
  transplant must surface this as a diagnostic stop; it must not be laundered
  into a later wider result.
- **`Unknown` at the settled fixpoint** = the engine *could not determine* a type:
  no constraint and no spec ever reached the slot. It is the absence of an answer.

`Unknown` is iteration scaffolding, never a result — so it **may not appear in a
product**. At a settled fixpoint every reachable slot must be `Known`; a surviving
`Unknown` is either an under-specification (needs a spec) or an engine coverage
gap (a construct not yet modeled), and the distinction is exactly the
`Unknown ≠ none ≠ any` separation above.

A fallback, fail arm, or unresolved callee stays `Unknown` while the worklist is
running. It becomes dead/inaccessible only after the fixpoint has enough proof
to prove no live input reaches it. A declared-spec lookup follows the same rule:
if the matcher cannot prove a matching arrow, the spike keeps the result
`Unknown`; it does not invent `none` from an underconstrained or unsupported
scheme match.

`any` follows the same discipline from the other end of the lattice. It is not a
projection fallback. Reading a tuple field projects across feasible tuple clauses;
clauses that are contradictory (for example, a conjunction that would require the
same value to be both a 2-tuple and a 3-tuple) contribute no proof. If no
feasible tuple has the field, the projection is `none`; if the input is still
unknown, the projection remains `Unknown`.

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

Structs should use the same field-wise shape when added: each declared field
starts `Unproven` until that field has its own proof. An aggregate with one
proven field is not a proven aggregate; it is an aggregate whose one field can
help the matcher or guard reducer choose a branch.

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
  receiver is `Known`, the call yields `Unknown` and is retried as the receiver
  ascends.

The fixpoint halts when no activation's inputs or return are still moving.

## Why it terminates

The worklist is a standard monotone fixpoint, and the premises hold:

- **Monotone** — a slot's type only ascends (`Unknown ⊑ Known(t) ⊑ Known(t ⊔ t')`);
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
