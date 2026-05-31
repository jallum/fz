# Type Specialization

## Model

The planner gives every function its type by **inferring it from the body**, one
call-contract at a time. A parameter carries no type of its own — it starts at
`any`, and each operation in the body *refines* it. A `@spec` is an optional pin
on that inference, not its source: the planner reaches the same types without
one, just with fewer constraints to lean on.

Specialization is a **monotone worklist fixpoint**. Argument types flow into a
function, the body's operations propagate constraints, a return type flows out,
and recursion converges by **widening** in a finite-height lattice. Three pieces
carry the whole model:

```text
refinement lattice   the finite-height join used for widening
spec                 a (function, input-types) node — one call-contract
worklist             monotone propagation with dependency rescheduling
```

## Two lattices

Types live in the set-theoretic lattice (`set-theoretic-types.md`), whose join is
`union`. That lattice is exact and has **infinite height** — `1 | 2 | 3 | …`
never stops ascending — so a fixpoint run directly over it need not terminate.

Widening uses a second, coarser lattice of **finite height**: the refinement
order, where each type is a refinement of a more general one.

```text
int_lit(1)            ⊑ int   ⊑ number ⊑ any
float_lit(2.0)        ⊑ float ⊑ number ⊑ any
[] | nonempty_list(a) ⊑ list(a)        ⊑ any
&fnN[c…]:(A…)->R      ⊑ (A…)->R         ⊑ any
```

`widen(a, b)` is the least upper bound *in this lattice* — the smallest type at
least as general as both. Because every chain is bounded, repeated widening of a
slot can only step up finitely often. This is the sole termination mechanism;
there are no per-slot heuristics deciding what to widen, and no special case for
"recursive" or "callback" parameters. A slot's widened type is just the LUB of
the types it is observed to take, and a slot whose value never changes is its own
LUB — invariance falls out, it is not detected.

## Functions are parametric; the body constrains

A parameter begins at the top of the lattice (`any`) and the body pushes it down.
Every operation is a **call against a signature** that constrains its operands
and yields a result — and that includes the ones that look like syntax:

```text
a + b        is  +(a, b)        with  +  : (number, number) -> number
f.(x, y)     is  apply(f, x, y) with  f  : (A, B) -> R
g(x)         is  a named call   with  g  's inferred or declared signature
```

So `fn add(a, b), do: a + b` has principal type `(number, number) -> number`: the
`+` signature alone refines `a` and `b` off `any`. A `@spec add(integer, integer)`
narrows that further; its absence costs precision, not correctness. There is one
constraint mechanism — signature application — so two paths cannot impose the same
constraint differently.

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

## Specialization is a worklist fixpoint

A **spec** is keyed by a function and its input types, where inputs are
`capture-types ++ parameter-types` — the full call-contract. The worklist holds
specs whose inputs have changed:

- A call instantiates the callee's signature against the incoming argument types
  and records a return-read dependency from caller to callee.
- A recursive function's parameter slots are the **join, across every call site
  including the back-edge**, widened in the refinement lattice. Data slots that
  shrink (`nonempty_list(int)` then `[]`) ascend to their LUB (`list(int)`);
  threaded slots that never change (the accumulator's type, the reducer) stay put.
- When a callee's effective return changes, its readers are rescheduled. When a
  capture's type changes — because the planner learned more about the function
  that built the closure — the closure's spec is rescheduled, and its readers
  with it.

The fixpoint halts when no spec's inputs or return are still moving.

## Why it terminates

The worklist is a standard monotone fixpoint, and all three premises hold:

- **Monotone** — a slot's type only ascends the refinement lattice (joins are
  upward); it never oscillates down.
- **Finite height** — every leaf rides a bounded chain
  (`int_lit ⊑ int ⊑ number ⊑ any`, `[] | nonempty(a) ⊑ list(a) ⊑ any`).
- **Bounded structure** — capture nesting is static, so widening refines the
  leaves inside a fixed-shape type and never grows the shape.

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
U = fn (x,a) -> x + a       body ⇒ (number, number) -> number        — concrete, no call site needed
g = U                        myreduce's capture-source is U
W = fn (e,i) -> g.(e,i)      captures concrete g ⇒ (number,number)->number, capture concrete
go(nonempty_list(int), int, &W[U]:(number,number)->number)
   f.(h, acc) : number       acc joins int ⊔ number = number  (one rung)
   list slot  : nonempty_list(int) ⊔ [] = list(int)            (one rung)
   f          : unchanged — fixpoint
go : number  ⇒  myreduce : number
```

The closure `W` capturing a closure `U` settles for the same reason `&fnN[5]`
does: `U`'s type is inferred concrete from its body, so the capture is concrete,
so the spec key repeats and the fixpoint lands.
