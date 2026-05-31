# Control-Flow Lowering

Branching constructs lower through explicit continuation functions:

- an outer function evaluates the selector/test and routes to an arm function;
- each arm function evaluates one source arm;
- non-tail constructs add a join function that receives the arm value and
  continues surrounding code.

That join is part of the source expression. Therefore an arm expression is in
tail position only when the whole branching construct is in tail position. If a
non-tail `if`, `case`, `cond`, `with`, or `receive` arm contains a call, lowering
must treat that call as non-tail so the call's continuation can pass its result
to the construct join.

Example:

```fz
next = if rem(index, nth) == 0, do: fun.(head), else: head
[next | rest]
```

The `fun.(head)` call does not return from the `if_then` arm directly. It produces
the `if` value, then the `if_join` continuation binds `next` and lowers
`[next | rest]`.

The invariant is simple: branch-local tailness follows the construct's join
shape, not the fact that the arm body is syntactically last inside its helper
function.
