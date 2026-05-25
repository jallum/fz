# Agent Docs

Agent docs are memory for future work. They should help the next agent make the
right move quickly by giving them the subsystem's working model.

## Shape

Write the doc for the moment when someone asks:

```text
Give me the subsystem model I need before I edit it.
```

Good agent docs are:

- short
- explanatory
- concrete
- current
- easy to scan

They are not research logs. Research is staging: use it to learn, then promote
the durable model into a doc and delete the stale notes.

## Start With The Model

Say what the subsystem is for and name the few pieces that matter. A reader
should be able to draw the box-and-arrow sketch in their head before they see a
list of cautions.

Good:

```text
AnyValueRef is one opaque runtime word. Scalars and heap objects differ behind
that word, but callers pass the same shape through the interpreter, REPL, JIT,
and AOT paths.
```

Weak:

```text
Do not split ValueRef into payload plus kind.
```

The weak version may be true, but it does not teach the model. It leaves the
next agent obeying a rule instead of understanding the reason the rule exists.

## Use Tiny Walkthroughs

Examples should show how data moves through the system. Keep them tiny enough
that the reader can simulate the path without needing the whole codebase open.

Good:

```text
send(pid, 42)
  box 42 only because send takes any
  store ValueRef(Int) in the mailbox
```

Weak:

```text
For example, in a larger program with several calls and a scheduler...
```

## Name The Pieces

Most mistakes happen when two pieces both seem responsible for the same thing.
Name each major component and the state or decision it owns.

Examples:

```text
Public ABI: one any value ref.
Heap internals: layout-local metadata.
Tests: telemetry proves the decision; structure proves the artifact.
```

Boundaries still matter. They should appear as policy choices after the reader
understands the pieces, not as an opening wall of prohibitions.

## Explain Policy Choices

Policy choices answer:

```text
When two designs are possible, which one does this subsystem choose?
```

Good policy sections say the choice, the reason, and the observable contract.

```text
REPL user code runs on IrInterpRuntime, not the compile-time evaluator. That
keeps interactive code on the same runtime path as ordinary programs, so spawn,
receive, resources, and heap values behave the same at the prompt.
```

Avoid naked warnings unless the warning is the policy.

## Cut Without Mercy

Delete anything that does not help the next agent build the right mental model
or make the right edit.

Keep:

- plain subsystem explanation
- major components and ownership
- dataflow through the components
- policy choices and invariants
- tiny walkthroughs
- proof gates

Use sparingly:

- forbidden shapes, only after the correct shape is clear

Cut:

- chronology
- stale research
- vague warnings
- repeated examples
- implementation details that are easy to rediscover
- motivation already captured by the model

## Proof Gates

End with the concrete checks that prove the model still holds. Prefer named
tests, fixture legs, telemetry assertions, manual smoke checks, or exact
commands over broad advice.

Good:

```text
Gate this model with:
- cargo test repl::tests::composer_accepts_complete_multiline_expression_chunks_from_editor
- cargo test --test fixture_matrix repl
- manual terminal smoke for Ctrl-C, Ctrl-D, history, and multiline entry
```

Weak:

```text
Make sure it works.
```

## Final Check

Before saving, ask:

```text
Could a new agent explain the subsystem, name the ownership boundaries, and
choose the right test in two minutes?
```

If not, make the model clearer. Shorter is useful only when it still explains
the system.
