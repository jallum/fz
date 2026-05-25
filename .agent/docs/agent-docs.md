# Agent Docs

Agent docs are memory for future work. They should help the next agent make the
right move quickly.

## Shape

Write the doc for the moment when someone asks:

```text
What should I remember before touching this?
```

Good agent docs are:

- short
- opinionated
- concrete
- current
- easy to scan

They are not research logs. Research is staging: use it to learn, then promote
the durable rule into a doc and delete the stale notes.

## Start With The Rule

Say the important thing first.

Good:

```text
Generated code carries ValueRef as one opaque word. Do not split it into
payload plus kind.
```

Weak:

```text
Historically, we tried several representations before arriving at the current
approach...
```

## Use Tiny Examples

Examples should remove doubt, not tell a story.

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

## Name The Boundary

Most mistakes happen at boundaries. Be explicit about them.

Examples:

```text
Public ABI: one any value ref.
Heap internals: layout-local metadata.
Tests: telemetry proves the decision; structure proves the artifact.
```

## Cut Without Mercy

Delete anything that does not change what the next agent will do. 

Keep:

- rules
- invariants
- forbidden shapes
- small examples

Cut:

- chronology
- motivation already captured by the rule
- vague warnings
- repeated examples
- implementation details that are easy to rediscover
- stale research that no longer changes what to do

## Final Check

Before saving, ask:

```text
Would this help me make a correct edit in two minutes? Is this ELI5?
```

If not, shorten it or leave the detail out.
