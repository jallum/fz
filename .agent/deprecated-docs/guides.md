# User Guides

`guides/*.html` are for people learning fz. They are not agent memory and not
compiler notes.

## Purpose

A guide should help a reader build a working mental model:

```text
What is this feature for?
How do I use it?
What should I expect at runtime?
What can bite me?
```

Start from the user's problem, then explain the machinery only when it helps
predict behavior.

## Shape

Every guide opens with an `<h1>` and a one-line `<p class="subtitle">` that
says, in plain words, what the page teaches.

The reference-style guides then follow this arc:

1. Give the friendly idea.
2. Show the smallest useful syntax.
3. Walk what happens step by step.
4. Explain the runtime model behind the behavior.
5. Give a complete fixture-style example.
6. End with footguns and the contract.

These guides carry a numbered `<ul class="toc">` of links to their sections,
and the `<h2>` section titles are plain and numbered to match. A narrative essay
guide skips the table of contents and uses unnumbered headings instead; that is
the exception, not the default.

Good:

```html
<h2 id="send">4. send — putting a message in someone's mailbox</h2>
```

Weak:

```html
<h2 id="send">4. Runtime mailbox enqueue semantics</h2>
```

## Voice

Friendly, direct, ELI5. Assume the reader is smart but new to the concept.

Good:

```text
A process is a tiny independent program with a private inbox.
```

Weak:

```text
Process isolation is implemented by disjoint heap ownership.
```

You can introduce precise terms, but earn them with examples first.

## Examples

Use examples a user could imagine writing:

```text
spawn(worker)
send(pid, {:reply, ref, value})
receive do ... end
```

Then explain what fz does with them. Prefer step-by-step walkthroughs over
abstract declarations.

Good examples are:

- small
- runnable-looking
- tied to the surrounding paragraph
- annotated only where the annotation teaches something

## Implementation Detail

Implementation detail belongs in a guide only when it explains user-visible
behavior.

Good:

```text
Messages are deep-copied, so the sender and receiver never share mutable state.
```

Weak:

```text
The send path calls Runtime::send_via_current_runtime.
```

Use internal names sparingly. If a name appears, immediately translate it into
what the user should understand.

## Callouts

`guides/style.css` defines the callout shapes. Each color carries a meaning:

- `<div class="aside">` — blue left-border block for a mental model or a
  behind-the-scenes explanation. This is the workhorse, the most-used callout.
  Most open with plain prose; some open with a bold lead-in such as
  `<strong>Mental model:</strong>`.
- `<div class="box yellow">` — footgun. Opens with the hazard in bold, e.g.
  `<strong>Externs are an unsafe surface.</strong>`.
- `<div class="box green">` — contract or reassuring invariant.
- `<div class="box blue">` — the boxed blue variant: a full bordered box
  (rather than a left-border aside) for an important note, a constraint or
  contract that wants box framing, or a labeled set of related items.

`style.css` also defines `.box.red`; no guide uses it.

A callout earns its place by making the main lesson easier to remember, not by
decorating the page.

## Contract

Every guide should leave the reader with a compact contract.

Examples:

```text
Processes do not share memory. They exchange deep-copied messages.
```

```text
Declare the C signature truthfully. Pick the right marshal class.
```

The contract is the reader's rule of thumb after they forget the details.

## Before Editing

Before changing a guide, verify facts in code or fixtures. User-facing docs
must not repeat stale implementation plans.

Good sources:

- fixtures that demonstrate the behavior
- runtime/compiler code that owns the behavior
- tests that pin the behavior

If a fact is only a future plan, say so plainly or leave it out.
