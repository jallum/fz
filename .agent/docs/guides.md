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

The existing guides usually follow this arc:

1. Give the friendly idea.
2. Show the smallest useful syntax.
3. Walk what happens step by step.
4. Explain the runtime model behind the behavior.
5. Give a complete fixture-style example.
6. End with footguns and the contract.

Use a table of contents. Keep section titles plain and numbered.

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

Use callouts for mental models, contracts, and warnings.

Patterns already used:

- blue aside: mental model or behind-the-scenes explanation
- yellow box: footgun
- green box: contract or reassuring invariant

Do not use callouts as decoration. They should make the main lesson easier to
remember.

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
