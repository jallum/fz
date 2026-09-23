# Predict, Measure, Collapse

A repair needs to explain two things: why the result is correct, and why the
system does exactly the work it does. A compiler can produce the right type
while repeatedly computing and discarding intermediate answers. Checking only
its final output misses that defect.

Use this strategy when work is unexplained or several mechanisms appear to
answer the same question. It extends the
[Output Contract Loop](output-contract-loop.md): reduce the problem, derive the
answer, predict the work, and compare both with a measurement. Collapse means
moving each decision to one owner and removing the mechanisms it replaces.

## Start with an answer you can derive

Reduce the failing program until you can solve it by hand. Keep the feature
that causes the failure; remove unrelated computation. The original program
remains a later check that the repair works in context.

Write the intended answer beside the reduced fixture. For compiler work, include
which activations exist, what distinguishes their keys, and what each returns.
An activation is a function specialized for a particular argument key. These
identities matter: two activations with the same return type can still represent
unnecessary duplication.

For example, suppose a function returns either an integer or a list containing
its recursive result. Its return satisfies:

```text
R = int | [R]
```

The answer is a recursive type: an integer, or a list whose elements have that
same type. The notation `μX. int | [X]` gives this infinite family a finite
name. Successive approximations such as `int`, `int | [int]`, and
`int | [int | [int]]` each describe only part of it.

This paper answer is the specification. If the intended model cannot express
it, record that limitation. Replacing it with a broader answer merely to make
the computation stop leaves the original requirement unmet.

## Predict the work before changing the implementation

Starting from the paper answer, work backwards through its prerequisites.
Identify the component that owns each decision, the facts it needs, and the
components that consume its answer. Examine existing code that already answers
the question before introducing another mechanism.

For the reduced fixture, write the expected sequence of jobs and publications,
including counts per function. Account for waits and reruns: what is missing,
who supplies it, and what change makes the waiting job run again? Record the
values published as well as their counts.

For example, a design might say that a solver publishes a return only after it
has the complete recursive equation. Predict how the equation becomes complete
and which publication follows. If a trace contains two earlier return
publications, the final correct type does not explain them. Find their owners
and the inputs each owner used.

Keep the prediction unchanged during the comparison. It can be wrong, but a
revision needs a written reason supported by evidence. Copying measured counts
into the expectation would remove the independent check.

## Measure, then distinguish the explanations

Run the fixture through the production boundary. Capture telemetry and the
relevant dumps, along with the revision and commands needed to reproduce them.
[Profile a Compilation](profile-a-compilation.md) explains how to trace work to
the events that caused it.

Compare the result and the sequence of work with the prediction. For every
mismatch, identify the first decision that differs. Extra work can expose a
second owner, an incomplete set of dependencies, or a job started before its
inputs are ready. Missing work can mean that a replacement was never connected
to its consumers.

When two explanations fit, design a probe that distinguishes them. Suppose a
job runs twice. One explanation is that it first waits for a missing input;
another is that an unchanged input unnecessarily wakes it. Record the inputs
available on each run and the revision that caused the wake. Those observations
separate the explanations; the count alone cannot.

Apply the same standard to a rejected idea. If a combined change fails, test
the base, each change alone, and both together. Run the failing fixture alone
and check the other configurations' logs. A failure present under both designs
cannot distinguish them. Preserve the evidence, then revert temporary probe
edits.

## Turn diagnoses into bounded repairs

Separate diagnosis from implementation. Give each reduced case a fresh reader
who establishes the paper answer and tests competing explanations. The report
states what was observed, what is inferred, and what remains unmeasured.

Combine the reports by the decision that needs repair. Several failing tests
may expose one missing distinction in the data model. That is one repair group,
with one builder and a prediction held by the person coordinating the work.
Each builder targets the group's reduced fixture; one builder does not take on
all remediation groups at once.

For example, a missing graph edge and a consumer that treats a missing answer
as “definitely absent” may require one change. Recording the edge while leaving
that interpretation intact can move the defect to the next layer. Changes that
need each other to preserve the contract belong in the same group.

The handoff brief contains:

- The reduced fixture and its paper answer.
- The base revision, reproduction commands, measurements, and separating probes.
- The decision's owner, the data carrying its answer, and its consumers.
- The predicted result and work, the mechanisms to remove, and acceptance tests.
- Any unresolved question, explicitly marked as unmeasured.

Represent the groups as `bw` tickets with dependencies. Each atomic change has
one ticket, one commit, and one close. The builder first writes a failing test
of the paper answer, then repairs the data model so that answer follows from it.

Every new fact needs a production consumer. Every new subscription needs an
account of what can wake it. For example, reading a shared fact contributed by
many callers may cause an edit to one caller to rerun work for unrelated callers.
Test that effect as well as the reduced fixture's correctness.

## Measure the deletion itself

A replacement is complete when it carries the responsibilities of the old
mechanism and the old mechanism is gone. Calling a new helper while the old
analysis still runs does not establish that the analysis can be removed.

Keep a removal ledger in the working ticket or brief. For each mechanism, record
its question, the surviving owner and consumers, the full deletion to measure,
the result, and the ticket responsible for finishing it. A row closes when the
code and stale documentation are gone.

To discover dependents, temporarily rename a definition without updating its
callers—for example, prefix its name with an underscore—and compile. The errors
identify references that need attention. Search source, tests, and agent guidance
with `rg` as well. Remove the temporary rename before committing. No remaining
references establishes that the named mechanism is gone; behavioral tests
establish that its necessary responsibilities survived.

If the full deletion makes a test fail, reduce that failure and determine which
responsibility was lost. Move it to the correct owner. Keeping the old mechanism
behind a flag leaves the two owners in place.

Preserve each test's intent. A test that only requires a deleted implementation
detail can go; a test of valid behavior needs to remain or be restated. A work
count with an obsolete name may only need renaming. Update the documentation
with the deletion so it describes the implementation a reader will actually find.

## Close the gap, then widen the checks

First reproduce the predicted answer and work on the reduced fixture. Then run
neighboring cases, the original program, and the required suite through the
relevant execution paths. Compare against the actual base revision using test
names, not just totals: fixing one test and breaking another leaves the total
unchanged. Record hangs and assertions hidden behind earlier failures separately.
An interrupted run does not establish a passing result.

If a measurement remains unexplained, preserve the trace and return to diagnosis.
Increasing a budget, adding a retry, or broadening the answer cannot explain the
mismatch. A lower work count also needs scrutiny: the intended computation may
have stopped running. Change an expected count only with a causal explanation;
a raised count requires authorization.

Completion means the result and work match the justified prediction, each
replacement has real consumers, obsolete mechanisms are removed, and required
checks pass. Remove temporary probes and scaffolding. Any authorized scaffolding
that remains needs a removal ticket. Documentation states the built behavior.

Nothing lands newly failing against a green base. Partial progress on a failing
base requires prior authorization, a strictly shorter failure list, no newly
failing tests, and every remaining failure named verbatim in the commit. Record
new defects as tickets: handle blockers first and place other discoveries at the
end of the epic. Unmeasured work remains visible until it is measured.
