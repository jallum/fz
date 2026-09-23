# Predict, Measure, Collapse

Use this strategy when the compiler produces an incorrect answer, performs
unexplained work, or has several mechanisms answering the same question.

The loop extends the [Output Contract Loop](output-contract-loop.md): solve a
small example, predict the work needed to produce its answer, then measure both.
Collapse the competing mechanisms into one owner for each decision.

## Goal and signal

Produce the correct answer with every step of work accounted for.

The signal includes:

- which activations exist, what keys distinguish them, and what each returns
- which jobs run, in what order, and how often per function
- which facts change, what values they publish, and which jobs they wake

A correct final type can hide repeated intermediate answers. A low job count can
hide work that never ran. Check the answer and the work together.

## The Loop

1. Reduce the failure.

Cut the program down until it can be solved by hand. Preserve the decision that
fails; remove unrelated computation. Keep the original program for checking
that the eventual repair works in context.

2. Solve it on paper.

Write the equations and their solution beside the fixture. State which
activations exist, their keys, and their returns. This is the specification.

If the intended model cannot represent the answer, record that limit. Broadening
the answer to make the computation stop does not meet the specification.

3. Predict the succession.

Before building, write the expected jobs and publications in order, with counts
per function. Work backwards from the answer through its prerequisites.

For each decision, name:

- the component that owns it
- the facts it needs and who supplies them
- the consumers of its answer
- any wait or rerun, and the change that causes it

Examine existing authorities and analogous code before introducing a new one.
Keep the prediction fixed during the comparison. If it proves wrong, revise it
with a written explanation supported by evidence.

4. Measure the fixture.

Run through the production boundary with telemetry and the relevant dumps.
Record the revision, commands, and results. Use
[Profile a Compilation](profile-a-compilation.md) to trace work to its cause.

Compare the answer and each step of work with the prediction. Include published
values: a count of two return definitions does not say whether they agreed.

5. Explain every divergence.

Find the first decision that differs. Check for a second owner, missing
dependencies, an unused replacement, or work begun before its inputs are ready.

When two explanations fit, run a probe that separates them. A job running twice
might have waited for a missing input, or been woken by an unchanged one. Record
the inputs on each run and the revision that caused the wake; the count alone
cannot distinguish these causes.

Apply the same test to a refutation. Split combined edits, run the failure alone,
and compare the base, each edit alone, and both together. Check the other
configurations' logs before blaming a design. Preserve the evidence and revert
the temporary probes.

6. Group the repairs, then build.

Keep diagnosis separate from implementation. Give each reduced case a fresh
reader who establishes the paper answer and tests competing explanations. The
report separates observations, inferences, and unmeasured claims.

Combine reports that point to the same decision into one repair group. For
example, adding a missing graph edge may also require changing a consumer that
reads missing evidence as “definitely absent.” If those changes need each other
to preserve the contract, they are one group.

Give each group one builder and its reduced fixture as the target. The
coordinator holds the prediction. The brief includes:

- the fixture and paper answer
- the base revision, reproduction commands, and probe results
- the surviving owner, the data carrying its answer, and its consumers
- the predicted work, removals, acceptance tests, and unresolved questions

Use `bw` tickets in dependency order: one atomic change, one commit, one close.
The builder first writes a failing test of the paper answer, then repairs the
data model so the answer follows from it.

7. Measure the full deletion.

Remove the mechanism the design replaces and run the fixture. Swapping one leaf
while the old analysis keeps running does not prove that analysis is redundant.

Keep a removal ledger in the ticket or brief. Each row names the mechanism, its
question, the surviving owner and consumers, the measured deletion result, and
the ticket responsible for finishing it.

To find dependents, temporarily rename a definition without updating callers
—for example, prefix it with an underscore—and compile. The errors form a
worklist. Search source, tests, and agent guidance with `rg` as well. Remove the
rename probe before committing.

A failing deletion exposes a responsibility to investigate and place with the
correct owner. Keeping the old path behind a flag leaves the repair unfinished.
Close the ledger row when the code and stale documentation are gone and tests
prove the necessary behavior survived.

8. Widen the checks.

After the reduced fixture matches, run neighboring cases, the original program,
and the required suite across relevant execution paths. Compare exact failing
test names against the actual base revision. Fixing one test and breaking another
leaves the total unchanged.

Record hangs and checks hidden behind earlier assertions separately. An
interrupted run is incomplete evidence. Test effects on unrelated work too: a
shared fact with many publishers can wake readers when an unrelated caller edits.

## Tiny Walkthrough

Suppose a function returns an integer or a list containing its recursive result.

1. Paper answer: `R = int | [R]`, written finitely as `μX. int | [X]`. The `X`
   refers back to the same type.
2. Prediction: for a design where one solver owns the complete equation, write
   how its inputs become ready and which return publication follows.
3. Measurement: the final type agrees, but the trace also publishes `int` and
   then `int | [int]` before reaching it.
4. Probe: record who published each answer and which inputs it used. Determine
   whether another publisher remains or the solver saw an incomplete equation.
5. Repair: establish the intended owner and its prerequisites; measure with the
   displaced mechanism deleted.
6. Test: assert the recursive answer and the justified work counts together.

## Heuristics

- Every derived fact names a production consumer. A fact nobody reads has not
  replaced the mechanism still doing the work.
- A failed implementation does not by itself disprove its design. Isolate the
  failure before rejecting the idea.
- Preserve test intent. Delete tests of obsolete behavior; restate valid tests
  around the surviving model. An obsolete name may only need renaming.
- An unexpectedly lower count needs explanation too. The intended work may have
  stopped running.
- If the trace cannot explain a mismatch, preserve it and return to diagnosis.
  A wider answer, larger budget, retry, or changed golden cannot explain it.

## Gates

The strategy is being followed well when:

- the paper answer and work prediction precede implementation
- every mismatch has a measured cause or a documented correction to the prediction
- replacements have production consumers and displaced mechanisms are absent
- tests prove both the result and the work through the production boundary
- required checks pass and documentation describes the built behavior
- temporary probes are removed; authorized retained scaffolding has removal tickets

Nothing lands newly failing against a green base. Partial progress on a failing
base requires prior authorization, a strictly shorter failure list, no newly
failing tests, and every remaining failure named verbatim in the commit. A raised
work pin requires a causal explanation and authorization; changing the expected
count to match a run is not evidence.

New defects get tickets: blockers first, other discoveries at the end of the
epic. Unmeasured claims remain explicitly unmeasured.
