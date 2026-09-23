# Predict, Measure, Collapse

Use this strategy when a repair must explain both the answer and the work needed
to produce it, especially when several mechanisms answer the same question.
It extends the [Output Contract Loop](output-contract-loop.md) with a held work
prediction, independent diagnosis, and measured removal of duplicate authority.

## Goal and signal

The goal is one authoritative answer per semantic question, carried by a data
model that makes the correct result natural. Every derived fact names its
production consumer; deriving a replacement fact without moving its readers
leaves the old mechanism in charge.

The signal has two parts: the exact result and the exact work that produced it.
For a small compiler fixture, record the activations, their keys and returns,
the ordered jobs and publications, and counts per function. A correct final
type with unexplained intermediate definitions or reruns is not a completed
repair. Counts alone can also hide a wrong answer: record the values published.

## The loop

1. **Reduce.** Cut the failing program down until it can be solved by hand.
   Preserve the decision that fails. Use larger programs to check composition
   after the reduced case is understood.
2. **Solve on paper.** Write the equations, identities, and intended result next
   to the fixture. State the supported domain. If the answer cannot be expressed
   by the intended model, record that limit explicitly; a fallback that erases
   the distinction does not solve it.
3. **Predict the succession.** Before implementation, write which jobs run,
   which facts they read and publish, their order, and counts by subject. Name
   the owner of each answer and the consumers that use it. Include prerequisite
   waits, revisions, and wakes where they affect the work. Keep this prediction
   fixed while comparing it with the measurement.
4. **Measure.** Run the fixture through the production boundary with telemetry
   and the relevant dumps. Use [Profile a Compilation](profile-a-compilation.md)
   for capture and causal analysis. Record the exact revision, commands, and
   results so another reader can reproduce the comparison.
5. **Explain every divergence.** Trace each extra or missing event to its cause.
   Check for a second authority, an unconnected replacement, an incomplete
   dependency graph, or work started before its prerequisites. Correct either
   the implementation or the prediction, with the evidence and explanation
   written down. Re-blessing a golden, changing a pin, or adding a termination
   budget is not an explanation.
6. **Verify before asserting.** When two explanations fit, run the smallest
   probe that gives different outcomes under them. Preserve its evidence and
   revert the diagnostic edits. A plausible source location is a hypothesis
   until the failing path is observed there.

A refutation needs the same discipline as a proposed cure. Split combined edits,
run the failure alone, compare with the base, and check the logs of configurations
the explanation did not blame. A failed implementation does not by itself
disprove its design. For two interacting changes, measure the base, each change
alone, and both together before attributing the result.

## Separate diagnosis from building

Give each reduced case a fresh reader whose job is to establish the paper
answer and run separating probes, not to deliver a repair. Each report separates
observations, hypotheses, and unmeasured claims. Probe edits are reverted before
handoff; retained tests express the contract through the production boundary.

Combine the reports into one brief. Group symptoms by the semantic question and
authority they share, rather than assigning a repair to each failing assertion.
This is the fold: several apparent problems become one change to the model.
Examine existing authorities and analogous code before proposing another
subsystem. If an edge and its consumer's interpretation must change together,
they belong to one atomic group.

Each group gets a held prediction and one builder, with its reduced fixture as
the target. Do not give every remediation to one builder at once. Plan groups as
`bw` tickets in dependency order, with one ticket, commit, and close per atomic
change. A brief contains:

- The contract, reduced fixture, and paper answer.
- The base revision, reproducing commands, measured trace, and separating probes.
- The surviving authority, its fact carrier, and every production consumer.
- The predicted result and work, including effects on unrelated edits or roots.
- The mechanisms to remove, acceptance tests, and unresolved questions.

The builder first pins the paper answer with a failing test, then repairs the
model from the data upward. A new fact or subscription has a cost: explain what
publishes it, who reads it, and which changes wake those readers. Local fixture
correctness does not establish that unrelated work remains untouched.

## Prove the removal

Keep a removal ledger in the working ticket or brief:

| Mechanism | Question it answers | Surviving authority and consumers | Measured removal evidence | Owning ticket |
| --- | --- | --- | --- | --- |

Measure the full deletion named in each row. Swapping a leaf while its mechanism
continues running is not evidence that the mechanism is redundant. If deletion
exposes a missing responsibility, reduce that failure and move the responsibility
to its proper owner. Keeping the duplicate behind a gate postpones the repair.

As a temporary probe, rename a definition with a leading underscore without
updating its callers, then compile to enumerate dependents. Compiler errors form
a deletion worklist. Also search source, tests, and agent guidance with `rg` for
the removed symbols and concepts. Zero references and passing behavioral tests
are complementary evidence: spelling alone does not prove an authority is gone.
Remove the rename probe before committing.

Remove stale tests and goldens that only preserve a dead mechanism, while
retaining or restating tests of valid behavior. A valid work pin with an obsolete
name needs renaming, not deletion. Update guidance in the same change so the next
reader cannot mistake a leftover for a supported tool. Close a ledger row only
when the implementation and its stale documentation are gone.

## Acceptance and stop conditions

Run the reduced fixture first, then neighboring cases, the original composite,
and the required suite across the relevant execution paths. Compare the exact
failing-test names against the actual base revision; totals can hide a newly
broken test behind an unrelated fix. Distinguish failures, hangs, and checks
masked by an earlier assertion. An interrupted run is incomplete evidence.

The repair is complete when the paper result and work prediction match, every
replacement has a production consumer, the superseded mechanisms are absent,
and the required checks pass. Documentation describes the built behavior in the
present tense. Remove temporary probes and scaffolding; any authorized retained
scaffolding has a removal ticket.

If a fixture misses its paper answer for an unexplained reason, stop building,
preserve the exact succession, and return to diagnosis. Do not widen the answer,
raise a cap, add a retry, or silently reinterpret missing evidence as a settled
answer. An unexpectedly lower count also needs explanation: it may mean the
intended work stopped running.

Nothing lands newly red against a green base. Partial progress on a failing base
requires prior authorization, a strictly shorter red list, no newly failing
tests, and every remaining failure named verbatim in the commit. Do not change
work pins merely to fit a measurement; explain the causal difference and obtain
authorization for a raised pin. New defects get tickets: blockers first, others
at the end of the epic. Unmeasured claims remain explicitly unmeasured.

## Tiny example

Suppose a recursive value satisfies `R = int | [R]`. The paper answer is the
finite description `μX. int | [X]`. A succession of `int`, `int | [int]`, and
`int | [int | [int]]` is not that answer.

For a design whose solver owns the complete equation, predict its publication
and the work required to supply every dependency. If the final dump is correct
but the trace contains repeated approximations, inspect who publishes each one.
If two explanations remain—duplicate ownership or an incomplete equation—probe
the owners and inputs before choosing a cure. Delete the displaced publisher in
the measurement itself, then assert both the result and the justified work.
