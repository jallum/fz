# Output Contract Loop

Use this strategy for semantic compiler work where the current implementation is
complicated, partly wrong, or likely to hide the real bug behind downstream
noise.

The loop starts from the desired output contract and works backwards from one
small example until the source of the mistake is obvious.

## Goal

Produce the correct externally-visible result with a design that is:

- elegant
- data-model -> up
- correct by construction
- easy to prove with telemetry and tests

## The Loop

1. Define the output contract.

State the exact thing the system must produce at the boundary that matters:

- a projected planner spec
- a call-target set
- a return type
- a dead-arm fact
- a materialized body

Do not start from the current implementation. Start from the thing the rest of
the system should be able to trust.

2. Pick one small example.

Choose the smallest fixture or program that exercises the contract. Prefer one
that isolates a single decision:

- one call-target shape
- one pattern partition
- one closure boundary
- one return-join question

If the larger failing program is noisy, carve out the smaller shape first.

3. Work the example out on paper.

Write down:

- the relevant input facts
- the intermediate semantic decisions
- the correct output

This is the proof target. If the paper walk is not clear, the code work is not
ready yet.

4. Make the signal loud.

Add or extend telemetry so the system reports the exact facts needed to compare
the real result against the paper result.

Good telemetry answers questions like:

- which spec was projected?
- which activations covered it?
- which branches were dead?
- which call edges were selected?
- which body was materialized?

The signal should come from the production path whenever possible.

5. Pin the expectation.

Add a test that:

- runs through the production API or the real subsystem boundary
- reads the telemetry
- names the intended behavior explicitly

The test should fail because the observable contract is wrong, not because a
private helper changed shape.

6. Work backwards to the decision point.

Trace the mismatch from the bad observable result back to the first place the
system makes the wrong decision.

Ask:

- where is the wrong union formed?
- where is precision erased?
- where is reachability invented?
- where is stale state kept alive after a transform?

Do not patch the last stage that notices the bug. Find the earliest wrong fact.

7. Repair the data model.

Change the model so the incorrect state is harder or impossible to represent.

Typical moves:

- separate two concepts that were collapsed into one key
- remove a fake fallback path
- move authority to the subsystem that already computes the fact
- preserve coherence after each transform instead of relying on recomputation

The fix should make the paper result the natural outcome of the model, not a
special case.

8. Delete obsolete concepts and pins.

When the model changes, remove:

- dead paths
- stale caches
- compatibility shims
- tests that pin invalid behavior
- docs that describe the old story

A correct fix usually lets something die.

9. Re-run the same signal.

Use the exact telemetry and tests from steps 4 and 5 to prove the repaired
model produces the expected result.

Then widen out to nearby fixtures to confirm the model generalizes cleanly.

## Tiny Walkthrough

Suppose the planner emits a broad callable fallback for a named function
reference even though every closure call is statically resolved.

The loop looks like this:

1. Contract: the finished compile-time planner output contains only the
   activation-covered specs needed by the program.
2. Example: `f = &id/1; {f.(1), f.(:ok)}`.
3. On paper: two activation projections, no fallback.
4. Telemetry: inspect `fz.planner.activation_projection`.
5. Test: assert the authoritative compile path emits no `callable_fallback`.
6. Trace back: the planner invents reachability from `MakeClosure`, not from a
   real unresolved call boundary.
7. Repair: delete `MakeClosure`-driven fallback reachability and keep only real
   boundary obligations.
8. Cleanup: remove stale fallback tests and docs.
9. Verify: the named-ref fixture stays green, and neighboring closure fixtures
   still report the right activation facts.

## Heuristics

- Prefer one example at a time. A large matrix is for confirming a model, not
  discovering it.
- If the signal is muddy, improve telemetry before changing logic.
- If two passes both compute the same semantic fact, pick one authority and
  delete the duplicate.
- If a transform leaves stale state behind, the transform is incomplete.
- If a test needs internals to prove the behavior, consider whether telemetry is
  missing.

## Gates

The strategy is being followed well when:

- the output contract is written down before code changes
- the paper example and the test assert the same thing
- telemetry exposes the deciding fact directly
- the fix removes code or concepts instead of layering on compensations
- the final tests prove the production boundary behavior
