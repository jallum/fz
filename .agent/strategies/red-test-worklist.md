# Red-Test Worklist

Use this strategy when a branch carries many failing (or hanging) tests at once
-- the residue of a large mid-flight refactor where genuinely good work is mixed
with broken corners. A suite that is mostly red hides new regressions: one more
failure is invisible against sixty. The worklist turns that pile into a queue
that is worked one test at a time, with the suite green the entire way.

## The rule

Every currently-failing or hanging test is disabled with a greppable marker, so
the suite is green. Green is the floor: from here, any new red is unambiguously
caused by the change in front of you. The disabled set is a worklist, not a
graveyard -- each entry is re-enabled, understood, and resolved on its own.

## Two markers

Disabled tests fall into two disjoint, separately greppable buckets:

- `#[ignore = "red-worklist: triage + re-enable"]` -- the worklist proper.
  Current-world (compiler2) tests we will re-enable one at a time and resolve.
- `#[ignore = "old-world: <subsystem>, not considered"]` -- tests of the legacy
  subsystems being retired (`ir_planner`, `ir_codegen`, `ir_interp`). These are
  NOT triaged and NOT re-enabled; they die with the old world. They are marked
  only so the suite is green and so they never get confused with the worklist.

Keep the two buckets clean: a red old-world test is `old-world`, never
`red-worklist`. The burndown count is `red-worklist` markers only.

## Establishing the floor

1. Enumerate every red. A SIGABRT or an infinite loop kills the stock test
   binary mid-suite, so a single run under-counts. Run, disable what it names,
   re-run, repeat until the suite completes and reports `0 failed`. Hanging
   tests count: `#[ignore]` skips them, so they stop blocking the run.

2. Disable each with `#[ignore = "<id>: <one-line why>"]` placed between
   `#[test]` and `fn`. The `<id>` is greppable (the owning ticket, or the
   worklist tag) so the queue can be listed at any time:

   ```
   rg '#\[ignore = "' src | rg '<id>'
   ```

3. Confirm the suite is green. Do not proceed with a red floor.

## The loop (one test at a time)

1. Pick one disabled test. Remove its `#[ignore]`. Run only it.

2. Read the failure AND the test. Recover the test's *intent* -- the behavior it
   was written to protect -- separately from its *mechanism* -- the fixtures it
   builds and the assertions it makes. These can disagree.

3. Decide which is wrong, with skepticism toward the test:
   - **The code is wrong** -> a real regression or unbuilt behavior. Fix the
     code. The test was right to fail.
   - **The test is wrong** -> it enshrines an outdated or never-correct model
     (a layout that should have changed, a shape that recorded a bug as
     expected output). Preserve the intent; correct the assertion to the
     current data model. Never weaken an assertion just to pass -- re-aim it at
     the right fact. A test whose intent is itself obsolete is deleted, not
     neutered.
   - **Out of scope** -> the failure is real but belongs to other work. File a
     ticket, re-disable referencing that ticket, move on. This is the only
     sanctioned way a test stays disabled.

4. Make it green by fixing code or re-aiming the test -- never by disabling it
   again to dodge the work (except the out-of-scope case above, which is a
   ticket, not a dodge).

5. Keep everything else green. One re-enabled test is one coherent commit (or a
   small batch of a single root cause closed together), titled for the test or
   the fix.

6. Next.

## Gates

The strategy is being followed well when:

- the suite reports `0 failed` before and after every step
- a re-enabled test's intent is stated before its mechanism is touched
- assertions are corrected toward the model, never softened toward passing
- the only tests left disabled carry a ticket id explaining why
- the worklist shrinks monotonically; `rg` on the marker shows the burndown
