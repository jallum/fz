# Red-Test Worklist

Use this strategy when a branch carries many failing tests at once -- the
residue of a large mid-flight change where good work is mixed with broken
corners. A mostly-red suite hides new regressions: one more failure is
invisible against sixty. The worklist turns the pile into a queue that is
worked one test at a time.

## The rule

No test is disabled for being red. A red test runs, fails, and says so. The
record of what is red is the list a gate run produces, and each run's list is
compared against the previous run's.

Green is not the floor; the previous run's list is. A change is judged against
it, not against zero.

## The two lists

A gate run produces one list per suite:

- `lib_failed` -- the failing tests of `cargo test --lib -- --test-threads=1`.
- `matrix_failed` -- the failing fixtures of
  `cargo test --test fixture_matrix -- --test-threads=1`.

Both suites run single-threaded, because a parallel fixture matrix is
nondeterministic and a shared-thread panic can cut a run short.

Compare each list against the same list from the previous run:

- **Newly red** -- present now, absent before. Reported verbatim: the test's
  name and the exact assertion that failed. Never paraphrased, never
  summarized to a count.
- **Fixed in the candidate** -- present before, absent now. This is the
  burndown.

The bar for landing is that the red list is strictly shorter and nothing is
newly red. When something is newly red anyway, the remainder is stated
verbatim so the next run inherits a true list.

## The one allowed `#[ignore]`

A test is ignored only when it cannot run in the gate at all -- it hangs, or it
needs something the gate does not provide. Its label leads with what running it
needs, then the reason. A fixture says the same thing in its `defer:` header.

`fixtures2/behavior/value_call_guarded.fz` is the example. Its `defer:` header
opens with `running this fixture needs a compile timeout:` and then gives the
cause -- the compile does not terminate, and why.

The label is a requirement, not an excuse. A reader who supplies the named
thing can run the test. "Broken", "flaky", "triage later" and a ticket id are
none of them a requirement, so none of them is a label.

## The loop (one test at a time)

1. Pick one entry from the red list. Run only it.

2. Read the failure AND the test. Recover the test's *intent* -- the behavior
   it was written to protect -- separately from its *mechanism* -- the fixtures
   it builds and the assertions it makes. These can disagree.

3. Decide which is wrong, with skepticism toward the test:
   - **The code is wrong** -> a real regression or unbuilt behavior. Fix the
     code. The test was right to fail.
   - **The test is wrong** -> it enshrines an outdated or never-correct model
     (a layout that should have changed, a shape that recorded a bug as
     expected output). Preserve the intent; correct the assertion to the
     current data model. Never weaken an assertion just to pass -- re-aim it at
     the right fact. A test whose intent is itself obsolete is deleted, not
     neutered.
   - **Out of scope** -> the failure is real but belongs to other work. It
     stays red and stays on the list.

4. Make it green by fixing code or re-aiming the test. Disabling it is not one
   of the options.

5. Keep the rest of the list from growing. One resolved test is one coherent
   commit (or a small batch closed by a single root cause), titled for the fix.

6. Next.

## Gates

The strategy is being followed well when:

- every run's two lists are captured, and each is compared against the previous
  run's before anything is judged
- newly red entries are quoted with their failing assertion, not counted
- a worked test's intent is stated before its mechanism is touched
- assertions are corrected toward the model, never softened toward passing
- the red list shrinks monotonically across the branch
- every `#[ignore]` and `defer:` in the tree names a thing that running it
  needs
