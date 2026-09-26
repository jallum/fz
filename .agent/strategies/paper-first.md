# Paper First

**Use when** a problem is too noisy to reason about directly: a wrong result,
more work than the input warrants, or many symptoms at once.

A large failing system shows the effects of every fault at once. A small
example shows one fault, and it is small enough to answer by hand. Answer it
yourself, watch the system answer it, and the first place the two differ is
the fault.

## The loop

1. **Shrink.** Cut the problem down until one question is left that you can
   answer by hand. After each cut, check that the symptom is still there; if
   it is gone, the cut removed the cause, which is worth knowing too. Keep
   the original problem, and note how it behaves now.

2. **Answer it from first principles.** Without reading the implementation,
   work out what the correct result is and what it should take to produce
   it. Write both down. If you cannot, you do not understand the question
   yet: shrink further.

3. **Watch the system answer it.** Run the small case and make it show its
   steps, not just its result. If it cannot show the step you need, add the
   observation before changing anything else.

4. **Find the first difference.** Compare the steps with your answer. The
   first place they part is the fault; everything after it is consequence.
   If more than one explanation fits, run a probe that tells them apart. If
   your answer turns out to be wrong, correct it with the evidence, never to
   match the run.

5. **Fix where the difference starts.** Change the thing that made the first
   wrong decision, so the correct answer follows from it. Anything the fix
   makes unnecessary goes in the same change. Pin the small case as a test
   that failed before the fix and passes after.

6. **Return to the original.** Run it again. One source of noise should be
   gone. If noise remains, it is the next problem: go back to step 1.

## Principles

- One question at a time. Noise is many answers mixed together.
- Answer before you look. An answer derived after reading the code tends to
  describe the code.
- The first difference, not the last symptom. Fixing where a fault is
  noticed leaves it in place.
- A correct result can hide wasted work, and a small amount of work can hide
  work that never ran. Check both.
- A wider answer, a larger limit, a retry or an updated expectation is not
  an explanation.

## Example

`fixtures2/behavior/json_roundtrip.fz` is a small program the compiler spends
thousands of steps on, about half of them repeats. Shrunk to one recursive
function,

```
def build(0), do: :start
def build(n), do: {n, build(n - 1)}
```

the question is `build/1`'s return type. By hand it is
`R = :start | {integer, R}`, found in one step. The compiler revises it
seventeen times and then gives up and widens it (`RETURN_LADDERS` in
`drive_test.rs`). The first difference is that it climbs toward a recursive
type one level at a time instead of solving it. Fixing that removes one
source of the larger program's noise; what remains is the next question.
