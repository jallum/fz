# Ownership Shape

Use this strategy when a copy exists only so the code compiles: a `.clone()`,
a `.to_vec()`, a `collect`, a placeholder value or a hand-placed `drop` whose
one job is to get a value past the borrow checker.

## What appeasement is

The borrow checker rejects code that reads a value while something else may
write it. There are two ways to answer. One is to change who owns what, so the
read and the write no longer overlap. The other is to make a copy, so the
checker has nothing left to compare. The second is borrow-checker appeasement.

The copy compiles, costs an allocation, and leaves the ownership question
unanswered. The next reader of the code pays for it twice: once at run time,
and once working out whether the copy means anything.

The test is simple. A copy is appeasement when deleting it would change nothing
except whether the program compiles.

## How it looks

Each example shows the appeasing form, why the checker forced it, and the
shape that makes the copy unnecessary.

### A clone to walk your own input

```rust
struct Lowerer { input: Vec<Item>, out: Vec<Out> }

for item in self.input.clone() {   // copies every item
    self.visit(&item);             // visit takes &mut self
}
```

`visit` borrows all of `self`, and `input` is part of `self`. The input is not
state the walk changes, so it does not belong beside the state:

```rust
struct Lowerer<'a> { input: &'a [Item], out: Vec<Out> }

let input = self.input;            // copies the reference, not the items
for item in input {
    self.visit(item);
}
```

### An owned return from a reader

```rust
fn name(&self, id: Id) -> String { self.names[&id].clone() }

if world.name(id).is_empty() { .. }   // a String allocated to answer yes or no
```

The accessor copies because some caller, somewhere, needed to keep the value.
Every other caller pays for that one:

```rust
fn name(&self, id: Id) -> &str { &self.names[&id] }

let kept = world.name(id).to_owned(); // the caller that keeps it says so
```

### A collect to release a borrow

```rust
let ids: Vec<Id> = self.ready.iter().copied().collect();
for id in ids {
    self.done.insert(id);
}
```

`ready` and `done` are different fields, and the checker tracks fields
separately:

```rust
for id in &self.ready {
    self.done.insert(*id);
}
```

This stops compiling the moment the loop body calls a `&mut self` method. That
is the signal to split the struct, as in the first example, and the collect
was hiding it.

### A placeholder swapped into a cell

```rust
let thing = mem::replace(&mut *cell.borrow_mut(), Thing::new());
let (thing, result) = work(thing);
*cell.borrow_mut() = thing;        // the Thing::new() above was never used
```

A whole value is built so the cell is never empty. Lend the value in place, or
let the cell say that it can be empty:

```rust
let result = work(&mut cell.borrow_mut());
```

### A drop placed by hand

```rust
let mut log = self.log.borrow_mut();
log.push(line);
drop(log);
self.flush();                      // flush borrows the log again
```

The guard lives longer than its use. Give the borrow the scope of the one
statement that needs it:

```rust
self.log.borrow_mut().push(line);
self.flush();
```

## What is not appeasement

A copy that transfers or shares ownership on purpose is doing real work:

- a key or a value cloned into a map, a set or a fact that stores it
- `Rc::clone` of data that is immutable and shared
- a scope that forks: `let mut inner = env.clone()` where the two then diverge
- `mem::take` that drains a buffer being handed to its next owner

Each of these can say who keeps the copy. An appeasing copy cannot.

## The loop

1. Change the signature, not the call sites. Return a borrow, hold a
   reference, take a slice. `cargo check` then lists every dependent.

2. Sort the errors into two piles. Callers that compile after a trivial edit
   were pure appeasement. Callers that fail to borrow interleave a read with a
   write; these are the real knots.

3. Resolve each knot by the first move that works:
   - **Compute, then commit.** Finish the reads, then do the writes.
   - **Split the borrow.** Take the field instead of the whole, or separate
     the immutable input from the mutable working state.
   - **Share by handle.** An `Rc`, only for data that is immutable after
     construction and must outlive the borrow. This keeps the copy and makes
     it cheap, so it comes last.

4. Stop when sharing by handle is the only move left for most callers. The
   knot is then the owner itself, and that is a design proposal, not a
   cleanup.

5. Delete every copy the change made unnecessary, with any comment that
   explained it.

## Gates

The strategy is being followed well when:

- behaviour is unchanged: no golden, census number or pinned count moves
- every copy that remains can name who keeps it
- no comment exists to justify a copy; a copy that needs explaining is a shape
  that needs fixing
- a caller that needs ownership clones at its own call site, where review
  sees it
