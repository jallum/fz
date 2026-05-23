![CI](https://github.com/jallum/fz/actions/workflows/ci.yml/badge.svg)
![coverage](https://raw.githubusercontent.com/jallum/fz/badges/coverage.svg)

# fz

**fz is an Elixir-flavored functional language that compiles to native
code.** You write code that looks and feels like Elixir; the compiler
turns it into a real executable, or runs it in-process via a JIT, or
walks it with an interpreter, or drops you into a REPL. All four paths
share one IR, one set of semantics, and one runtime — and a fixture
matrix forces them to agree.

```elixir
fn add(a, b), do: a + b

fn main() do
  print(add(2, 3))
end
```

fz is pre-1.0. It's a lab, not a product. But the lab is real: there
are hundreds of small fixture programs in this repo, and every one of
them is a tiny, executable promise about the language.

---

## The bet

fz is built on three deliberate choices.

### 1. Elixir's surface, because it's pleasant

If you've written Elixir, fz will read like a slightly stripped-down
dialect. Same `fn name(args), do: body`, same `case` / `with` /
`receive`, same atoms, tuples, lists, maps, binaries, same
`defmodule`, same `@type` / `@spec`, same `defmacro` + `quote` /
`unquote`, same `|>`. We borrowed the surface syntax wholesale because
Elixir is one of the most pleasant functional languages to read, and
there was no reason to relearn that lesson.

### 2. BEAM's concurrency model, because it works

The BEAM (Erlang's VM, and Elixir's host) has spent forty years
getting a handful of ideas extremely right, and we are taking those
wholesale:

- **isolated processes**, each with its own private heap, so "no
  shared mutable state" is enforced by the runtime instead of by
  convention
- **message passing** as the only way processes interact — copy on
  send, no aliasing across the boundary
- **pattern matching at the core of the language**, not bolted on the
  side — function clauses, `case`, `with`, *and* `receive` all run
  through the same matcher
- **lightweight processes by the thousand**, preemptively scheduled,
  cheap to spawn and cheap to discard
- **selective receive**, so a process can wait for the exact message
  it cares about instead of inventing a state machine around `next()`

We are not trying to reinvent the wheel. Wheels are great. We want a
faster one that can ship native binaries.

### 3. A real compiler underneath, because that's the new thing

Elixir compiles to BEAM bytecode. fz has its own compiler and its own
native runtime, written in Rust: an interpreter, a Cranelift-based
JIT, an AOT path that produces real executables, and a REPL — all
sharing one IR. That means the BEAM-shaped surface sits on top of a
compiler that's trying to learn as much as it can about your program
and turn the obvious parts into direct native code.

The most striking thing we get from this: **the sender uses the
receiver's matcher to process a message on its own heap, before
anything crosses the boundary.** We'll get to it. It's worth waiting
for.

And one more thing the compiler can do for us: **FBIP** (functional
but in-place). You write obviously functional code:

```elixir
fn map([], _), do: []
fn map([h | t], f), do: [f(h) | map(t, f)]
```

A naïve runtime allocates a brand-new cons cell for every element.
But if the compiler can prove the input list is **unique** — nobody
else is holding a reference to it — it can reuse the existing cons
cells in place, writing the new head and reusing the tail pointer.
Same code, same semantics, no extra allocation. You get the
readability of pure functional code with the memory profile of a
mutating loop, and the compiler keeps you honest about when that's
actually safe.

---

## A guided tour

### Pattern matching is how you make decisions

A function can have several clauses. fz picks the first one whose
shape matches:

```elixir
fn length([]), do: 0
fn length([_ | rest]), do: 1 + length(rest)

fn describe(0), do: :zero
fn describe(1), do: :one
fn describe(_), do: :many
```

Under the hood, every match in the language — function clauses,
`case`, `with`, even `receive` — feeds into one tiny "sorting
machine": ask yes/no questions about the shape, pluck out the pieces
that matter, hand the winning branch the values it asked for. One
machine, four surface forms. ([pattern-matching guide](guides/pattern-matching.html))

### Values are immutable

Lists, tuples, maps, binaries, atoms, integers, floats, UTF-8 strings —
all values. You don't mutate them; you make new ones:

```elixir
fn swap({a, b}), do: {b, a}

fn main() do
  print(swap({:left, :right}))   # {:right, :left}
end
```

This is the load-bearing rule that makes the concurrency story safe:
if nobody can mutate anything, nobody can race over anything.

### Concurrency: processes, not threads

A **process** is a tiny unit of execution with its own stack, its own
heap, and its own mailbox. You spin up thousands; they don't share
memory; they talk by passing messages.

Three primitives carry the entire story:

- `spawn(f)` — start a new process running `f`, return its pid
- `send(pid, msg)` — drop a message in someone's mailbox
- `receive do … end` — pattern-match a message out of your own mailbox

Smallest possible ping:

```elixir
fn child(), do: send(1, 42)

fn main() do
  spawn(child)
  print(receive do x -> x end)   # 42
end
```

A ring of processes, each adding 1 and passing the value on:

```elixir
fn relay(0, home) do
  send(home, receive() + 1)
end

fn relay(n, home) do
  next = spawn(fn() -> relay(n - 1, home))
  send(next, receive() + 1)
end

fn main() do
  home = self()
  head = spawn(fn() -> relay(4, home))
  send(head, 0)
  print(receive())   # 5
end
```

When a value is sent across processes, it is deep-copied into the
recipient's heap. There are no shared references because there are no
references — only values.

### Selective receive, sharpened

This is the showpiece. Here's an ordinary-looking program — a tiny
server that echoes back a key, and a client that asks it two questions:

```elixir
fn handle_get(ref, from, key) do
  send(from, {:reply, ref, key})
  server()
end

fn server() do
  receive do
    {:get, ref, from, key} -> handle_get(ref, from, key)
    {:stop}                -> nil
  end
end

fn main() do
  s     = spawn(server)
  ref_a = make_ref()
  ref_b = make_ref()
  me    = self()

  send(s, {:get, ref_a, me, 1})
  send(s, {:get, ref_b, me, 2})

  # Replies arrive in ref_a, ref_b order, but we want ref_b's first.
  val_b = receive do
    {:reply, ^ref_b, v} -> v
  after
    500 -> :timeout
  end

  # ref_a's reply has been sitting in the mailbox the whole time.
  val_a = receive do
    {:reply, ^ref_a, v} -> v
  end

  print(val_a + val_b)
  send(s, {:stop})
end
```

The Elixir programmer reads this and thinks: *"yes, that's selective
receive — wait for the message I actually want, leave the rest in the
mailbox for later."* The behaviour is identical to BEAM's. What's
different is how the runtime gets there.

When the receiver writes `receive do {:reply, ^ref_b, v} -> v end`,
the compiler lowers that pattern into a tiny matcher program: a
constant-time decision tree that knows exactly which shapes the
receiver will accept and which pieces of those shapes (`v`) it wants
to bind. A copy of that matcher lives on the **sending** side.

So when `send(...)` runs:

- **If the message matches**, only the **bound pieces** — the values
  the receiver actually asked to pluck out — get copied into the
  receiver's heap, ready to use. The parts of the message the
  receiver didn't name (the `:reply` tag, the matched ref, anything
  else) stay on the cutting room floor in the sender's heap and get
  collected normally. The receiver wakes up with exactly the values
  it asked for, already in its heap, no rescan and no over-copy.
- **If the message doesn't match the parked receiver**, BEAM
  semantics still apply: the message gets enqueued at the end of the
  mailbox (a later `receive` might want it), and the parked receiver
  stays parked. What we *don't* do is wake the receiver up just to
  look at a message we already know it would reject.

That's the trick: compilation lets us turn "send the whole message,
then match it on arrival" into "match first, then send only what was
asked for" — while keeping BEAM mailbox semantics intact. The
receiver told us, by writing a `receive`, exactly what it cared
about; the sender does the work on its own time and its own heap.

### First-class functions, closures, simple macros

```elixir
fn double(x), do: x * 2
fn compose(f, g, x), do: f(g(x))

defmacro inc(x) do
  quote do: unquote(x) + 1
end

fn main() do
  print(compose(double, inc, 20))   # 42
end
```

### All of it together: quicksort

```elixir
fn append([], ys), do: ys
fn append([h | t], ys), do: [h | append(t, ys)]

fn partition(_, [], lo, hi), do: {lo, hi}
fn partition(p, [h | t], lo, hi) when h < p, do: partition(p, t, [h | lo], hi)
fn partition(p, [h | t], lo, hi), do: partition(p, t, lo, [h | hi])

fn qsort([]), do: []
fn qsort([p | rest]) do
  {lo, hi} = partition(p, rest, [], [])
  append(qsort(lo), [p | qsort(hi)])
end

fn main() do
  print(qsort([3, 1, 4, 1, 5, 9, 2, 6, 5]))
end
```

Pattern matching, recursion, tuples, lists, multiple clauses — that's
the whole sort, and it's readable end to end.

### Talking to C

The OS lives in C. fz doesn't try to hide that — it declares it:

```elixir
extern "C" fn libc::creat(path :: cstring, mode :: integer) :: integer
extern "C" fn libc::write(integer, binary, integer) :: integer
extern "C" fn libc::close(integer) :: integer

fn main() do
  fd = libc::creat("/tmp/hello", 420)   # 0o644
  libc::write(fd, <<104, 105, 10>>, 3)  # "hi\n"
  libc::close(fd)
end
```

Each argument has a *marshal class* (`integer`, `binary`, `cstring`,
`any`, `nil`) telling fz how to translate between tagged fz values
and the raw 64-bit slots C expects. The `cstring` class is a small
trick: every fz binary has an invisible trailing zero byte past its
end, so handing a binary to a C function that wants a `char *` is a
pointer pass, not a copy. You can also attach a destructor to a
resource and let fz clean up after the C side when the value goes
away. ([externs guide](guides/externs.html))

The point: the standard library — file I/O, time, networking,
whatever — can be built out of fz code that calls C, instead of
waiting on the compiler team to add features one by one.

---

## Under the hood

### Types are fuel for the compiler

The type system isn't there to catch your typos. It's there to let
the compiler skip work. The more fz can prove about a value, the
more direct the code it can emit:

```elixir
fn main() do
  x = 41 + 1
  print(x)        # compiler knows x is an integer; uses the int print path
end
```

```elixir
fn kind(0), do: :zero
fn kind(n) when n > 0, do: :positive
fn kind(_), do: :other

fn main() do
  print(kind(5))   # compiler proves which clause wins, drops the rest
end
```

Keep the source language small and pleasant; teach the compiler to
learn as much as it can from it.

### The pipeline

```text
source code
  -> parse
  -> resolve names and macros
  -> lower to fz IR
  -> learn type facts
  -> simplify what can be simplified
  -> run it: interpreter, JIT, AOT, or REPL
```

One IR, four ways to run it. They must agree.

### Looking inside the compiler

The rule in this repo: **do not guess.** Make the compiler leave
breadcrumbs.

```sh
cargo run -- dump fixtures/quicksort/input.fz --emit clif       # Cranelift IR
cargo run -- dump fixtures/quicksort/input.fz --emit specs      # inferred specs
cargo run -- dump fixtures/quicksort/input.fz --emit outcomes   # what happened at each call site
cargo run -- dump fixtures/quicksort/input.fz --emit stats      # compiler counters
```

These answer the questions you actually have while changing things:
*Did this call get folded? Did this function get specialized? Did
the compiler skip something — and why?* Many fixtures pin budget
numbers (function count, instruction count, typer pops, dispatches)
so that a change in compiler shape shows up loudly instead of
quietly.

---

## Trying it

Build the compiler:

```sh
cargo build
```

Run a file with the JIT:

```sh
cargo run -- run fixtures/quicksort/input.fz
```

Build a native executable:

```sh
cargo run -- build fixtures/quicksort/input.fz -o /tmp/qsort
/tmp/qsort
```

Run through the interpreter:

```sh
cargo run -- interp fixtures/quicksort/input.fz
```

Start the REPL:

```sh
cargo run -- repl
```

Run the whole test suite:

```sh
cargo test
```

Fixture tests run small `.fz` programs and compare their output
across every execution path that applies (JIT, interpreter, AOT
executable, REPL script mode). A fixture is more than a sample file
— it is a tiny promise about the language. If quicksort works in
the JIT but not in AOT, the fixture matrix catches it.

The fixture catalog lives in [fixtures/index.md](fixtures/index.md);
compiler dump budgets are explained in
[fixtures/GOLDEN.md](fixtures/GOLDEN.md).

---

## What's in the box today

- integers, floats, atoms, booleans, `nil`, tuples, lists, maps,
  binaries, UTF-8 strings
- immutable values
- pattern matching (function clauses, `case`, `with`, `receive`)
- multi-clause functions and guards
- modules, imports, simple macros
- first-class functions and closures
- `@type` and `@spec` declarations
- processes: `spawn`, `self`, `send`, `receive`, refs, selective
  receive with sender-side matching
- a working interpreter, JIT (Cranelift), AOT path, and REPL
- C externs with marshal classes and resource destructors

## Repository map

- `src/parser/`, `src/lexer.rs`, `src/ast.rs` — read source code
- `src/type_expr/`, `src/types.rs`, `src/ir_typer.rs` — types and
  inference
- `src/fz_ir.rs`, `src/ir_lower.rs`, `src/ir_reducer.rs` — build and
  simplify fz IR
- `src/ir_codegen*.rs` — Cranelift codegen for JIT and AOT
- `src/ir_interp.rs` — run fz IR without native codegen
- `src/runtime.fz` — the fz prelude (written in fz)
- `runtime/` — the native runtime crate
- `fixtures/` — small programs that document and test the language
- `guides/` — long-form explainers
  ([processes](guides/processes.html),
  [pattern matching](guides/pattern-matching.html),
  [memory](guides/memory.html),
  [externs](guides/externs.html))

## Status

fz is pre-1.0. Expect rough edges. The current focus is on making
the semantics precise, keeping the four execution paths in lockstep,
and teaching the compiler to turn more and more obvious functional
code into efficient native code.
