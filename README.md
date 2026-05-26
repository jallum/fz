![CI](https://github.com/jallum/fz/actions/workflows/ci.yml/badge.svg)
![coverage](https://raw.githubusercontent.com/jallum/fz/badges/coverage.svg)

# **fz** - a friendly, functional language

The BEAM got something profound right: cheap processes, isolated heaps,
message-passing, pattern matching at the core, selective receive. Forty
years on, that's still the model for fault-tolerant concurrent systems,
and nobody has improved on the semantics.

The implementation strategy was shaped by what was possible in an
interpreter built in the 80s. fz keeps the semantics and asks what a
whole-program compiler with types can do with them.

What that means in practice: fz reads like Elixir, runs the actor model
you already know, and compiles — through a set-theoretic type system, a
Cranelift JIT, and an AOT path — to native code. One IR powers four
execution modes (interpreter, JIT, AOT executable, REPL), and a fixture
matrix forces them to agree.

```elixir
fn add(a, b), do: a + b

fn main() do
  print(add(2, 3))
end
```

Having full control of the stack buys some flexibility in interesting
places: When you write `receive` in fz, the receiver's pattern is
compiled into a matcher that can also on the sender's heap, and only the
values the receiver actually bound cross the process boundary. Everything
else stays on the cutting room floor. Same Elixir-shaped program, same
semantics; the machine does less work.

This README is a tour, not a spec. If you're an Elixir or Erlang person
curious about what a typed, natively-compiled cousin looks like — or a
compiler person who wants to see the internals of a language that
takes the BEAM seriously — keep reading.

---

## The bet

Three deliberate choices.

### 1. Elixir's surface, because it's pleasant

If you've written Elixir, fz will read like a slightly stripped-down
dialect. Same `fn name(args), do: body`, same `case` / `with` /
`receive`, same atoms, tuples, lists, maps, binaries, same
`defmodule`, same `@type` / `@spec`, same `defmacro` + `quote` /
`unquote`, same `|>`. We borrowed the surface syntax wholesale because
Elixir is one of the most pleasant functional languages to read
(_thank you_, José!), and there was no reason to relearn that lesson.

### 2. BEAM's concurrency model, because it works

The BEAM has spent forty years getting a handful of ideas extremely
right, and we are taking those wholesale:

- **isolated processes**, each with its own private heap, so "no
  shared mutable state" is enforced by the runtime instead of by
  convention
- **message passing** as the only way processes interact — copy on
  send, no aliasing across the boundary
- **pattern matching at the core of the language**, not bolted on the
  side — function clauses, `case`, `with`, *and* `receive` all run
  through the same matcher
- **lightweight processes by the thousand**, cooperatively scheduled
  at receive and compiler-inserted yield points, cheap to spawn and
  cheap to discard
- **selective receive**, so a process can wait for the exact message
  it cares about instead of inventing a state machine around `next()`

We are not trying to reinvent the wheel -- wheels are _great_. We
want a faster one that can ship native binaries.

The long-term goal is full interop: an fz node speaking Erlang's
external term format and distribution protocol, joining an existing
BEAM cluster as just another participant in the supervision tree. Not
"migrate to fz" — "add an fz node to the cluster." That work is
sequenced behind getting the local semantics right first.

### 3. A real compiler underneath, because that's where the win lives

Elixir compiles to BEAM bytecode. fz has its own compiler and its own
native runtime, written in Rust: an interpreter, a Cranelift-based
JIT, an AOT path that produces real executables, and a REPL — all
sharing one IR.

The compiler doesn't exist for its own sake. It exists so we can do
things the BEAM's interpreter structurally couldn't. The sender-side
matcher above is one example. **FBIP** (functional but in-place) is
another. You write obviously functional code:

```elixir
fn map([], _), do: []
fn map([h | t], f), do: [f(h) | map(t, f)]
```

A naïve runtime allocates a brand-new cons cell for every element. But
if the compiler can prove the input list is **unique** — nobody else
is holding a reference to it — it can reuse the existing cons cells in
place, writing the new head and reusing the tail pointer. Same code,
same semantics, no extra allocation. You get the readability of pure
functional code with the memory profile of a mutating loop, and the
compiler keeps you honest about when that's actually safe.

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
machine, four surface forms. The machine also destructures shared
shape exactly once — when two clauses both match `[h | t]`, as
`partition` does in the quicksort below, the cons cell gets walked one
time across both clauses, not twice. ([pattern-matching guide](guides/pattern-matching.html))

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

This one is _pretty_. Here's an ordinary-looking program — a tiny
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
to bind. The compiler also wraps the winning clause's body and its
captured bindings into a continuation — a closure ready to run. This
matcher can be used to scan the mailbox, but it can also be run on
the **sending** side.

So when `send(...)` runs:

- **If the message matches**, the matcher builds the resumption
  closure on the sender's heap with the bound values baked in. That
  closure — and *only* that closure — gets deep-copied into the
  receiver's heap. The parts of the message the receiver didn't name
  (the `:reply` tag, the matched ref, anything else) stay on the
  cutting room floor in the sender's heap and get collected normally.
  The receiver wakes up, the trampoline tail-calls the closure, and
  the clause body runs with exactly the values it asked for already
  in place — no rescan, no rebinding, no branch selection on the
  receiver side.
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

The receiver gets concierge treatment.

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

### Types do two jobs

Types catch mistakes — wrong shapes, missing clauses, the things you'd
otherwise find at runtime. They also let the compiler skip work: the
more fz can prove about a value, the more direct the code it can emit.
You get both from the same investment.

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

The type system is set-theoretic — unions, intersections, negations —
following the Castagna line that Elixir's own typer is built on. Keep
the source language small and pleasant; teach the compiler to learn as
much as it can from it.

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
fz dump fixtures/quicksort/input.fz --emit clif       # Cranelift IR
fz dump fixtures/quicksort/input.fz --emit specs      # inferred specs
fz dump fixtures/quicksort/input.fz --emit outcomes   # what happened at each call site
fz dump fixtures/quicksort/input.fz --emit stats      # compiler counters
```

These answer the questions you actually have while changing things:
*Did this call get folded? Did this function get specialized? Did
the compiler skip something — and why?* Many fixtures pin budget
numbers (function count, instruction count, planner pops, dispatches)
so that a change in compiler shape shows up loudly instead of
quietly.

---

## Trying it

Build the compiler:

```sh
cargo build --release
```

That gives you a `fz` binary at `target/release/fz` — put it on your
`PATH` (or alias it) and the rest of these commands just work.

Run a file with the JIT:

```sh
fz run fixtures/quicksort/input.fz
```

Build a native executable:

```sh
fz build fixtures/quicksort/input.fz -o /tmp/qsort
/tmp/qsort
```

Run through the interpreter:

```sh
fz interp fixtures/quicksort/input.fz
```

Start the REPL:

```sh
fz repl
```

Run the whole test suite:

```sh
cargo test --workspace
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
- set-theoretic types with `@type` and `@spec` declarations
- pattern matching (function clauses, `case`, `with`, `receive`)
- multi-clause functions and guards
- modules, imports, simple macros
- first-class functions and closures
- processes: `spawn`, `self`, `send`, `receive`, refs, selective
  receive with sender-side matching
- a working interpreter, JIT (Cranelift), AOT path, and REPL
- C externs with marshal classes and resource destructors

## Repository map

- `src/parser/`, `src/lexer.rs`, `src/ast.rs` — read source code
- `src/type_expr/`, `src/types.rs`, `src/ir_planner/` — types and
  inference
- `src/fz_ir.rs`, `src/ir_lower/`, `src/ir_reducer.rs` — build and
  simplify fz IR
- `src/ir_codegen*.rs` — Cranelift codegen for JIT and AOT
- `src/ir_interp/` — run fz IR without native codegen
- `src/runtime.fz` — the fz prelude (written in fz)
- `runtime/` — the native runtime crate
- `fixtures/` — small programs that document and test the language
- `guides/` — long-form explainers
  ([processes](guides/processes.html),
  [pattern matching](guides/pattern-matching.html),
  [memory and destination planning](guides/memory.html#destination-planning),
  [externs](guides/externs.html))

---

## Status

fz is early. The compiler, the runtime, four execution paths, the type
system, and the sender-side matcher are all working today — but the
language is small, the standard library is smaller, and the edges are
sharp. Expect to read the dumps when things surprise you.

What's next, roughly in order:

- **OTP behaviors** (`gen_server`, `supervisor`, links, monitors) —
  built in fz on top of the existing process primitives
- **Blocking-aware externs** so `libc::read` doesn't stall a scheduler
  thread
- **Distribution via ETF and disterl** — fz nodes that join existing
  BEAM clusters as ordinary participants in the supervision tree
- **An FBIP tensor type** — Nx-shape ergonomics, in-place buffer reuse,
  no `defn` ceremony, BLAS/MKL via externs
- **Autodiff** over fz IR

The current focus is keeping the four execution paths in lockstep and
teaching the compiler to turn more obvious functional code into
efficient native code. Every other goal sits on top of that one.

## A note on the name

The name is two keystrokes. The project needed to be called something.
If "fz" ends up meaning something later, it'll be because the work
earned it, not because the name promised it.
