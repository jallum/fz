![CI](https://github.com/jallum/fz/actions/workflows/ci.yml/badge.svg)
![coverage](https://raw.githubusercontent.com/jallum/fz/badges/coverage.svg)

# **fz** - a friendly, functional language

The BEAM got some things profoundly right: cheap processes, isolated heaps,
message-passing, pattern matching at the core, selective receive. Forty
years on, that's still the model for fault-tolerant concurrent systems,
and nobody has improved on the semantics.

The implementation strategy was shaped by what was possible in an
interpreter built in the 80s. fz keeps the semantics and asks what a
whole-program compiler with types can do with them.

What that means in practice: fz reads like Elixir, runs the actor model
you already know, and compiles — through a set-theoretic type system, a
Cranelift JIT, and an AOT path — to native code. One IR powers three
execution modes (AOT executable, JIT, interpreter) — and soon a REPL —
and a fixture matrix forces them to agree: the small programs in
`fixtures/` run on every path that applies, and their output is checked.

```elixir
def add(a, b), do: a + b

def main() do
  dbg(add(2, 3))
end
```

To run it, build the compiler, save the sample as `add.fz`, and run it:

```sh
cargo build --release
target/release/fz2 run add.fz   # prints 5
```

`fz2` is fz's compiler and runner; the name comes from fz's second
compiler, which replaced the first. *Trying it*, below, covers the other
ways to run a program.

A file can also be a script: its top-level expressions run in order as the
program's `main/0` (a file with both top-level expressions and its own
`def main()` is an error).

Having full control of the stack buys some flexibility in interesting
places: When you write `receive` in fz, the receiver's pattern is
compiled into a matcher that can also run on the sender's heap, and only
the values the receiver actually bound cross the process boundary.
Everything else stays on the cutting room floor. Same Elixir-shaped
program, same semantics; the machine does less work.

The same control buys another trick we think you'll like: the compiler
builds values directly into their final position and reuses list cells
it can prove are private — so textbook functional code runs with the
allocation profile of a hand-tuned loop, and you never write a single
borrow annotation to get it.

If you're an Elixir or Erlang person curious about what a typed,
natively-compiled cousin looks like — or a compiler person who wants to
see the internals of a language that takes the BEAM seriously — keep reading.

---

## The bet

Three deliberate choices.

### 1. Elixir's surface, because it's pleasant (_thank you_, José!)

If you've written Elixir, fz will read like a slightly stripped-down
dialect in some ways, more fleshed out in others. Same 
`def name(args), do: body`, same `case` / `with` /
`receive`, same atoms, tuples, lists, maps, binaries, same
`defmodule`, same `@type` / `@spec`, same `defmacro` + `quote` /
`unquote`, same `|>`. We borrowed the surface syntax wholesale because
Elixir is one of the most pleasant functional languages to read, and 
there was no reason to relearn that lesson.

### 2. BEAM's concurrency model, because it works

The BEAM has spent forty years getting a handful of ideas extremely
right, and we are taking those wholesale:

- **isolated processes**, each with its own private heap, so "no
  shared mutable state" is enforced by the runtime instead of by
  convention
- **message passing** as the only way processes interact — copy on
  send, no mutable aliasing across the boundary (binaries over 64 bytes
  are shared immutably by refcount, as on the BEAM)
- **pattern matching at the core of the language**, not bolted on the
  side — function clauses, `case`, `with`, *and* `receive` all run
  through the same matcher
- **lightweight processes by the thousand**, cooperatively scheduled
  at receive and, in compiled code, at compiler-inserted yield points
  on loop back edges, cheap to spawn and
  cheap to discard
- **selective receive**, so a process can wait for the exact message
  it cares about instead of inventing a state machine around `next()`

We are not trying to reinvent the wheel — wheels are _great_. We
want a faster one that can ship native binaries.

The long-term goal is full interop: an fz node speaking Erlang's
external term format and distribution protocol, joining an existing
BEAM cluster as just another participant in the supervision tree. Not
"migrate to fz" — "add an fz node to the cluster." That work is
sequenced behind getting the local semantics right first.

### 3. A real compiler underneath, because that's where the win lives

Elixir compiles to BEAM bytecode. fz has its own compiler and its own
native runtime, written in Rust: an interpreter, a Cranelift-based
JIT, and an AOT path that produces real executables — all sharing one
IR.

Owning the whole stack, from source to machine code, is what pays for
the two tricks teased at the top. The tour shows each one in full (*Selective
receive, sharpened* and *All of it together: quicksort*); both keep BEAM
semantics exactly.

---

## A guided tour

### Pattern matching is how you make decisions

A function can have several clauses. fz picks the first one whose
shape matches:

```elixir
def length([]), do: 0
def length([_ | rest]), do: 1 + length(rest)

def describe(0), do: :zero
def describe(1), do: :one
def describe(_), do: :many

def main() do
  dbg(length([:a, :b, :c]))   # 3
  dbg(describe(1))            # :one
end
```

Under the hood, every match in the language — function clauses,
`case`, `with`, even `receive` — feeds into one tiny "sorting
machine": ask yes/no questions about the shape, pluck out the pieces
that matter, hand the winning branch the values it asked for. One
machine, four surface forms. The machine also tests shared shape
once — when adjacent clauses both match `[h | t]`, as `partition` does
in the quicksort below, the cons test is asked one time across both
clauses, not twice. ([pattern-matching guide](guides/pattern-matching.html))

### Values are immutable

Lists, tuples, maps, binaries, atoms, integers, floats, UTF-8 strings —
all values. You don't mutate them; you make new ones:

```elixir
def swap({a, b}), do: {b, a}

def main() do
  dbg(swap({:left, :right}))   # {:right, :left}
end
```

This is the load-bearing rule that makes the concurrency story safe:
if nobody can mutate anything, nobody can race over anything.

### First-class functions, closures, simple macros

Functions are values: pass them around, return them, capture their
environment in a closure. Macros run at compile time, rewriting code
before it is lowered.

```elixir
def double(x), do: x * 2
def compose(f, g, x), do: f.(g.(x))

defmacro inc(x) do
  quote do: unquote(x) + 1
end

def add1(x), do: inc(x)

def main() do
  dbg(compose(double, add1, 20))   # 42
end
```

Those closures are what the concurrency examples below spawn — when you
write `spawn(fn() -> relay(n, home) end)`, that anonymous function is a
first-class value handed to a brand-new process.

### Concurrency: processes, not threads

A **process** is a tiny unit of execution with its own heap (which also
holds its pending calls) and its own mailbox. You spin up thousands; they don't share
memory; they talk by passing messages.

Three primitives carry the entire story:

- `spawn(f)` — start a new process running `f`, return its pid
- `send(pid, msg)` — drop a message in someone's mailbox
- `receive do … end` — pattern-match a message out of your own mailbox

Smallest possible ping:

```elixir
def child(parent), do: send(parent, 42)

def main() do
  me = self()
  spawn(fn() -> child(me) end)
  dbg(receive do x -> x end)   # 42
end
```

A ring of processes, each adding 1 and passing the value on:

```elixir
def relay(0, home) do
  value = receive do x -> x end
  send(home, value + 1)
end

def relay(n, home) do
  next = spawn(fn() -> relay(n - 1, home) end)
  value = receive do x -> x end
  send(next, value + 1)
end

def main() do
  home = self()
  head = spawn(fn() -> relay(4, home) end)
  send(head, 0)
  got = receive do x -> x end
  dbg(got)   # 5
end
```

### Selective receive, sharpened

This one is _pretty_. Here's an ordinary-looking program — a tiny
server that echoes back a key, and a client that asks it two questions:

```elixir
def handle_get(ref, from, key) do
  send(from, {:reply, ref, key})
  server()
end

def server() do
  receive do
    {:get, ref, from, key} -> handle_get(ref, from, key)
    {:stop}                -> nil
  end
end

def main() do
  s     = spawn(&server/0)
  ref_a = make_ref()
  ref_b = make_ref()
  me    = self()

  send(s, {:get, ref_a, me, 1})
  send(s, {:get, ref_b, me, 2})

  # Replies arrive in ref_a, ref_b order, but we want ref_b's first.
  val_b = receive do
    {:reply, ^ref_b, v} -> v
  end

  # ref_a's reply has been sitting in the mailbox the whole time.
  val_a = receive do
    {:reply, ^ref_a, v} -> v
  end

  dbg(val_a + val_b)
  send(s, {:stop})
end
```

The Elixir programmer reads this and thinks: *"yes, that's selective
receive — wait for the message I actually want, leave the rest in the
mailbox for later."* The behaviour is identical to BEAM's. What's
different is how the runtime gets there.

When the receiver writes `receive do {:reply, ^ref_b, v} -> v end`,
the compiler lowers that pattern into a tiny matcher program: a
decision tree that knows exactly which shapes the
receiver will accept and which pieces of those shapes (`v`) it wants
to bind. The compiler also wraps the winning clause's body and its
captured bindings into a continuation — a closure ready to run. This
matcher can be used to scan the mailbox, but it can also be run on
the **sending** side.

So when `send(...)` runs:

- **If the message matches**, the sender copies *only the parts of the
  message holding the values the pattern bound* into one fresh block of its own memory and queues that
  block for the receiver. The parts of the message the receiver didn't
  name (the `:reply` tag, the matched ref, anything else) stay in the
  sender's heap and get collected normally. The receiver wakes up,
  adopts the segment, builds the resumption closure over the values it
  asked for, and the clause body runs — no rescan, no rebinding, no
  branch selection on the receiver side. A pattern that binds nothing
  copies nothing.
- **If the message doesn't match the parked receiver**, BEAM
  semantics still apply: the message gets enqueued at the end of the
  mailbox (a later `receive` might want it), and the parked receiver
  stays parked. What we *don't* do is wake the receiver up just to
  look at a message we already know it would reject. The sender copies
  the whole message once, into one block the receiver adopts the next
  time it runs.

That's the trick: compilation lets us turn "send the whole message,
then match it on arrival" into "match first, then send only what was
asked for" — while keeping BEAM mailbox semantics intact. The
receiver told us, by writing a `receive`, exactly what it cared
about; the sender does the work on its own time and its own heap.

You can watch it happen. Every send to another process logs one
`fz.runtime.send.probe` event: its `outcome` says whether the message
matched the receive the other process is parked on, and `gift_bytes`
says how much the sender copied. Save the program as `selective.fz`:

```sh
fz2 --log-telemetry t.jsonl run selective.fz   # prints 3
grep '"probe"' t.jsonl
```

| Send | The receiver is parked on | Outcome | Bytes copied |
| ---- | ------------------------- | ------- | ------------ |
| `{:get, ref_a, me, 1}` | nothing yet: the server hasn't run | miss | 48 |
| `{:get, ref_b, me, 2}` | nothing yet | miss | 48 |
| `{:reply, ref_a, 1}` | `{:reply, ^ref_b, v}` | miss | 48 |
| `{:reply, ref_b, 2}` | `{:reply, ^ref_b, v}` | hit | 0: `v` is a number |
| `{:stop}` | `{:get, …}` or `{:stop}` | hit | 0: it binds nothing |

The reply `main` was waiting for crosses as the one value it binds,
and a number needs no copy: it travels as a machine word beside its
kind. The reply it wasn't waiting for crosses whole and waits in the
mailbox. The same five events appear on `interp`, `run` and `build`;
[fixture 02080](fixtures/02080_the_readme_selective_receive_sample_copies_only_what_the_waiting_receive_binds.fz)
is this program, and its test pins them.

A message is measured, then copied once by the sender into one block of
memory the receiver adopts. No process ever writes into another process's heap: the receiver
grafts the sender's block onto its own heap with pointer moves, and its
next garbage collection copies out whatever is still live. A process that
sends to itself skips the scheduler's in-queue: the message is copied once,
straight onto its own mailbox. Because the
receiver's matcher runs on the sender, a `when` guard in a `receive`
runs there too, so it must be pure; a call such as `self()` in a guard
names the receiver, because the receiver evaluates it before it parks.

The receiver gets concierge treatment.

### All of it together: quicksort

```elixir
def append([], ys), do: ys
def append([h | t], ys), do: [h | append(t, ys)]

def partition(_, [], lo, hi), do: {lo, hi}
def partition(p, [h | t], lo, hi) when h < p, do: partition(p, t, [h | lo], hi)
def partition(p, [h | t], lo, hi), do: partition(p, t, lo, [h | hi])

def qsort([]), do: []
def qsort([p | rest]) do
  {lo, hi} = partition(p, rest, [], [])
  append(qsort(lo), [p | qsort(hi)])
end

def main() do
  dbg(qsort([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]))
end
```

Pattern matching, recursion, tuples, lists, multiple clauses — that's
the whole sort, and it's readable end to end. It's also where the second
trick from *The bet* pays off.

The folklore says elegance like this costs allocations: a `{lo, hi}`
tuple built only to be torn apart, the whole `lo` list built and then
walked again and re-copied by `append`, a closure for every "what to do
when this returns." fz mostly doesn't pay. Two compiler ideas get us
there, and **neither asks anything of you**:

- **Destination planning** — before codegen, the planner asks each call
  not just *what type* it returns but *where the result is going*. If the
  caller is about to destructure a pair, the callee hands back two
  register values and never builds the tuple. If a list's eventual tail
  is already known, the callee builds its cons cells pointing at that
  tail from the start — so `append` never walks or re-copies a finished
  list.
- **Owned-cons reuse** — the compiler finds the places where a cons cell
  can be reused in place instead of allocated. A single alias bit in the
  cell, set when the cell is published, decides at runtime: still
  private, relink it; already published, allocate a fresh one. This doesn't bend the immutability
  rule from above — the compiler only exploits privacy the program can
  never observe.

The payoff is measurable and pinned
([fixtures/01577_quicksort.fz](fixtures/01577_quicksort.fz), which adds a
`System.alloc_stats()` readout to this program). Sorting its eleven-element
list allocates **exactly the eleven input cons cells and zero tuples**. On the
native paths the only closures are the two the scheduler builds to start any
program:

```text
list_cons_allocs = 11     # the input list's cells, nothing more
struct_allocs    = 0      # no {lo, hi} tuple ever hits the heap
closure_allocs   = 2      # the scheduler's two start-up closures; none from the sort
```

The non-tail recursion in `append` and `qsort` still needs somewhere to
resume: on the JIT and AOT paths that is 44 heap continuation frames (2432
bytes allocated over the run) — frames, not closures.

Here's what we like: **no reference counting on lists, tuples or closures, no
borrowing annotations.**
Koka-style reuse leans on runtime refcounts; Rust-style reuse leans on
lifetimes and `&` in your source. fz does neither — the source is the
same direct functional code, with no `unique`, no linearity, no "this
list is mine." The compiler finds the reuse sites; the runtime checks one
bit. You get the readability of pure functional code with the memory
profile of a hand-tuned loop.

This is the JIT and the AOT compiler doing their job — turning the
program you'd actually ship into native code that allocates like you
hand-tuned it. (The interpreter runs the same code to the same
answers; they're there to keep us honest, not to win the allocation
game.) ([the full walkthrough](guides/quicksort-without-temporaries.html))

The same machinery now applies through the standard library too. The
runtime-library `Enum.sort/1` is a merge sort with a default comparator
closure. Native code proves that comparator is constant, erases it from
the recursive sort frames, and keeps the hot path closure-free
([fixtures/01460_enum_sort.fz](fixtures/01460_enum_sort.fz)):

```text
Enum.sort list_cons_allocs = 22
Enum.sort closure_allocs   = 2     # the scheduler's start-up pair; the comparator is gone
Enum.sort heap_bytes       = 352
```

That is still a general-purpose library sort rather than hand-shaped
quicksort, so it allocates more cons cells. The important part is that
the abstraction boundary is no longer where optimization stops.

### Talking to C

The OS lives in C. fz doesn't try to hide that — it declares it:

```elixir
extern "C" defp libc::creat(c_string, integer) :: c_int
extern "C" defp libc::write(c_int, binary, integer) :: integer
extern "C" defp libc::close(c_int) :: c_int

def main() do
  fd = libc::creat("/tmp/hello", 420)   # 0o644
  libc::write(fd, <<104, 105, 10>>, 3)  # "hi\n"
  libc::close(fd)
end
```

Each argument has a *marshal class* (`integer`, `float`, `boolean`,
`c_int`, `binary`, `c_string`, `any`, `nil`, … — the externs guide lists
them all) telling fz how to translate between tagged fz
values and the slots C expects. `c_int` is the one that says a value is
32 bits wide, so an error sentinel like `-1` stays `-1` on a machine
whose C library leaves the other half of the register alone. The `c_string` class is a small
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

Types catch mistakes — calls outside a function's `@spec`, clauses that
can never match, the things you'd otherwise find at runtime. (A missing
clause is still a runtime `FunctionClauseError`, as in Elixir.) They also let the compiler skip work: the
more fz can prove about a value, the more direct the code it can emit.
You get both from the same investment.

```elixir
def main() do
  x = 41 + 1
  dbg(x)          # x is known to be an integer: the add runs on raw machine words, untagged
end
```

```elixir
def kind(0), do: :zero
def kind(n) when n > 0, do: :positive
def kind(_), do: :other

def main() do
  dbg(kind(5))   # kind/1 is inlined into main; its dispatch is three machine compares
end
```

The type system is set-theoretic — unions, intersections, negations —
following the Castagna line that Elixir's own typer is built on. Keep
the source language small and pleasant; teach the compiler to learn as
much as it can from it.

### Looking inside the compiler

The rule in this repo: **do not guess.** Make the compiler leave
breadcrumbs.

```sh
fz2 run --dump clif=/tmp/quicksort.clif fixtures/01577_quicksort.fz
fz2 run --dump types=/tmp/quicksort.types fixtures/01577_quicksort.fz
fz2 run --dump activations=/tmp/quicksort.activations fixtures/01577_quicksort.fz
fz2 run --dump backend=/tmp/quicksort.backend fixtures/01577_quicksort.fz
fz2 run --dump native=/tmp/quicksort.native fixtures/01577_quicksort.fz
```

A `run`, `interp`, or `build` command writes each dump to its file (`clif`
needs `run` or `build`, which generate machine code). The supported dump kinds
are `activations`, `types`, `backend`, `native`, `fnir`, and `clif`. Each
function in a `clif` dump ends with the symbol every callee reference (`fn0`,
`fn1`, ...) names.

These answer the questions you actually have while changing things:
*Did this call get folded? Did this function get specialized? Did
the compiler skip something — and why?* How a source file becomes a running
program is in [.agent/docs/pipeline.md](.agent/docs/pipeline.md).

---

## Trying it

Build the compiler:

```sh
cargo build --release
```

That gives you a `fz2` binary at `target/release/fz2` — put it on your
`PATH` (or alias it) and the rest of these commands just work.

Run a file with the JIT:

```sh
fz2 run fixtures/01577_quicksort.fz
```

fz2's options go before the source path. Every token after the path belongs to
the program, verbatim, and `System.argv()` returns them as a list of binaries
(`--` is an ordinary argument):

```sh
fz2 run script.fz input.txt --verbose    # System.argv() == ["input.txt", "--verbose"]
```

A built executable reads its own command line the same way:

```sh
fz2 build script.fz -o /tmp/script
/tmp/script input.txt --verbose
```

Build a native executable:

```sh
fz2 build fixtures/01577_quicksort.fz -o /tmp/qsort
/tmp/qsort
```

Run through the interpreter:

```sh
fz2 interp fixtures/01577_quicksort.fz
```

Run the whole test suite:

```sh
cargo test --workspace
```

[CONTRIBUTING.md](CONTRIBUTING.md) covers the rest of working on fz: test
output, fixtures, CI, and the pre-commit hook.

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
- a working interpreter, JIT (Cranelift), and AOT path
- C externs with marshal classes and resource destructors
- destination planning and owned-cons reuse (see *All of it together:
  quicksort*)

---

## Status

fz is early. The compiler, the runtime, three execution paths, the type
system, the sender-side matcher, destination planning and owned-cons reuse
are all working today — but the language is small, the standard
library is smaller, and the edges are sharp. Expect to read the dumps
when things surprise you.

What's next, roughly in order:

- **OTP behaviors** (`gen_server`, `supervisor`, links, monitors) —
  built in fz on top of the existing process primitives
- **Blocking-aware externs** so `libc::read` doesn't stall a scheduler
  thread
- **Distribution via ETF and disterl** — fz nodes that join existing
  BEAM clusters as ordinary participants in the supervision tree
- **An FBIP tensor type** — the same in-place machinery, extended to
  Nx-shaped buffers: Nx-shape ergonomics, in-place buffer reuse, no
  `defn` ceremony, BLAS/MKL via externs
- **Autodiff** over fz IR
- **A REPL** on the same IR as the other three paths

The current focus is keeping the three execution paths in lockstep and
teaching the compiler to turn more obvious functional code into
efficient native code. Every other goal sits on top of that one.

## Editor Support

The `vscode-fz/` folder contains a minimal VS Code extension for FZ syntax
highlighting and editor defaults. It is TextMate-based only for now: no
language server, no diagnostics, just file association and a grammar tuned
to the language surface.

## Papers that shaped fz

fz didn't invent its good ideas — it borrowed them from people who worked
them out properly. The ones that left the deepest marks:

- **Luc Maranget, _Compiling Pattern Matching to Good Decision Trees_**
  (ML '08). The "one tiny sorting machine" behind every match in the
  language — the decision tree that asks yes/no questions about shape
  and shares the tests adjacent clauses have in common — is this
  paper.
  [pdf](http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf)

- **Alex Reinking, Ningning Xie, Leonardo de Moura & Daan Leijen,
  _Perceus: Garbage Free Reference Counting with Reuse_** (PLDI '21).
  The "garbage-free, reuse cells you can prove are private" goal behind
  reusable-cons transport. Perceus reaches it with runtime reference counts;
  fz chases the same near-zero-allocation profile but finds reuse sites
  statically and checks a single alias bit instead of counting references.
  [pdf](https://xnning.github.io/papers/perceus.pdf)

- **Anton Lorenzen, Daan Leijen & Wouter Swierstra, _FP²: Fully in-Place
  Functional Programming_** (ICFP '23). The discipline that says when
  ordinary functional code can run with no allocation at all — the lens
  we use on destination planning today, and the basis for the planned
  FBIP tensor type.
  [pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf)

- **Giuseppe Castagna, _Programming with Union, Intersection, and
  Negation Types_** (2022). The semantic-subtyping theory the
  set-theoretic type system stands on — unions, intersections,
  negations, and the precise typing of branching and pattern matching.
  [pdf](https://www.irif.fr/~gc/papers/set-theoretic-types-2022.pdf)

- **Giuseppe Castagna, Guillaume Duboc & José Valim, _The Design
  Principles of the Elixir Type System_** (Programming, 2024). The
  Castagna line — referenced above — applied directly to the
  Elixir/Erlang family: function domains tied to arity, guard analysis,
  unified records and dictionaries, and the dynamic type. fz reads like
  Elixir and types like this.
  [pdf](https://arxiv.org/pdf/2306.06391)

## A note on the name

The name is two keystrokes. The project needed to be called something.
If "fz" ends up meaning something later, it'll be because the work
earned it, not because the name promised it.
