# Modules and Namespaces

A module is a unit of naming and definition. The module subsystem owns four
things: stable identity, the lifecycle a module passes through from a bare
reference to optional source plus optional callable interface, the namespace
chain that resolves names inside a scope, and how runtime-library modules enter
a compile. The end-to-end flow that drives these transitions is in
[`pipeline`](pipeline.md); this doc is the data model behind the definition
stratum.

## Identity is allocated on reference

Referencing a module or a function allocates a stable id immediately; defining it
later fills the state behind that id.

- `ModuleId` — `reference(name)` for a top-level/runtime module,
  `reference_child_module(parent, local)` for a nested one. `ModuleId::GLOBAL`
  (`0`) is the top-level scope. `ModuleMap` keys and retains the parsed
  `ModuleName`; an implementation is the module named `Protocol.Target`.
  Source boundaries survive reservation, definition, lookup, function
  denotations, and quoted references, which name a module by its atom.
- `FunctionId` — `reference_function(module, name, arity)`; generated lambdas get
  ids through `reference_generated`.
- `FunctionRef { module, denotation }` pairs a World-local module coordinate
  with the shared immutable `FunctionDenotation`. Its typed source origin owns
  semantic order; local ids key resolution and facts.

A function or module can be *referenced* without being *defined*: a placeholder
id exists, callers can name it, and the surface fills in when its source is
scoped. An uncalled definition stays a cold fact (see [`pipeline`](pipeline.md)).

## The module lifecycle

`ModuleState` is the slot behind a `ModuleId`. Source/body state and interface
state are separate concerns, so the slot may have either, both, or neither:

```text
Placeholder { interface? }             referenced, no source yet
Indexed { source, interface? }         source discovered during code indexing
Scoped { source, base, interface? }    a base namespace head has been chosen
Defined { source, base, interface }    the module body is published
```

A module's stage only moves forward for the same source: indexing a Scoped or
Defined module again from the source it already has (`ModuleState::reconcile`)
keeps the stage and reports no change, so a file's top-level walk that re-runs
after `ModuleDefined` does not un-define the module it was waiting on. A
different source starts the module over at Indexed.

`ModuleSource { code, parent, source, kind }` carries the source facts and
parent ownership edge. `ModuleMap` interns each module by its `ModuleName`, whose atom is the module's
identity in value position; consumers do not reconstruct it from parent and local display spellings.
`kind` is `Body`, `Protocol`, or `ProtocolImpl` (see
[`protocols`](protocols.md)). `ModuleInterface` is the module-owned callable
surface: exported callables are represented by `FunctionId`-backed entries plus
callable kind (`PublicFunction` or `Macro`) and variadic metadata.

Four jobs drive the transitions:

```text
index_code     parse a code contribution; discover_modules registers each nested
               module/protocol as Indexed, then publishes CodeIndexed
scope_code     pick the base namespace, run define_scope over GLOBAL, publish CodeScoped
define_module_interface
               publish an already-known interface for a module that may not have
               source/body state in this compiler run
define_module  scope the module body (or protocol surface) and publish ModuleDefined
```

`define_module` waits for what it needs and asks for it: a child waits on its
parent's `ModuleDefined` (or `CodeScoped` when the parent is global); a
not-yet-pulled runtime module waits on its `CodeIndexed` after
`ensure_runtime_module` submits its source. `define_module` also derives and
publishes `FactKey::ModuleInterface(module)` for source-defined modules.

`require` and `import` refuse a module defined inside the requiring scope's own
body (`World::module_defined_within`, checked in
`ScopeDirective::apply_require` and `apply_import`), as Elixir does: that module is not loaded until the scope that
defines it has finished. The diagnostic is `resolve/module-not-loaded` at the
`require`/`import` span. A module defined earlier outside the requiring
`defmodule` is required normally.

The important split is:

- `FactKey::ModuleDefined(module)` — local body/scoping readiness
- `FactKey::ModuleInterface(module)` — cross-module callable visibility

## Namespaces are a savepoint chain

Name resolution is an append-only chain. A `Namespace` is a `BindingId` — a
savepoint into `NamespaceStore.bindings`. Binding a name pushes a
`{ name, symbol, prev }` and returns the new head; lookup walks from a head
backward and the first matching symbol wins. A `NamespaceSymbol` is a `Module`,
`Function`, `Callable`, `Macro`, `Type`, or `Splice`. A `Splice` binds a name to
a quoted AST snippet that the macro expander substitutes in place when the name
is referenced — a generic primitive that binds a module's attributes (see "A module attribute" below).
A splice binding is interned by what its value says (`semantically_eq` at
`Horizon::Full`), not by the heap that holds it: binding a name to a rebuilt but
equal value on the same head returns the namespace bound before.

```text
bind(head, "add", Function(f))  -> head'      (a new savepoint over head)
lookup(head', "add")            -> Function(f)
bind(head, "t", Type(type_t))    -> head''     (type names use the same chain)
```

This is what lets a scope extend its parent's visibility without copying: a child
scope's base is its parent's head, and entering/leaving a scope is just choosing
which head to bind onto. Type lookups filter for `NamespaceSymbol::Type`, while
value/callable lookups filter for modules/functions/macros, so a type name and a
value name can share spelling without becoming one binding kind.

A `CallableName` asks the chain at most once. Its qualifier is a `ModuleTarget`,
so an alias path written in source (`Unresolved`) stays distinct from a module
named by its atom (`Exact`), which no alias in scope redirects, and `World::callable_name_qualifier` answers which
module a qualified name names. Nothing splits a rendered `Module.function`
string back into a module and a name: a callable that was already resolved
travels as the function itself.

## One answer to "which module does this name mean"

`World::resolve_module_name(head, path)` is the one answer, for every position
a module name is written in: a value, a struct, a call's qualifier, a capture,
the macro expander's remote-call check, a `defimpl`'s protocol and target, and
the prefix of a dotted type (`Geo.Pt.t`). The rule is Elixir's:

- the first segment is looked up in scope `head`, and the remaining segments
  are walked from the module it binds (`alias Foo.Bar` makes `Bar.Baz` mean
  `Foo.Bar.Baz`; a nested `defmodule Inner` binds `Inner` in its parent);
- a first segment nothing binds means the name is the root module spelled
  that way. `Enum.count(x)` needs no alias, and a root `defmodule Geo.Pt` is
  reached by `Geo.Pt.f()` though nothing binds `Geo`.

The module a name is written inside adds nothing: inside `defmodule Geo.Pt`,
`Pt` alone is the root module `Pt`, as in Elixir. A qualifier is therefore
always a module, defined or not. One nothing defines is reported when the wait
on its definition goes unanswered (`resolve/unknown-module`), not at
resolution; `lower/unbound` is for an unqualified name nothing binds.

## A module name is a value

In value position a module alias is an atom, as in Elixir. The decoder turns
`{:__aliases__, meta, [:Foo, :Bar]}` into `Expr::Alias(ModuleName)`, keeping
the segments it was written with. `World::module_alias_atom` answers which atom
that is: it resolves the alias through `resolve_module_name`, so a name the
namespace binds (`alias Foo.Bar, as: B` makes `B` mean `Foo.Bar`) gives its
target and any other name gives itself, and returns
`ModuleName::atom_name`, the full path under the `Elixir` root
(`Elixir.Foo.Bar`). Body lowering and guard reification both ask it, so `B` in
an expression and `x == B` in a guard are the same constant atom, typed as that
singleton atom. A name no module defines is still its atom: resolving it mints
a placeholder id and starts no module work. A qualified callee
(`Foo.Bar.f()`) reads the same segments as its `ModuleTarget::Unresolved`
qualifier.

## A module's atom

A module's identity is an atom, as in Elixir. `ModuleName` holds either an
alias path or a bare atom, and `ModuleName::atom_name` and
`ModuleName::from_atom_name` are the one mapping between module and atom, in
both directions:

| module | atom |
| --- | --- |
| `Foo.Bar` (an alias path) | `Elixir.Foo.Bar` |
| `:erlang` (a bare atom, `ModuleName::bare_atom`) | `erlang` |

An atom that starts `Elixir.` followed by a well-formed path is that path's
module. Any other non-empty atom is the bare-atom module of that name, so
`:Foo` is a module distinct from `Foo`. `Elixir.` followed by no path, or an
empty atom, names no module. A bare-atom module prints as `:erlang`
(`ModuleName`'s `Display` and `dotted`, which `parse_dotted` reads back).

`defmodule :name do ... end` parses to `defmodule` whose first argument is the
atom, and `parse_module_name` in `quoted_surface.rs` reads it as the bare-atom
module. Such a module is never nested under its parent and binds no alias in
the namespace; it is reached by its atom. `__MODULE__` in it is that atom.
Only `defmodule` takes a bare atom; protocols and implementations take alias
paths.

`lib/erlang.fz` defines `:erlang` with `float_to_binary/2`, which takes
`decimals: n` for an integer `n` from 0 to 253 and writes the float in fixed
notation (`fz_float_to_fixed_binary`, rounded from the exact value with a tie
going away from zero) and `[:short]`, which is `Float.to_string/1`'s shortest
round-trip text. Any other option or an out-of-range `n` has no clause.
It also defines `raise/3`, which raises `reason` again as the kind it is
given (`:error`, `:throw` or `:exit`) and ignores the stacktrace. `error/1` raises
`reason` with the kind `:error`, as `Kernel.panic/1` does (`01382`); `error/3`
is `error/1` with the argument list and `error_info:` options ignored.

The BIFs `json.erl` calls are source in the same module (`01813`, `01814`):
`element/2`, `binary_part/3` (a negative length counts back from the start; it is
guard-callable, as in Elixir),
`iolist_to_binary/1`, `iolist_size/1`, `integer_to_binary/1` and `/2`,
`atom_to_binary/2` (`:utf8`, `:unicode`, `:latin1`), `is_map_key/2`,
`binary_to_float/1` and `binary_to_integer/1`. A call they cannot answer raises
`ArgumentError` listing every faulty argument as Erlang's error formatter does
(`is_map_key/2` raises `BadMapError`). `String.to_float/1`,
`String.to_integer/1` and `IO.iodata_to_binary/1` delegate to them as
Elixir's do. An iolist whose tail is a binary is handled by `iolist_to_binary/1`.

`lib/binary.fz` defines `:binary` with `at/2`, `copy/1`, `copy/2` and
`referenced_byte_size/1`. `at/2` reads the byte with a
`<<_::binary-size(pos), byte, _::binary>>` match; a position at or past the end
raises `ArgumentError` with the message `argument error`, as OTP's BIF does.
`copy/2` is the extern `fz_binary_copy`, which builds
the result in one buffer; `String.duplicate/2` is `:binary.copy/2`. `copy`
takes a binary and `referenced_byte_size` takes any bitstring, as in OTP. A
subject that is not a bitstring, or a count that is not a non-negative integer,
raises `ArgumentError` with Elixir's per-argument wording; a bitstring whose bit
length is not a multiple of 8, given to `copy`, is reported as
`is a bitstring (expected a binary)` (`01338`). The specs name `binary` and
`bitstring`, so a call whose argument is proven to be something else is refused
at compile time; a value that may be a binary compiles and raises when it runs.

`lib/lists.fz` defines `:lists` with `reverse/1`, `reverse/2`, `duplicate/2`,
`map/2` and `foldl/3`, clause for clause as OTP's `lists.erl` writes them.
`reverse/2` is a BIF in OTP and is written in fz here. `map/2` and `foldl/3`
guard `is_function(f, 1)` and `is_function(f, 2)`; `duplicate/2` guards
`is_integer(n) and n >= 0`. The specs are OTP's, so a call whose arguments are
proven outside them is refused at compile time.

`lib/unicode_util.fz` defines `:unicode_util` with `cp/1` and `gc/1`, the next
codepoint and the next extended grapheme cluster of chardata (a binary, or a list
of codepoints, binaries and chardata, improper tails included). Both answer `[]`
for empty chardata and `{:error, rest}` when `rest` begins with a binary that is
not UTF-8; `gc/1` decides cluster ends by the same rules as
`String.next_grapheme/1`. Fixture 01944 compares every case against Elixir.

`lib/maps.fz` defines `:maps` with `to_list/1`, `keys/1`, `values/1`, `put/3`,
`merge/2` and `from_list/1`. `to_list/1`, `keys/1` and `values/1` are each a
single runtime walk of the map's entries; `put/3` is the extern `fz_map_put`,
in OTP's argument order (`put(key, value, map)`); `from_list/1` builds through
the extern `fz_map_from_kv` (the last pair for a key wins); and `merge/2` is
`from_list(to_list(a) ++ to_list(b))`. Each of `to_list/1`, `keys/1`,
`values/1`, `put/3` and `merge/2` raises `BadMapError` for a non-map, behind an
`is_map` guard (`merge/2` names the first argument that is none).
`Map.to_list/1`, `keys/1`, `values/1`, `put/3`, `merge/2` and `new/1` delegate
to them, as Elixir's `Map` does, and `Map.take/2`, `drop/2` and `filter/2` build
their results through `from_list/1`. `Map.delete/2` and `Map.get/2` raise
`%BadMapError{}` for a non-map, and every `Map` function that returns a map
says `:: map` in its spec.

`lib/bitwise.fz` defines `Bitwise` with `band/2`, `bor/2`, `bxor/2`, `bnot/1`,
`bsl/2` and `bsr/2` and the operators `&&&`, `|||`, `<<<` and `>>>`. As in
Elixir each delegates to the `:erlang` function of the same name; those
(`lib/erlang.fz`) are the typed clause families over `is_integer` heads that
call one `fz_op_b*` extern, as `Kernel.rem/2` and `Kernel.+/2` do. A guard may
call any of them, and native code computes them in place (`recipe.rs` rows; the
interpreter calls the runtime function). Each is `@doc guard: true`. A
non-integer operand raises `ArithmeticError`. Integers
are 64 bits wide: `bsl/2` and `bsr/2` raise `ArithmeticError` where Elixir would
grow a bignum, a result that needs more than 64 bits (`bsl(1, 63)`,
`bsr(1, -63)`). `bsl` by a negative count shifts right and `bsr` by a negative
count shifts left, as in Elixir (`01818`). `use Bitwise` and the deprecated
`~~~` and `^^^` are not defined.

## A call by name

`f(a)` always names the function `f/1`, as in Elixir, even where a variable
`f` is bound; the closure a variable holds is called with `f.(a)`. Body
lowering (`direct_callee`, `jobs/body.rs`) resolves a bare name as a function
without looking at the scope, and the scope walk (`jobs/scope.rs`) does not
count that name as a use of the variable, so `value = 3; value(1)` warns that
`value` is unused (`01781`).

## A call on a module value

`m.f(a)` whose base is not a module name is a call on the module the value
`m` holds. A field read is the same syntax without the call (`m.f`), and
`m.f.(a)` calls the closure that field holds. Body lowering emits
`LoweredTail::DirectCall` whose callee is
`DirectCallee::ModuleValue { module, function }`: the value of `m`, lowered
before the arguments, and the name `f`. The module is not one of the call's
arguments.

Semantic analysis resolves the call from the type of `m`
(`jobs::semantic::resolve_module_value_call`, `module_value_receiver`). The
atoms in the type say which modules the value can be.

When the type lists its atoms, they are the modules. Each atom names a module
absolutely through `ModuleName::from_atom_name` and `World::reference_module`,
and `World::module_public_function` answers that module's public `f/n`; a
qualified callee in source asks the same method.

When the type holds atoms it does not list (`atom`, `any`), the value can be
any module a value can name. `World::nameable_modules` is that set, ordered by module name, so the
order of the callees and of the modules that lack `f/n` is a function of the
set's members and not of when each was noted: every
module whose source the compile has indexed (`source_publish::
publish_module_indexed`), every module a lowered body writes as a value, in
an alias or a struct (`Lowerer::name_module_as_value`), and the module of every
exception any program of the compile can raise (`World::note_raisable`, see
[exceptions](exceptions.md#what-a-handler-can-receive)). The set is the
fact `FactKey::NameableModules`, which the call reads whether or not it holds
anything yet. `nameable_module_callees` waits for each of those modules to be
defined, reads its `ModuleInterface`, and keeps the ones that have a public
`f/n`. It asks for no function body, so a module that lacks `f/n` is defined
for the call and none of its functions is compiled for it.

Each function is then resolved as any direct call is, and its targets carry
the atom that selects them in `CallTargetSummary.selector`. Every direct
callee is planned (`plan_direct_call`) before any is prepared
(`prepare_keyed_call`): preparing mints the callee's activation and waits on
its return, so a call that finds one callee unready prepares none, and no wait
stands without a row of the caller's behind it. A protocol callback among the
callees is resolved by `resolve_protocol_call` after the direct callees are
prepared; that call is all-or-none among its own targets, not with the
module-value call's other callees.

The values no module claims are the receiver's type less the selectors. When
that is not empty the call has one more target, the miss:
`SelectedCallee::Undefined(UndefinedFunction)`, selected by that remainder,
with no activation and the return type `none`. It carries the function, the
arity and the atoms of the nameable modules that lack the function. The miss
goes through `call_destinations` as any target does and materializes as
`CallTarget::Undefined`.

| type of `m` | the call |
| --- | --- |
| one atom | one target: `CallDestinations::Direct`, and no read of `m` at run time |
| several atoms | one target per atom: `CallDestinations::Dispatch`, whose plan reads `m` as its first input |
| `atom`, `any`, or a listed atom joined with something that is no atom | a target per nameable module that has `f/n`, and the miss |
| a type holding no atom | compile error `type/module-value-call` |
| a listed atom naming no module, or a module without `f/n` | the compile error a qualified call to it gets (`resolve/unknown-module` for `:nosuch.thing(1)`) |

Both executors lower the miss as a raise that shows the value of `m`. Native
lowering (`NativeLowerer::raise_undefined_function`) ends the block in
`Term::RaiseUndefined`, whose codegen calls `fz_raise_undefined_function`; the
interpreter (`ir_interp::backend::raise_undefined_function`) calls
`failure::raise_undefined_function`. The runtime words the exception as Elixir
does:

| value of `m` | raises |
| --- | --- |
| an atom naming a module that lacks the function | `UndefinedFunctionError`, `function M.f/n is undefined or private` |
| any other atom | `UndefinedFunctionError`, `function :a.f/n is undefined (module :a is not available)` |
| `nil` | `UndefinedFunctionError`, `function nil.f/n is undefined` |
| a value that is no atom, `n > 0` | `ArgumentError`, `you attempted to apply a function on V. Modules (the first argument of apply) must always be an atom` |
| a value that is no atom, `n == 0` | `ArgumentError`, `you attempted to apply a function named :f on V. ...` |

An `UndefinedFunctionError` carries `module`, `function`, `arity`, `reason`
(`nil`) and `message`.

A module in a library file the compile never indexed is not nameable, so a
call that reaches it by a computed atom raises "is not available". A map given
such a module under `__struct__` is likewise no struct of it: it prints as a
map and reaches no `defimpl`. A nameable module is the struct it declares for
a map that names it while the program runs (see
[fact engine](fact-engine.md#root-local-struct-schemas)). With no
arguments and parentheses, `m.f()` on a map raises `ArgumentError`; Elixir
reads the field and warns.

A dispatch plan's inputs are the selector and then the arguments
(`CallSiteSummary::arity`). `BackendTail::DirectCall.selector` holds the value
of `m`; both executors read it for the plan and pass only `args` to the
target, so the arguments stay one-for-one with the callee's inputs.

The activation key keeps `m` whole (`jobs::keying`), so callers passing
different modules keep different keys and each key's call has one target.
`e.__struct__.message(e)` is this call: the `__struct__` field of a struct
type is one atom.

`apply(m, :f, [a, b])` is this call too. `Kernel.apply/3` (`lib/kernel.fz`) is
a macro that answers the remote-call node `m.f(a, b)` when the function is an
atom and the arguments are a list, both written at the call. Any other call of
it raises in the macro, and a macro's raise is a compile error at the call
(`lower/unsupported`).

Fixtures `00864` (one module), `00865` (several), `00867` (an atom made at
run time), `00869` (every miss) and `00870` (`apply/3`) agree with Elixir on
interp, run and build; `00866` and `00871` are the refusals.

## Scoping a body

`define_scope` walks a scope's items in two passes so bodies can reference names
declared later in the same scope:

1. **Reserve.** Bind every local function (as `Function`/`Macro`), every noted
   `@type` name (as `Type`), and every child module / protocol name, so forward
   references resolve in both value and type positions.
2. **Apply, in source order.** Resolve `alias`, `import`, and `require`.
   Exact `only:` imports/requires can mint `FunctionId`s lazily by recording
   interface expectations and binding `Callable` placeholders immediately.
   Set-valued `import M` / `import M, except: ...` and the corresponding
   `require` forms wait on `FactKey::ModuleInterface(module)`, because they
   need the provider's full exported callable set before they can bind names.
   `require` also publishes the required module path into the lexical
   namespace so qualified remote macro calls can resolve the module name. For
   a dotted path such as `Foo.Bar`, the full path is made visible through
   `Foo`; the short name `Bar` still requires an explicit `alias`.
   Separately, `require` binds a required-macro entry in the lexical namespace
   for each selected remote macro `FunctionId` this scope may expand, and an
   `import` of a module (with or without `only:`/`except:`) makes all of that
   module's macros callable the same way. A visible module with neither still
   trips `macro/not-required`.
   A module or protocol declaration binds a name in its declaring scope as
   Elixir's `defmodule` does: a single-segment name binds itself; a dotted name
   nested in a module binds only its first segment, to the parent's child of
   that segment (`defmodule H.T` inside `M` defines `M.H.T` and makes `H.T`
   reach it); a dotted name declared at the root binds nothing, so `Geo.Pt` is
   reached only by its full path and `Pt` stays free for another module.
   Later jobs wait only when they need more than that placeholder:
   macro expansion waits for the provider interface when it must decide whether
   a reserved callable is a macro, and module-interface publication validates
   that each exact expectation was actually exported. Then define each reserved
   function and scope each child module onto the current head.

### One definition stands

The clauses of a function that sit together in a body are one definition
(`read_surface` gathers neighbours of one name and arity into one form). The
walk keeps, for each function of the module, a `LocalCallable`: its symbol, how
many of its definitions are reserved and not yet reached, how many a later one
has replaced, and where it stands (`Standing::NotDefined`, `Defined` or
`Overridable`). A defined or overridable function holds its `ReachedDefinition`:
the form, the namespace it was reached in and its owner module.
`reach_definition` applies the rules as the walk reaches each definition:

| The function is | Arrives | Result |
|---|---|---|
| not defined | a definition | defined |
| defined | `defoverridable name: arity` | overridable |
| overridable | a definition of the same kind | the new definition stands, and the mark is spent |
| defined | a definition | `resolve/duplicate-function`, pointing at both |
| not defined, or overridable | `defoverridable` | `resolve/overridable` |
| overridable function | a macro, or the reverse | `resolve/overridable` |

`read_surface` also records, in `ScopeSurface::ungrouped`, each clause written
after another function's clause although an earlier clause of its own name and
arity exists. Only another function's clause separates clauses: a statement, a
macro call or an attribute between them does not, as in Elixir, where only a
stored definition moves the "last definition". `discover_modules` emits each
one as `resolve/ungrouped-clauses` through `emit_warning_once`, in Elixir's
words: "clauses with the same name and arity (number of arguments) should be
grouped together", or "clauses with the same name should be grouped together"
when the clause before it has the same name and another arity, followed by
`"def h/1" was previously defined (file:line)` for the first clause. Fixture
`01938` carries the warning text.

A definition with another of the same function still to come is recorded and
not published: its source is never noted, so nothing expands or compiles it.
The definition that stands is published once, and the interface is that
definition's, so a `defp` that replaces a `def` takes the function out of the
interface. A definition a macro expands to is counted when the macro's
fragment is reserved, which is when the walk reaches the macro call; a
replacement that arrives that way, after the default was already published,
replaces the published source.

A definition that replaces an overridable one sees it as `super`.
`publish_super` publishes the replaced definition as a private function named
the way Elixir names it, `name (overridable N)` with `N` counting the
function's replaced definitions, in the namespace and owner module it was
reached in. The replacing definition's namespace binds `super` to it, so
`super(args)` resolves as an ordinary local call, wherever it is written in
that definition, including in an `fn` and in a macro's expansion. A `super`
whose arity differs from the function's, or one written in a definition that
replaces nothing, resolves to nothing and is `lower/unbound`. Each override in
a chain sees the one before it. The replaced definition's source is noted;
like any function, nothing lowers it unless `super` calls it. The walk
publishes it when it reaches the replacing definition, from the same ground,
so its source is an output of that definition's derivation rather than a
derivation of its own (`LocalCallable::superseded`).

`defoverridable` is `ScopeForm::Overridable`, read by `build_form`. It takes
`name: arity` pairs. Fixtures `00872` and `01303` are the oracle fixtures;
`00873` through `00875` are the refusals.

Clauses of one function join across items when an item macro or an unquote
fragment adds them. Each clause carries its `ClauseOrigin`, `Written` or
`Expanded`. A clause of `Expanded` origin whose name and arity the module
already defines, or a written clause that follows an expanded one, joins the
function (`ReachedDefinition::takes_clauses_of`): the walk publishes the
function again with every clause so far, superseding the earlier publication
the way `defoverridable` does. Two written definitions apart stay a second
definition and are refused, so a function that gains no clause later is
published once. Fixture `01933` holds the join.

A `defstruct` form defines the module's `__struct__/0`. The walk reserves it
with the body's other names and applies `def __struct__(), do: %__MODULE__{}`
(`build_struct_function`) where the form stands, through the path a written
`def` takes, so a module that writes its own `__struct__/0` is refused with
`resolve/duplicate-function` (fixture `00881`). `Kernel.struct/1`,
`struct/2` and `struct!/2` (`lib/kernel.fz`) start from `module.__struct__()`,
a call on a module value, and replace the fields they are given with
`Map.replace/3` and `Map.replace!/3`. `struct!/2` on a module also takes the last
`:__struct__` pair of its fields: another module than the one named raises
`ArgumentError`, after any `KeyError` for an undeclared key; `struct/2` ignores
the pair. Fixtures `00880` and `01903` agree with Elixir on interp, run and
build.

A non-private function or macro becomes a `ModuleInterfaceCallable`; `defp`
functions stay callable in-module but out of the interface. A qualified call
`M.f(...)` resolves through `World::module_public_function`: once `M`'s
interface is known it answers from the interface, and a name the interface
does not export (a `defp` among them) is `resolve/unknown-import` at the call's
span; before then the call records an expectation that `define_module` checks
when `M` is defined. Fixtures `01300` (call after the module) and `01301`
(call before it) are the refusals. Non-global
modules that do not define `__info__/1` get a synthesized ordinary function
source for their callable interface. The pass returns the finished namespace head
plus the callable interface, which `define_module` freezes onto the module slot.

## Runtime library and the prelude

Runtime-library modules are not a special class. At construction the world
`reference`s each runtime module so its name is a stable id, but it does
**not** submit any source. The first real reference pulls the owning module's
source through `ensure_runtime_module`, which `submit_code`s it as ordinary code;
the same `index_code` / `scope_code` / `define_module` jobs handle it. Runtime
registration happens before named-parent resolution, so a dotted runtime module
such as `String.Chars` owns and indexes its own source instead of waiting for
its ordinary `String` parent.

A runtime module is registered in one place: its `RuntimeModuleSource` entry in
`src/modules/runtime_library.rs`, which names the file under `lib/`. The
prelude binds no name for it: `OptionParser.parse/2` in user code names the
root module `OptionParser` as any unbound name does, and the first call pulls
the source. `lib/elixir_quote.fz` defines `:elixir_quote`, the functions a spliced `quote` calls
(`list/2`, `tail_list/3`). A module named by a bare atom (`:erlang`, `lib/erlang.fz`) has the
registry name `":erlang"`: `:erlang.f(x)` names its module by the atom, and
the first call pulls the source like any other runtime module.

The one place the bootstrap is special is *reading*: `is_bootstrap(code)` (the
prelude plus the runtime modules) is read canonically — definition heads are parsed as
definitions rather than macro calls — because the macros that implement def-heads
are defined in the bootstrap and cannot be bounced through. Everything else is
ordinary user source; see macro-expansion.md.

The prelude (`runtime.fz`) is scoped first as ordinary code: when `scope_code`
sees the prelude it scopes from an empty namespace and saves the resulting head
as the prelude head; every other code contribution then scopes from that head
(and waits on the prelude's `CodeScoped`). So default visibility is a saved
namespace head, not a compiler phase.

Root submission does not force that prelude work by sweeping all code. A root
waits for its entry function facts; the function-source demand selects the
indexed code surface that can publish that entry, and that code's `ScopeCode`
is what pulls `CodeScoped(runtime_prelude)` if needed. The ownership chain is
therefore root -> entry fact -> candidate source surface -> prelude namespace,
never root -> every code contribution.

There is no `.fzi`/`.fzo` store and no separate-compilation sidecar: a program's
module world is the source it submits plus the runtime-library source pulled on
demand. A user module is present only when its source was submitted.

## Where it lives

```text
identity.rs    ModuleId / FunctionId / FunctionRef, ModuleState, ModuleSource,
               ModuleMap, FunctionMap
module_interface.rs
               ModuleInterface, callable entries, exact expectations, ready/pending queries
namespace.rs   NamespaceStore, BindingId (Namespace), NamespaceSymbol
runtime.rs     bootstrap — reference runtime module names; pull source lazily
jobs/source.rs index_code / scope_code / define_module / define_scope / discover_modules
```

## Proof gates

```text
cargo test --lib compiler2::world_test
cargo test --lib compiler2::namespace_test
cargo test --lib compiler2::drive_test::a_call_on_one_module_is_a_direct_call_keyed_by_the_module
cargo test --lib compiler2::drive_test::a_call_on_one_of_two_modules_dispatches_on_the_module_and_passes_only_the_arguments
cargo test --lib compiler2::drive_test::a_replaced_definition_is_never_noted_and_the_interface_follows_the_one_that_stands
cargo test --lib compiler2::drive_test::compiler2_submit_root_pulls_scope_and_seeds_entry_semantics_without_warming_foo
cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer
```

## A module attribute

`@name value` is a `ScopeForm::Attribute`, ordered among the module's forms.
`@doc` and `@spec` attach to the next function, `@type` is a scope attribute,
and any other name is a value attribute, `@moduledoc` and `@typedoc` among
them. The documentation attributes take any expression: a heredoc, a sigil, a
`<>` concatenation, another attribute, a bracketless keyword list
(`@doc since: "1.0"`), `false` and `nil` all work. The value must be a binary,
`false`, `nil` or a list, or the definition is refused with
`lower/invalid-documentation`; the compiler keeps no documentation text. A
function's `@doc` is evaluated, through the same evaluator, when the walk
reaches the function (`ScopePublisher::evaluate_function_docs`).
`ScopePublisher::apply_attribute` binds
`"@name"` as a `Splice` to the value's quoted code: a written literal is its own
code, and an expression that computes runs once, while the module is defined,
through the definition-time evaluator with `Macro.escape/1`
(`src/compiler2/definition_time.rs`), so it sees the attributes set above it.
Every definition after it records that namespace, so `@name` in its head, guard
or body reads the value nearest above the definition, as in Elixir. The
expander rewrites the read `{:@, _, [{name, _, nil}]}` to that splice; a read
of an attribute never set warns `lower/undefined-attribute` in Elixir's words
and reads `nil`. A macro's quoted `@name` is read in the module the macro
expands in. A nested module starts from its own namespace, so it reads only
its own attributes. Fixtures `01785` and `01786` hold these.

A form between two written clauses of one function, an attribute among them,
closes the clause group, so the later clause is a second definition.

