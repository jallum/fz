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

- `ModuleId` — `reference_named(name)` for a top-level/runtime module,
  `reference_child_module(parent, local)` for a nested one. `ModuleId::GLOBAL`
  (`0`) is the top-level scope.
- `FunctionId` — `reference_function(module, name, arity)`; generated lambdas get
  ids through `reference_generated`.
- `FunctionRef { module, name, arity }` is the reverse identity — compiler2's
  module/function/arity key. Names are display spellings; the id is the identity,
  so resolution and facts key on the id.

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

`ModuleSource { code, parent, local_name, attrs, kind }` carries the source
facts, where `kind` is `Body { items }` or `Protocol { callbacks }` (see
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

The important split is:

- `FactKey::ModuleDefined(module)` — local body/scoping readiness
- `FactKey::ModuleInterface(module)` — cross-module callable visibility

## Namespaces are a savepoint chain

Name resolution is an append-only chain. A `Namespace` is a `BindingId` — a
savepoint into `NamespaceStore.bindings`. Binding a name pushes a
`{ name, symbol, prev }` and returns the new head; lookup walks from a head
backward and the first matching symbol wins. A `NamespaceSymbol` is a `Module`,
`Function`, `Callable`, `Macro`, or `Type`.

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
   Later jobs wait only when they need more than that placeholder:
   macro expansion waits for the provider interface when it must decide whether
   a reserved callable is a macro, and module-interface publication validates
   that each exact expectation was actually exported. Then define each reserved
   function and scope each child module onto the current head.

A non-private function or macro becomes a `ModuleInterfaceCallable`; private
(`fnp`) functions stay callable in-module but out of the interface. Non-global
modules that do not define `__info__/1` get a synthesized ordinary function
source for their callable interface. The pass returns the finished namespace head
plus the callable interface, which `define_module` freezes onto the module slot.

## Runtime library and the prelude

Runtime-library modules are not a special class. At construction the world
`reference_named`s each runtime module so its name is a stable id, but it does
**not** submit any source. The first real reference pulls the owning module's
source through `ensure_runtime_module`, which `submit_code`s it as ordinary code;
the same `index_code` / `scope_code` / `define_module` jobs handle it.

The prelude (`runtime.fz`) is scoped first as ordinary code: when `scope_code`
sees the prelude it scopes from an empty namespace and saves the resulting head
as the prelude head; every other code contribution then scopes from that head
(and waits on the prelude's `CodeScoped`). So default visibility is a saved
namespace head, not a compiler phase.

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
cargo test --lib compiler2::drive_test::compiler2_submit_root_pulls_scope_and_seeds_entry_semantics_without_warming_foo
cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer
```
