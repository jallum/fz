# Semantic Codegen Operations

The unit of Cranelift lowering is one fz function body. That body needs a
Cranelift `FunctionBuilder`, the Cranelift module, immutable `CodegenEnv`, a
mutable per-function `CodegenCache`, and function-local imports.

`CodegenFn` is the fz-owned semantic boundary for that unit of work. Ordinary
lowering constructs one `CodegenFn<BodyContext>` per lowered fz function body;
it owns the runtime refs and the function-local `FuncId -> FuncRef` import
table. Helpers still receive the Cranelift builder, module, and cache
explicitly because those borrows are short-lived, but semantic operations such
as list access, closure capture access, value boxing/unboxing, struct field
writes, owned-cons reuse, and alias publication should flow through
`CodegenFn`.

Value coercion is part of that semantic surface. Lowering code should call
methods such as `cx.value_as_any_ref`, `cx.value_raw_int`, `cx.value_truthy`,
and `cx.tagged_var`; the private `codegen_value_*` and `tagged_get` helpers are
implementation details inside `value.rs`.

Generated runtime shim bodies do not have a `CodegenEnv`, so they use
`CodegenFn<RuntimeShimContext>` through `CodegenFn::for_runtime_shim`. That
constructor is a boundary marker, not a shortcut for ordinary lowering helpers.
Shared semantic operations may be implemented for both context markers, but
new ordinary-function-only state should live on `BodyContext` rather than being
made available to shims by accident.

`CodegenFn` methods may currently call runtime BIFs, but the call is an
implementation detail. A later inline CLIF implementation should be local to
the semantic method.

Direct `declare_func_in_func` use belongs at module-construction boundaries,
dynamic user-function calls, or inside `CodegenFn`/semantic operation
implementations. Codegen changes should remove the bridge code they replace
before landing; do not leave old and new paths in parallel.

Small runtime helper calls in ordinary body lowering should be named
`CodegenFn` semantic methods before they spread. `call.rs`, `closure.rs`, and
`entry.rs` are pinned to zero direct function imports; new direct imports there
should move behind `CodegenFn` unless they are truly dynamic user-function
boundaries.

The cleanup has source-level budget tests for ordinary lowering modules. They
pin direct imports, `runtime.*` helper reach-ins, retired helper-local
constructors, the single ordinary function context, and explicit runtime-shim
contexts. When work removes more runtime-call plumbing, lower the budget in
that test. A new direct import or `runtime.*` helper reference should either
move behind a semantic `CodegenFn` method or be documented as a boundary
exception.
