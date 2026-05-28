# Semantic Codegen Operations

The unit of Cranelift lowering is one fz function body. That body needs a
Cranelift `FunctionBuilder`, the Cranelift module, immutable `CodegenEnv`,
mutable per-function `CodegenCache`, and function-local imports.

`CodegenFn` is the fz-owned boundary for that unit of work. Ordinary lowering
should grow toward semantic methods on this context, such as list access,
closure capture access, value boxing, struct field writes, and alias
publication. Those methods may currently call runtime BIFs, but the call is an
implementation detail. A later inline CLIF implementation should be local to
the semantic method.

Direct `declare_func_in_func` use belongs at module-construction boundaries or
inside `CodegenFn`/semantic operation implementations. Migration tickets must
remove the bridge code they introduce before closing; do not leave old and new
paths in parallel.

The cleanup has a source-level budget test for ordinary lowering modules. When
a ticket removes more runtime-call plumbing, lower the budget in that test. A
new direct import or `runtime.*` helper reference should either move behind a
semantic `CodegenFn` method or be documented as a boundary exception.
