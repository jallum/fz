# Runtime Predicate Programs

`runtime/src/predicate_program.rs` owns the executable representation of a
runtime membership question. A `RuntimePredicateProgram` is an immutable,
finite graph: POD nodes name operations and ranges in an indexed `u32` edge
table. Its nodes carry only tags, atom ids, arities, and indices. It never owns
`AnyValue`, `AnyValueRef`, a process-heap address, a closure pointer, or a
compiler `Ty`.

That boundary is deliberate. Type projection belongs to the compiler, while
the runtime owns the exact execution of the already-projected graph. Native
primitive tests and receive must consume this one runtime artifact when their
compiler bridge is added; neither may re-derive recursive membership.

## Static-data ABI and ownership

`RuntimePredicateProgramStatic` is `repr(C)` and begins with
`RUNTIME_PREDICATE_PROGRAM_ABI_VERSION`. It contains the root node index and
pointer/count pairs for `RuntimePredicateNode` and its edge table. Generated
code calls `fz_runtime_predicate_program_matches(process, value, program)`.

The compiled module owns the header and both read-only tables for every call
site that may name the header. JIT host ownership and AOT `.rodata` ownership
are both valid implementations of that rule. The runtime borrows the view for
one call; it neither copies it into `Process` nor registers it as a GC root.
The program has no moving heap references, so Cheney tracing has nothing to
update. `RuntimePredicateProgram` supplies the same contract for host-created
programs through shared immutable ownership; cloning it retains its tables.

## Evaluation

Evaluation constructs the finite product of program node and encountered value,
then solves its boolean equations from `false` upward using an explicit
worklist. `AnyOf` and `AllOf` produce disjunction and conjunction equations;
list and tuple nodes project children before adding their equations. This is
the least fixed point: an unproductive `V = V` cycle is false, while a cycle
with a finite base case can succeed. There is no recursion-depth budget and no
"active node means success" shortcut.

Runtime values remain finite immutable DAGs. Predicate programs may be cyclic,
which is how they represent regular infinite trees without reconstructing them
at each type revision.
