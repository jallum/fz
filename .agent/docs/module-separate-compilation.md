# Module identity and separate compilation

Use this when changing module resolution, interfaces, compiled units, or runtime
library import behavior.

`ModuleName`, `QualifiedName`, and `ExportKey` are the semantic identity types.
Dotted strings remain compatibility/display spellings for current flattened IR,
dumps, and diagnostics. New module-boundary code should assemble typed names
from parsed segments or interface data and render dotted text only at the edge.

The invariant for the separate-compilation arc is:

- private code is inferred inside a module;
- public boundaries are represented by typed interface/export facts;
- normal import resolution consumes interface facts, not dependency bodies;
- whole-program analysis may erase boundaries in LTO, but correctness cannot
  depend on doing so.
