---
purpose: "source-order item macro returns Fz-shaped function source"
paths: [jit, interp, fz2-run, fz2-interp, fz2-build]
kind: run
---

# item_macro_source

Defines an item macro that returns a quoted function definition as Fz-shaped
data. Source production expands the item macro, applies the returned source
fragment, and later code calls the generated function.
