---
purpose: "demonstrate expect_clif_contains / expect_clif_excludes header keys (fz-ul4.27.1)"
paths: [jit, interp]
expect_clif_contains:
  - fn: add1
    substr: iadd
  - fn: add1
    substr: "; @1:"
expect_clif_excludes:
  - fn: add1
    substr: this_substring_never_appears_in_clif_xyzzy
---

# expect_clif_demo

demonstrate expect_clif_contains / expect_clif_excludes header keys (fz-ul4.27.1)
