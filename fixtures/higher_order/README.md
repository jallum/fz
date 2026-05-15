---
purpose: "higher-order patterns — apply2, compose"
paths: [jit, interp, aot]
expect_clif_contains:
  - fn: k_5_s12
    substr: "(RawInt, Tagged, Tagged, RawInt) -> RawInt"
expect_clif_excludes:
  - fn: k_5_s12
    substr: sshr_imm
---

# higher_order

higher-order patterns — apply2, compose
