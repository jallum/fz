---
purpose: "100k-deep self-recursion must TCO — exits cleanly with the accumulated count"
paths: [jit, interp, aot]
expect_clif_excludes:
  - fn: count_s2
    substr: ishl_imm
  - fn: count_s2
    substr: bor_imm
  - fn: count_s3
    substr: ishl_imm
  - fn: count_s3
    substr: bor_imm
  - fn: k_2_s4
    substr: sshr_imm
---

# tail_recursion

100k-deep self-recursion must TCO — exits cleanly with the accumulated count
