---
purpose: "smallest JIT round-trip — fn def + call + print"
paths: [jit, interp]
expect_clif_excludes:
  - fn: add1_s2
    substr: ishl_imm
  - fn: add1_s2
    substr: bor_imm
  - fn: k_2_s3
    substr: sshr_imm
---

# add1

smallest JIT round-trip — fn def + call + print
