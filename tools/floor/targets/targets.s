// Hand-written arm64 targets for binary operations: the code the compiler should emit.
// Each routine is the whole loop of the matching program in ../programs, so its slope
// compares directly with the measured table. Nothing here calls anything.
//
// A binary value is a word: kind in the top byte (5 = bytes inline, 6 = view), address below.
//   inline: [bit_len << 4] [bytes ...]
//   view:   [bit_len << 4] [first byte address] [BinRef]      <- PROPOSED: length first.
//           today a view is [BinRef] [first byte address] [bit_len]; see t_byte_size_today.
// With the length first, the length of any binary is one load with no test of its shape.
//
// Arguments: x0 = n, x1 = process {hp, hlimit, reductions:u32, pad, arena}, x2 = a, x3 = b.
// x4 = running sum, returned in x0. "8:" is the slow path (overflow, bad match, collection,
// shared-buffer result): one branch never taken in these loops; the harness traps there,
// except heap exhaustion, where it resets hp to stand in for a collection.

.set VIEW_BIT, 57
.set ADDR, 0x00ffffffffffffff

.macro HEAD
    mov x4, #0
1:  cbz x0, 9f              // loop(0, ..) clause
    subs x0, x0, #1         // n - 1
    b.vs 8f                 //   integer overflow raises
.endm
.macro TAIL                 // x5 = amount added to the sum
    adds x4, x4, x5
    b.vs 8f
    ldr w6, [x1, #16]       // reductions: a self-call is a yield point
    subs w6, w6, #1
    str w6, [x1, #16]
    b.gt 1b
    mov w6, #4000           //   stand-in for the yield
    str w6, [x1, #16]
    b 1b
9:  mov x0, x4
    ret
8:  brk #1
.endm
.macro ALLOC                // $0 = bytes; x7 = new object; x16, x17 scratch
    ldp x7, x17, [x1]       // hp, hlimit
    add x16, x7, #$0
    cmp x16, x17
    b.hi 7f                 //   collection
    str x16, [x1]
.endm
.macro GC_STANDIN
7:  ldr x7, [x1, #24]
    str x7, [x1]
    add x0, x0, #1          // re-run this step
    b 1b
.endm

.text
.p2align 4

// ---- 00: the loop alone -------------------------------------------------------------
.globl _t_empty
_t_empty:
    HEAD
    mov x5, #1
    TAIL

// ---- 02: byte_size(b), b known to be a binary -----------------------------------------
.globl _t_byte_size
_t_byte_size:
    HEAD
    and x8, x2, #ADDR       // address
    ldr x9, [x8]            // bit_len << 4, same word for both shapes
    lsr x5, x9, #7          // bytes
    TAIL

// today's view layout: the shape must be tested, so 7 instructions, not 3
.globl _t_byte_size_today
_t_byte_size_today:
    HEAD
    and x8, x2, #ADDR
    ldr x9, [x8]            // inline: bit_len << 4
    ldr x10, [x8, #16]      // view: bit_len
    lsr x9, x9, #4
    tst x2, #(1 << VIEW_BIT)
    csel x9, x10, x9, ne
    lsr x5, x9, #3
    TAIL

// ---- 07: a == b, both known to be binaries ---------------------------------------------
// identity, then length, then bytes eight at a time with an overlapping last word.
.globl _t_eq
_t_eq:
    HEAD
    mov x5, #1
    cmp x2, x3              // same object: equal without reading it
    b.eq 5f
    and x8, x2, #ADDR
    and x9, x3, #ADDR
    ldr x10, [x8]
    ldr x11, [x9]
    cmp x10, x11            // lengths differ: unequal without reading bytes
    b.ne 4f
    add x12, x8, #8         // first byte: inline follows the header,
    ldr x13, [x8, #8]       //   a view holds its address
    tst x2, #(1 << VIEW_BIT)
    csel x8, x13, x12, ne
    add x12, x9, #8
    ldr x13, [x9, #8]
    tst x3, #(1 << VIEW_BIT)
    csel x9, x13, x12, ne
    lsr x10, x10, #7        // bytes
    cmp x10, #8
    b.lo 3f
2:  ldr x12, [x8], #8
    ldr x13, [x9], #8
    cmp x12, x13
    b.ne 4f
    sub x10, x10, #8
    cmp x10, #8
    b.hs 2b
    cbz x10, 5f
    add x8, x8, x10         // last 1..7 bytes: the word that ends at the end
    add x9, x9, x10
    ldur x12, [x8, #-8]
    ldur x13, [x9, #-8]
    cmp x12, x13
    b.ne 4f
    b 5f
3:  tbz x10, #2, 31f        // fewer than 8 bytes: 4, 2, 1
    ldr w12, [x8], #4
    ldr w13, [x9], #4
    cmp w12, w13
    b.ne 4f
31: tbz x10, #1, 32f
    ldrh w12, [x8], #2
    ldrh w13, [x9], #2
    cmp w12, w13
    b.ne 4f
32: tbz x10, #0, 5f
    ldrb w12, [x8]
    ldrb w13, [x9]
    cmp w12, w13
    b.eq 5f
4:  mov x5, #0
5:
    TAIL

// ---- 06b: <<rem(n, 256)>> -----------------------------------------------------------------
// size is static (8 bits): one 16-byte object, header and payload stored as a pair.
.globl _t_ctor_byte
_t_ctor_byte:
    HEAD
    mov x10, #256
    sdiv x11, x0, x10       // rem(n, 256)
    msub x11, x11, x10, x0
    ALLOC 16
    and x11, x11, #0xff     // the ::8 field truncates
    mov x12, #(8 << 4)
    stp x12, x11, [x7]      // header, byte (rest of the word zero)
    mov x13, x7
    movk x13, #0x0500, lsl #48  // kind 5 is not one logical immediate: two instructions
    mov x5, #1              // byte_size(r) is the static size
    TAIL
    GC_STANDIN

// ---- 06a: <<rem(n, 256)::8, n::16, c::binary>> -----------------------------------------------
// size = 3 + byte_size(c), computed once; one allocation; adjacent integer fields merged
// into one store; c copied a word at a time.
.globl _t_ctor_segments
_t_ctor_segments:
    HEAD
    mov x10, #256
    sdiv x11, x0, x10
    msub x11, x11, x10, x0
    and x8, x3, #ADDR       // c
    ldr x9, [x8]
    tst x9, #0x70           // c::binary must be whole bytes
    b.ne 8f
    lsr x9, x9, #7          // bytes of c
    add x14, x9, #3         // result bytes
    cmp x14, #64
    b.hi 8f                 //   larger results go to a shared buffer (not this loop)
    add x15, x14, #15       // object bytes: header + bytes, rounded to 16
    and x15, x15, #-16
    add x15, x15, #16
    ldp x7, x17, [x1]
    add x16, x7, x15
    cmp x16, x17
    b.hi 7f
    str x16, [x1]
    lsl x12, x14, #7
    str x12, [x7]           // header
    and x11, x11, #0xff     // a::8
    rev16 w12, w0           // n::16 big-endian
    and x12, x12, #0xffff
    orr x11, x11, x12, lsl #8
    str w11, [x7, #8]       // both integer fields in one store
    add x12, x8, #8         // first byte of c
    ldr x13, [x8, #8]
    tst x3, #(1 << VIEW_BIT)
    csel x12, x13, x12, ne
    add x13, x7, #11        // destination
    cmp x9, #8
    b.lo 3f
2:  ldr x15, [x12], #8
    str x15, [x13], #8
    sub x9, x9, #8
    cmp x9, #8
    b.hs 2b
    cbz x9, 5f
    add x12, x12, x9
    add x13, x13, x9
    ldur x15, [x12, #-8]
    stur x15, [x13, #-8]
    b 5f
3:  tbz x9, #2, 31f
    ldr w15, [x12], #4
    str w15, [x13], #4
31: tbz x9, #1, 32f
    ldrh w15, [x12], #2
    strh w15, [x13], #2
32: tbz x9, #0, 5f
    ldrb w15, [x12]
    strb w15, [x13]
5:  mov x13, x7
    movk x13, #0x0500, lsl #48  // kind 5 is not one logical immediate: two instructions
    mov x5, x14             // byte_size(r) is the size already computed
    TAIL
    GC_STANDIN

// ---- 08a: <<_::binary-size(3), part::binary-size(4), _::binary>> = b ---------------------------
// one length check for the whole pattern; a 4-byte slice is one load and one object.
.globl _t_slice
_t_slice:
    HEAD
    and x8, x2, #ADDR
    ldr x9, [x8]
    cmp x9, #(7 << 7)       // at least 7 bytes
    b.lo 8f
    tst x9, #0x70           // trailing ::binary must be whole bytes
    b.ne 8f
    add x10, x8, #8
    ldr x11, [x8, #8]
    tst x2, #(1 << VIEW_BIT)
    csel x10, x11, x10, ne
    ldur w12, [x10, #3]     // the four bytes
    ALLOC 16
    mov x13, #(32 << 4)
    stp x13, x12, [x7]
    mov x14, x7
    movk x14, #0x0500, lsl #48  // kind 5 is not one logical immediate: two instructions
    mov x5, #4              // byte_size(part) is static
    TAIL
    GC_STANDIN

// ---- 03c / 05b: acc = acc <> "ab", acc the growing result -----------------------------------------
// acc is a view that ends where its buffer's written bytes end, and the buffer has room:
// write the two bytes there and make a view two bytes longer. x2 carries acc.
// BinRef: [SharedBin]. SharedBin: [refcount][bytes][bytes_len][destructor][room].
.globl _t_append
_t_append:
    HEAD
    tbz x2, #VIEW_BIT, 8f   // an inline acc grows into a buffer (slow path, once)
    and x8, x2, #ADDR
    ldr x9, [x8]            // bit_len << 4
    ldp x10, x11, [x8, #8]  // first byte, BinRef
    and x12, x11, #ADDR
    ldr x12, [x12]          // SharedBin
    ldp x13, x14, [x12, #8] // bytes, bytes_len
    ldr x15, [x12, #32]     // room; a frozen buffer has the sign bit set
    add x16, x10, x9, lsr #7
    add x17, x13, x14
    cmp x16, x17            // acc ends where the written bytes end
    b.ne 8f
    add x14, x14, #2
    cmp x14, x15            // room for two more (signed: frozen fails)
    b.gt 8f
    mov x15, x16            // (ALLOC uses x16, x17)
    ALLOC 32                // before any write: a collection here re-runs the step
    mov w13, #0x6261        // "ab"
    strh w13, [x15]
    strb wzr, [x15, #2]     // the byte after the bytes stays NUL
    str x14, [x12, #16]
    add x9, x9, #(2 << 7)
    stp x9, x10, [x7]
    str x11, [x7, #16]
    orr x2, x7, #(6 << 56)
    mov x5, #0
    TAIL
    GC_STANDIN

// ---- 09a: byte_size(id(b)) ------------------------------------------------------------------------
// a binary is one word in one register; a call that cannot suspend is bl and ret.
_id: ret
.globl _t_through_call
_t_through_call:
    stp x29, x30, [sp, #-16]!
    mov x4, #0
1:  cbz x0, 9f
    subs x0, x0, #1
    b.vs 8f
    mov x19, x0             // (callee-saved homes are free in real code: live values already sit there)
    mov x0, x2
    bl _id
    and x8, x0, #ADDR
    ldr x9, [x8]
    lsr x5, x9, #7
    mov x0, x19
    adds x4, x4, x5
    b.vs 8f
    ldr w6, [x1, #16]
    subs w6, w6, #1
    str w6, [x1, #16]
    b.gt 1b
    mov w6, #4000
    str w6, [x1, #16]
    b 1b
9:  mov x0, x4
    ldp x29, x30, [sp], #16
    ret
8:  brk #1

// ---- 07, second form: the length word carries a "one holder" mark in bit 60 ---------------------
// (fz-nml.29's proposal), and bytes are compared sixteen at a time.
// The mark costs one instruction: lengths are compared as eor + tst under a mask.
.set LEN_MASK, 0x0fffffffffffffff
.globl _t_eq_wide
_t_eq_wide:
    HEAD
    mov x5, #1
    cmp x2, x3
    b.eq 5f
    and x8, x2, #ADDR
    and x9, x3, #ADDR
    ldr x10, [x8]
    ldr x11, [x9]
    eor x12, x10, x11
    tst x12, #LEN_MASK      // lengths differ (mark ignored)
    b.ne 4f
    add x12, x8, #8
    ldr x13, [x8, #8]
    tst x2, #(1 << VIEW_BIT)
    csel x8, x13, x12, ne
    add x12, x9, #8
    ldr x13, [x9, #8]
    tst x3, #(1 << VIEW_BIT)
    csel x9, x13, x12, ne
    ubfx x10, x10, #7, #53  // bytes, below the mark
    cmp x10, #16
    b.lo 3f
2:  ldp x12, x13, [x8], #16
    ldp x14, x15, [x9], #16
    cmp x12, x14
    ccmp x13, x15, #0, eq
    b.ne 4f
    sub x10, x10, #16
    cmp x10, #16
    b.hs 2b
    cbz x10, 5f
    add x8, x8, x10         // last 1..15 bytes: the sixteen that end at the end
    add x9, x9, x10
    ldp x12, x13, [x8, #-16]
    ldp x14, x15, [x9, #-16]
    cmp x12, x14
    ccmp x13, x15, #0, eq
    b.ne 4f
    b 5f
3:  tbz x10, #3, 30f        // 8..15 bytes: two words that overlap
    ldr x12, [x8]
    ldr x13, [x9]
    cmp x12, x13
    b.ne 4f
    add x8, x8, x10
    add x9, x9, x10
    ldur x12, [x8, #-8]
    ldur x13, [x9, #-8]
    cmp x12, x13
    b.ne 4f
    b 5f
30: tbz x10, #2, 31f
    ldr w12, [x8], #4
    ldr w13, [x9], #4
    cmp w12, w13
    b.ne 4f
31: tbz x10, #1, 32f
    ldrh w12, [x8], #2
    ldrh w13, [x9], #2
    cmp w12, w13
    b.ne 4f
32: tbz x10, #0, 5f
    ldrb w12, [x8]
    ldrb w13, [x9]
    cmp w12, w13
    b.eq 5f
4:  mov x5, #0
5:
    TAIL

// ---- 11a: "#{a}-#{b}" of two binaries ---------------------------------------------------------------
// one build of three pieces: size summed once, one allocation, each piece written in place.
.macro COPY                 // x12 = source, x13 = destination, x9 = bytes; x15 scratch
    cmp x9, #8
    b.lo 22f
21: ldr x15, [x12], #8
    str x15, [x13], #8
    sub x9, x9, #8
    cmp x9, #8
    b.hs 21b
    cbz x9, 25f
    add x12, x12, x9
    add x13, x13, x9
    ldur x15, [x12, #-8]
    stur x15, [x13, #-8]
    b 25f
22: tbz x9, #2, 23f
    ldr w15, [x12], #4
    str w15, [x13], #4
23: tbz x9, #1, 24f
    ldrh w15, [x12], #2
    strh w15, [x13], #2
24: tbz x9, #0, 25f
    ldrb w15, [x12], #1
    strb w15, [x13], #1
25:
.endm
.globl _t_interp
_t_interp:
    HEAD
    and x8, x2, #ADDR       // a
    and x10, x3, #ADDR      // b
    ldr x9, [x8]
    ldr x11, [x10]
    orr x12, x9, x11
    tst x12, #0x70          // both whole bytes
    b.ne 8f
    lsr x9, x9, #7
    lsr x11, x11, #7
    add x14, x9, x11
    add x14, x14, #1        // result bytes
    cmp x14, #64
    b.hi 8f
    add x15, x14, #15
    and x15, x15, #-16
    add x15, x15, #16
    ldp x7, x17, [x1]
    add x16, x7, x15
    cmp x16, x17
    b.hi 7f
    str x16, [x1]
    lsl x12, x14, #7
    str x12, [x7]
    add x12, x8, #8         // first byte of a
    ldr x13, [x8, #8]
    tst x2, #(1 << VIEW_BIT)
    csel x12, x13, x12, ne
    add x13, x7, #8
    mov x6, x9
    COPY
    add x13, x7, #8
    add x13, x13, x6        // after a (COPY's overlapping tail does not leave x13 there for 8+)
    mov w15, #'-'
    strb w15, [x13], #1
    add x12, x10, #8        // first byte of b
    ldr x15, [x10, #8]
    tst x3, #(1 << VIEW_BIT)
    csel x12, x15, x12, ne
    mov x9, x11
    COPY
    mov x13, x7
    movk x13, #0x0500, lsl #48
    mov x5, x14
    TAIL
    GC_STANDIN

// ---- 01a: eat(<<>>) / eat(<<_c, rest::binary>>), a self tail call per byte ----------------------
// b is known to be a binary, so its length is whole bytes and a cursor that is not at the end
// has a byte. The cursor is two registers: the next byte and one past the last. x0 counts
// calls of eat, each over the whole of b.
.globl _t_match_tail
_t_match_tail:
    HEAD
    and x8, x2, #ADDR
    ldr x9, [x8]            // bit_len << 4
    ldr x10, [x8, #8]       // view: first byte address
    add x11, x8, #8         // inline: the bytes follow the length
    tst x2, #(1 << VIEW_BIT)
    csel x10, x10, x11, ne
    add x9, x10, x9, lsr #7 // one past the last byte
2:  cmp x10, x9             // eat(<<>>)
    b.eq 3f
    add x10, x10, #1        // <<_c, rest::binary>>: the byte is not read
    ldr w6, [x1, #16]       // reductions: the self tail call is a yield point
    subs w6, w6, #1
    str w6, [x1, #16]
    b.gt 2b
    mov w6, #4000
    str w6, [x1, #16]
    b 2b
3:  mov x5, #0
    TAIL

// ---- 03a / 04a / 05a: r = a <> b, a result nothing else holds --------------------------------------
// one build of two pieces: size summed once, one allocation, each piece written in place.
// The same code serves <<a::binary, b::binary>>: the two spell one construction.
.globl _t_concat
_t_concat:
    HEAD
    and x8, x2, #ADDR       // a
    and x10, x3, #ADDR      // b
    ldr x9, [x8]
    ldr x11, [x10]
    orr x12, x9, x11
    tst x12, #0x70          // both whole bytes
    b.ne 8f
    add x14, x9, x11        // the result's length word is the sum of the operands'
    lsr x9, x9, #7
    lsr x11, x11, #7
    add x6, x9, x11         // result bytes
    cmp x6, #64
    b.hi 8f                 //   larger results go to a shared buffer (not this loop)
    add x15, x6, #15        // object bytes: header + bytes, rounded to 16
    and x15, x15, #-16
    add x15, x15, #16
    ldp x7, x17, [x1]
    add x16, x7, x15
    cmp x16, x17
    b.hi 7f
    str x16, [x1]
    str x14, [x7]           // header
    add x12, x8, #8         // first byte of a
    ldr x13, [x8, #8]
    tst x2, #(1 << VIEW_BIT)
    csel x12, x13, x12, ne
    add x13, x7, #8
    add x14, x13, x9        // where b goes
    COPY
    mov x13, x14
    add x12, x10, #8        // first byte of b
    ldr x15, [x10, #8]
    tst x3, #(1 << VIEW_BIT)
    csel x12, x15, x12, ne
    mov x9, x11
    COPY
    mov x13, x7
    movk x13, #0x0500, lsl #48
    mov x5, x6              // byte_size(r) is the size already computed
    TAIL
    GC_STANDIN

// ---- 01b: sum(<<>>) / sum(<<c, rest::binary>>) = c + sum(rest), not a tail call -------------------
// Going in, each call keeps one word, its byte, and the cursor moves on; coming back, each
// return adds its byte. The cursor is two registers, as in 01a. x0 counts calls of sum over
// the whole of b.
.globl _t_match_sum
_t_match_sum:
    HEAD
    and x8, x2, #ADDR
    ldr x9, [x8]            // bit_len << 4
    ldr x10, [x8, #8]       // view: first byte address
    add x11, x8, #8         // inline: the bytes follow the length
    tst x2, #(1 << VIEW_BIT)
    csel x10, x10, x11, ne
    add x9, x10, x9, lsr #7 // one past the last byte
    mov x12, sp             // where the frames end
2:  cmp x10, x9             // sum(<<>>)
    b.eq 3f
    ldrb w13, [x10], #1     // <<c, rest::binary>>
    str x13, [sp, #-16]!    // the frame of this call: c
    ldr w6, [x1, #16]       // reductions: the call is a yield point
    subs w6, w6, #1
    str w6, [x1, #16]
    b.gt 2b
    mov w6, #4000
    str w6, [x1, #16]
    b 2b
3:  mov x5, #0              // sum(<<>>) is 0
4:  cmp sp, x12
    b.eq 5f
    ldr x13, [sp], #16      // return into the frame: c + the result
    adds x5, x5, x13
    b.vs 8f
    b 4b
5:
    TAIL

// ---- 10a: send(self(), b), then receive x -> byte_size(x) -----------------------------------------
// The sender is the receiver, so the message is the word b itself: one 16-byte mailbox cell
// {next, value} linked at the tail, and the receive unlinks the head. An arm that takes any
// message has nothing to test. Process: +32 mailbox head, +40 mailbox tail.
.globl _t_send_self
_t_send_self:
    HEAD
    ALLOC 16
    stp xzr, x2, [x7]       // cell: no next, the message
    ldr x8, [x1, #40]       // tail
    add x9, x1, #32         //   an empty mailbox's tail is the head field itself
    cmp x8, #0
    csel x8, x8, x9, ne
    str x7, [x8]            // link
    str x7, [x1, #40]
    ldr x10, [x1, #32]      // receive: the head
    cbz x10, 8f             //   an empty mailbox parks the process (not this loop)
    ldp x11, x12, [x10]     // next, message
    str x11, [x1, #32]
    cmp x11, #0
    csel x13, xzr, x8, eq   //   the last cell leaves the mailbox empty
    str x13, [x1, #40]
    and x12, x12, #ADDR     // byte_size(x): x is a binary because b is
    ldr x5, [x12]
    lsr x5, x5, #7
    TAIL
    GC_STANDIN
