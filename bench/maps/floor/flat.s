// Hand-written arm64 targets for flat-map operations, against the runtime's layout:
//
//   header = count << 4 | kind bytes (1 per entry, padded to 8) | key words | value words
//   kind byte = key kind << 4 | value kind
//
// Entries are stored in term order. A key that is one word is found by word equality;
// the order is consulted only to place a key that is absent.
        .text

// fz_flat_scan(map x0, key word x1, key kind x2) -> x0 = slot, or -1 when absent
        .globl _fz_flat_scan
        .p2align 2
_fz_flat_scan:
        ldr     x8, [x0]
        lsr     x8, x8, #4              // count
        add     x9, x0, #8              // kind bytes
        add     x10, x8, #7
        and     x10, x10, #-8
        add     x10, x9, x10            // keys
        mov     x11, #0
        cbz     x8, 9f
1:      ldr     x12, [x10, x11, lsl #3]
        cmp     x12, x1
        b.eq    3f
2:      add     x11, x11, #1
        cmp     x11, x8
        b.lo    1b
9:      mov     x0, #-1
        ret
3:      ldrb    w13, [x9, x11]          // same word: is it the same kind?
        lsr     w13, w13, #4
        cmp     w13, w2
        b.ne    2b
        mov     x0, x11
        ret

// fz_flat_place(map x0, key kind x1, key order word x2, atom prefixes x3) -> x0 = slot for an absent key,
// or -1 when the order word does not decide (two atoms sharing a prefix, an integer beside a float).
// The order word of an atom is the first eight bytes of its name, big-endian; of an integer, its word
// with the sign bit flipped.
        .globl _fz_flat_place
        .p2align 2
_fz_flat_place:
        ldr     x8, [x0]
        lsr     x8, x8, #4              // high
        add     x9, x0, #8
        add     x10, x8, #7
        and     x10, x10, #-8
        add     x10, x9, x10            // keys
        mov     x11, #0                 // low
        adrp    x15, kind_rank@PAGE
        add     x15, x15, kind_rank@PAGEOFF
        ldrb    w16, [x15, x1]          // the key's rank in term order
        cmp     x11, x8
        b.hs    6f
1:      add     x12, x11, x8
        lsr     x12, x12, #1            // middle
        ldrb    w13, [x9, x12]
        lsr     w13, w13, #4
        cmp     w13, w1
        b.ne    4f
        ldr     x14, [x10, x12, lsl #3]
        cmp     w13, #0xF
        b.ne    2f
        ldr     x14, [x3, x14, lsl #3]  // an atom orders by its name prefix
        b       3f
2:      eor     x14, x14, #0x8000000000000000
3:      cmp     x14, x2
        b.eq    8f
5:      csinc   x11, x11, x12, hs       // entry below the key: low = middle + 1
        csel    x8, x12, x8, hs         // entry above the key: high = middle
        cmp     x11, x8
        b.lo    1b
6:      mov     x0, x11
        ret
4:      ldrb    w13, [x15, x13]         // different kinds: their ranks decide
        cmp     w13, w16
        b.ne    5b
8:      mov     x0, #-1
        ret

// fz_flat_find(map x0, key kind x1, key order word x2, atom prefixes x3, key word x4) -> x0 = slot,
// x1 = 1 found / 0 absent; x0 = -1 when the order word does not decide (two atoms sharing a prefix,
// an integer beside a float).
        .globl _fz_flat_find
        .p2align 2
_fz_flat_find:
        ldr     x8, [x0]
        lsr     x8, x8, #4              // high
        add     x9, x0, #8
        add     x10, x8, #7
        and     x10, x10, #-8
        add     x10, x9, x10            // keys
        mov     x11, #0                 // low
        adrp    x15, kind_rank@PAGE
        add     x15, x15, kind_rank@PAGEOFF
        ldrb    w16, [x15, x1]          // the key's rank in term order
        cmp     x11, x8
        b.hs    6f
1:      add     x12, x11, x8
        lsr     x12, x12, #1            // middle
        ldrb    w13, [x9, x12]
        lsr     w13, w13, #4
        cmp     w13, w1
        b.ne    4f
        ldr     x17, [x10, x12, lsl #3]
        cmp     x17, x4                 // the same word of the same kind is the key
        b.eq    7f
        cmp     w13, #0xF
        b.ne    2f
        ldr     x14, [x3, x17, lsl #3]  // an atom orders by its name prefix
        b       3f
2:      eor     x14, x17, #0x8000000000000000
3:      cmp     x14, x2
        b.eq    8f
5:      csinc   x11, x11, x12, hs       // entry below the key: low = middle + 1
        csel    x8, x12, x8, hs         // entry above the key: high = middle
        cmp     x11, x8
        b.lo    1b
6:      mov     x0, x11
        mov     x1, #0
        ret
7:      mov     x0, x12
        mov     x1, #1
        ret
4:      ldrb    w13, [x15, x13]         // different kinds: their ranks decide
        cmp     w13, w16
        b.ne    5b
8:      mov     x0, #-1
        mov     x1, #0
        ret

// fz_flat_find_bin(map x0, key x1 -> {bit length, bytes}) -> x0 = slot, x1 = 1 found / 0 absent;
// x0 = -1 for a key or an entry that is a view or not whole bytes.
        .globl _fz_flat_find_bin
        .p2align 2
_fz_flat_find_bin:
        stp     x29, x30, [sp, #-80]!
        mov     x29, sp
        stp     x19, x20, [sp, #16]
        stp     x21, x22, [sp, #32]
        stp     x23, x24, [sp, #48]
        stp     x25, x26, [sp, #64]
        ldr     x19, [x0]
        lsr     x19, x19, #4            // high
        add     x20, x0, #8             // kind bytes
        add     x21, x19, #7
        and     x21, x21, #-8
        add     x21, x20, x21           // keys
        mov     x22, #0                 // low
        mov     x23, x1
        ldr     x24, [x1]
        tst     x24, #7
        b.ne    8f
        lsr     x24, x24, #3            // key byte length
        cmp     x22, x19
        b.hs    6f
1:      add     x25, x22, x19
        lsr     x25, x25, #1            // middle
        ldrb    w8, [x20, x25]
        lsr     w8, w8, #4
        cmp     w8, #5
        b.ne    5f
        ldr     x9, [x21, x25, lsl #3]
        cmp     x9, x23                 // the same object is the same key
        b.eq    7f
        ldr     x26, [x9]
        tst     x26, #7
        b.ne    8f
        lsr     x26, x26, #3            // entry byte length
        add     x0, x9, #8
        add     x1, x23, #8
        cmp     x26, x24
        csel    x2, x26, x24, lo
        bl      _memcmp
        cmp     w0, #0
        b.lt    3f
        b.gt    2f
        cmp     x26, x24                // equal prefix: the shorter is first
        b.eq    7f
        b.lo    3f
2:      mov     x19, x25                // entry above the key
        b       4f
3:      add     x22, x25, #1            // entry below the key
4:      cmp     x22, x19
        b.lo    1b
6:      mov     x0, x22
        mov     x1, #0
        b       9f
7:      mov     x0, x25
        mov     x1, #1
        b       9f
5:      cmp     w8, #6
        b.ne    3b                      // every other kind is below a binary
8:      mov     x0, #-1
        mov     x1, #0
9:      ldp     x25, x26, [sp, #64]
        ldp     x23, x24, [sp, #48]
        ldp     x21, x22, [sp, #32]
        ldp     x19, x20, [sp, #16]
        ldp     x29, x30, [sp], #80
        ret

// fz_flat_write(bump x0 -> {top, end}, map x1, slot x2, action x3, key word x4, key kind x5,
//               value word x6, value kind x7) -> x0 = new map, or 0 for the slow path
// action 0 inserts the entry at the slot, 1 replaces the entry there, 2 leaves that entry out.
        .globl _fz_flat_write
        .p2align 2
_fz_flat_write:
        ldr     x8, [x1]
        lsr     x8, x8, #4              // count
        add     x9, x1, #8              // source kind bytes
        add     x10, x8, #7
        and     x10, x10, #-8
        add     x10, x9, x10            // source keys
        add     x11, x10, x8, lsl #3    // source values
        add     x12, x8, #1
        sub     x12, x12, x3            // new count
        cmp     x12, #32
        b.hi    9f                      // grows into a trie
        add     x13, x12, #7
        and     x13, x13, #-8           // new kind bytes length
        add     x14, x13, x12, lsl #4
        add     x14, x14, #23
        and     x14, x14, #-16          // object size
        ldp     x15, x16, [x0]          // bump top, end
        add     x17, x15, x14
        cmp     x17, x16
        b.hi    9f
        str     x17, [x0]
        lsl     x17, x12, #4
        str     x17, [x15]              // header
        add     x16, x15, #8            // new kind bytes
        add     x17, x16, x13           // new keys
        add     x14, x17, x12, lsl #3   // new values
        cbz     x13, 1f
        stur    xzr, [x17, #-8]         // clear the padding in the last kind word
1:      orr     w5, w7, w5, lsl #4      // the entry's kind byte
        mov     x13, x2                 // entries before the slot
        cbz     x13, 3f
2:      ldrb    w0, [x9], #1
        strb    w0, [x16], #1
        ldr     x0, [x10], #8
        str     x0, [x17], #8
        ldr     x0, [x11], #8
        str     x0, [x14], #8
        subs    x13, x13, #1
        b.ne    2b
3:      cmp     x3, #2
        b.eq    4f
        strb    w5, [x16], #1
        str     x4, [x17], #8
        str     x6, [x14], #8
4:      sub     x13, x8, x2             // entries from the slot on
        cbz     x3, 5f
        sub     x13, x13, #1            // the entry at the slot is not carried over
        add     x9, x9, #1
        add     x10, x10, #8
        add     x11, x11, #8
5:      cbz     x13, 7f
6:      ldrb    w0, [x9], #1
        strb    w0, [x16], #1
        ldr     x0, [x10], #8
        str     x0, [x17], #8
        ldr     x0, [x11], #8
        str     x0, [x14], #8
        subs    x13, x13, #1
        b.ne    6b
7:      mov     x0, x15
        ret
9:      mov     x0, #0
        ret

        .section __TEXT,__const
// Term order of value kinds: number < atom < reference < resource < closure < pid < struct < map < list < binary.
kind_rank:
        .byte   15, 8, 7, 6, 4, 9, 9, 3, 15, 5, 2, 15, 15, 0, 0, 1
