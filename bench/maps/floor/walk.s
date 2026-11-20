// Hand-written arm64 targets for turning a map into a list in one pass: its keys, its values, or its
// {key, value} pairs, against the runtime's layouts.
//
//   map node  = header | kind bytes (1 per entry, padded to 8) | key words | value words | child words
//   flat map  : header = count << 4
//   trie node : header = TRIE(bit 62) | total << 36 | child map << 20 | data map << 4
//   collision : header = TRIE(bit 62) | COLLISION(bit 61) | count << 36
//   kind byte : the key's kind in the high nibble, the value's in the low
//   list cell = head word | tail address | head kind << 56                                (16 bytes)
//   pair      = struct header | key word | value word | key kind, value kind, 6 zero bytes (32 bytes)
//
// A node's own entries come before its children's, and its children come in the order of their bits:
// the order in which the runtime numbers entries. Nodes still to visit wait on the machine stack,
// pushed in reverse so the first child comes off first. Each cell is linked to the one before it as
// it is placed, so the list is built front to back and never reversed: x9 is the address of the
// previous cell's tail word and x8 the previous cell's head kind, already shifted to the top byte.
        .text

        .macro  popcount dst, src
        fmov    d0, \src
        cnt     v0.8b, v0.8b
        addv    b0, v0.8b
        fmov    \dst, s0
        .endm

// Each takes (map x0, bump x1 = {top, end}); pairs also takes the pair's struct header in x2. Each
// returns the list's word in x0, or 0 when the bump has no room.
        .globl _fz_map_keys
        .globl _fz_map_values
        .globl _fz_map_pairs
        .p2align 2
_fz_map_keys:
        mov     x4, #0
        b       walk
_fz_map_values:
        mov     x4, #1
        b       walk
_fz_map_pairs:
        mov     x4, #2
walk:
        stp     x19, x20, [sp, #-16]!
        sub     sp, sp, #16
        mov     x9, sp                  // a stand-in tail word: it receives the list's own word
        movz    x8, #0x0100, lsl #48    // LIST << 56
        ldp     x10, x11, [x1]          // bump top, end
        str     xzr, [sp, #-16]!        // the bottom of the node stack
node:
        ldr     x12, [x0]
        add     x14, x0, #8             // kind bytes
        mov     x19, #0                 // children
        tbnz    x12, #62, trie
        lsr     x13, x12, #4            // a flat map's count
        b       entries
trie:
        ubfx    x13, x12, #36, #25      // a collision node's count
        tbnz    x12, #61, entries
        lsl     x16, x12, #44
        popcount w13, x16               // the node's entries
        ubfx    x16, x12, #20, #16
        popcount w19, x16               // its children
entries:
        add     x15, x13, #7
        and     x15, x15, #-8
        add     x15, x14, x15           // keys
        lsl     x16, x13, #3            // from a key to its value
        add     x20, x15, x16, lsl #1   // the first child word
        cbz     x13, children
        cbz     x4, keys
        cmp     x4, #1
        b.eq    values

pairs:
        ldr     x3, [x15, x16]          // the value's word
        ldr     x5, [x15], #8           // the key's word
        ldrb    w6, [x14], #1
        add     x7, x10, #48
        cmp     x7, x11
        b.hi    full
        str     x2, [x10]               // the pair: its header,
        stp     x5, x3, [x10, #8]       // the key and the value,
        ubfx    w12, w6, #4, #4
        bfi     w12, w6, #8, #4
        str     x12, [x10, #24]         // and their kinds
        add     x17, x10, #32           // the cell
        str     x10, [x17]
        orr     x12, x17, x8
        str     x12, [x9]               // linked to the cell before it
        movz    x8, #0x0300, lsl #48    // STRUCT << 56
        add     x9, x17, #8
        mov     x10, x7
        subs    x13, x13, #1
        b.ne    pairs
        b       children

keys:
        ldr     x5, [x15], #8
        ldrb    w6, [x14], #1
        lsr     w6, w6, #4
        b       cell
values:
        ldr     x5, [x15, x16]
        add     x15, x15, #8
        ldrb    w6, [x14], #1
        and     w6, w6, #0xf
cell:
        add     x7, x10, #16
        cmp     x7, x11
        b.hi    full
        str     x5, [x10]               // the head's word
        orr     x12, x10, x8
        str     x12, [x9]               // linked to the cell before it
        lsl     x8, x6, #56
        add     x9, x10, #8
        mov     x10, x7
        subs    x13, x13, #1
        b.eq    children
        cbz     x4, keys
        b       values

children:
        cbz     x19, next
        sub     x19, x19, #1
        ldr     x12, [x20, x19, lsl #3]
        str     x12, [sp, #-16]!
        b       children
next:
        ldr     x0, [sp], #16
        cbnz    x0, node
        str     x8, [x9]                // the last cell's tail: the empty list
        str     x10, [x1]
        ldr     x0, [sp], #16           // the list's word, from the stand-in
        ldp     x19, x20, [sp], #16
        cmp     x0, x8                  // nothing was placed: the empty list
        mov     x12, #8
        csel    x0, x12, x0, eq
        ret
full:
        ldr     x12, [sp], #16
        cbnz    x12, full
        add     sp, sp, #16
        ldp     x19, x20, [sp], #16
        mov     x0, #0
        ret
