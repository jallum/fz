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
//
// fz_map_next_batch is the target for one batch of an iterator's walk: from entry x1 on, up to 32 entries
// as {key, value, next} tuples, each tuple's next the tuple after it, the last one's the continuation or
// none.
//   triple       = struct header | key word | value word | next word | key kind, value kind, next kind, 5 zero bytes
//                  | 8 zero bytes                                                                  (48 bytes)
//   continuation = a cell holding the index of the first entry the batch leaves, linked to a terminator cell
//                  that holds the map                                                              (32 bytes)
// The descent reads one header per node it passes: a node wholly before the start is skipped by its total,
// and the entries of the node the start falls in are skipped by index, so the first entry costs the depth
// of the trie and each entry after it one step.
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
        .globl _fz_map_next_batch
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

// (map x0, index x1 < the map's entries, bump x2 = {top, end}, triple header x3, atom id of none x4). Returns the
// first tuple's word in x0, or 0 when the bump has no room.
        .p2align 2
_fz_map_next_batch:
        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        sub     sp, sp, #16
        mov     x23, sp                 // a stand-in for the previous tuple: its next word receives the first tuple
        sub     x8, sp, #24
        mov     x24, x0                 // the map
        ldr     x12, [x0]
        lsr     x21, x12, #4            // the map's entries
        tbz     x12, #62, 1f
        ubfx    x21, x12, #36, #25
1:      add     x22, x1, #32            // the index of the first entry the batch leaves
        cmp     x22, x21
        csel    x22, x22, x21, lo
        sub     x9, x22, x1             // entries still to place
        ldp     x10, x11, [x2]          // bump top, end
        str     xzr, [sp, #-16]!        // the bottom of the node stack
bnode:
        ldr     x12, [x0]
        add     x14, x0, #8             // kind bytes
        mov     x19, #0                 // children
        tbnz    x12, #62, btrie
        lsr     x13, x12, #4            // a flat map's count
        mov     x5, x13
        b       bskip
btrie:
        ubfx    x13, x12, #36, #25      // a collision node's count
        mov     x5, x13                 // the node's total
        tbnz    x12, #61, bskip
        lsl     x16, x12, #44
        popcount w13, x16               // the node's entries
        ubfx    x16, x12, #20, #16
        popcount w19, x16               // its children
        ubfx    x5, x12, #36, #25
bskip:
        cmp     x1, x5
        b.lo    bentries
        sub     x1, x1, x5              // the node is wholly before the start
        b       bnext
bentries:
        add     x15, x13, #7
        and     x15, x15, #-8
        add     x15, x14, x15           // keys
        lsl     x16, x13, #3            // from a key to its value
        add     x20, x15, x16, lsl #1   // the first child word
        cmp     x1, x13
        csel    x5, x1, x13, lo         // own entries before the start
        sub     x1, x1, x5
        sub     x13, x13, x5
        add     x14, x14, x5
        add     x15, x15, x5, lsl #3
        cbz     x13, bchildren
btriple:
        ldr     x5, [x15, x16]          // the value's word
        ldr     x6, [x15], #8           // the key's word
        ldrb    w12, [x14], #1
        add     x7, x10, #48
        cmp     x7, x11
        b.hi    bfull
        str     x3, [x10]               // the tuple: its header,
        stp     x6, x5, [x10, #8]       // the key and the value,
        ubfx    w17, w12, #4, #4
        bfi     w17, w12, #8, #4
        orr     w17, w17, #0x30000      // their kinds and the kind of next, a tuple
        str     x17, [x10, #32]
        str     xzr, [x10, #40]
        str     x10, [x8, #24]          // linked from the tuple before it
        mov     x8, x10
        mov     x10, x7
        subs    x9, x9, #1
        b.eq    bdone
        subs    x13, x13, #1
        b.ne    btriple
bchildren:
        cbz     x19, bnext
        sub     x19, x19, #1
        ldr     x12, [x20, x19, lsl #3]
        str     x12, [sp, #-16]!
        b       bchildren
bnext:
        ldr     x0, [sp], #16
        cbnz    x0, bnode
bdone:
        cmp     x22, x21
        b.hs    bnone
        add     x7, x10, #32            // the continuation: a terminator cell holding the map, and its cell
        cmp     x7, x11
        b.hi    bfull
        str     x24, [x10]
        movz    x12, #0x0200, lsl #48   // MAP << 56
        str     x12, [x10, #8]
        add     x17, x10, #16
        str     x22, [x17]
        movz    x12, #0x0d00, lsl #48   // INT << 56
        orr     x12, x12, x10
        orr     x12, x12, #0x8000000000000000
        str     x12, [x17, #8]
        mov     x10, x7
        mov     w12, #1                 // LIST
        b       bend
bnone:
        mov     x17, x4
        mov     w12, #0xf               // ATOM
bend:
        str     x17, [x8, #24]          // the last tuple's next
        strb    w12, [x8, #34]
        str     x10, [x2]
        ldr     x0, [x23]
        movz    x12, #0x0300, lsl #48   // STRUCT << 56
        orr     x0, x0, x12
        mov     sp, x23
        add     sp, sp, #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16
        ret
bfull:
        mov     sp, x23
        add     sp, sp, #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16
        mov     x0, #0
        ret
