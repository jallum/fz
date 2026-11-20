// Hand-written arm64 targets for finding a one-word key in a map past the flat limit: a hash array
// mapped trie of nodes, against the runtime's layout (runtime/src/any_value/map_node.rs):
//
//   trie node: TRIE(bit 62) | total << 36 | child map << 20 | data map << 4
//   collision: TRIE(bit 62) | COLLISION(bit 61) | count << 36
//   node     = header | kind bytes (1 per entry, padded to 8) | key words | value words | child words
//
// The hash takes four bits a level, the top four first. Slot `s` of a node holds an entry when bit s
// of the data map is set, a child when bit s of the child map is set, and nothing otherwise. A node's
// entries and children are stored in the order of their bits, so where one sits is the count of set
// bits below it. Every count is one shift of the header and a popcount, with no mask: the low nibble
// is clear, and the shift drops every field above the bits it counts.
//
// A child word is the child node's address. A collision node is the node of keys whose 64-bit hashes
// are all equal, so a search reaches one only for such a key; it is left to the runtime.
        .text

// The count of set bits of \src, into \dst. arm64 has no scalar popcount: the vector unit counts
// the bits of each byte and adds the eight counts.
        .macro  popcount dst, src
        fmov    d0, \src
        cnt     v0.8b, v0.8b
        addv    b0, v0.8b
        fmov    \dst, s0
        .endm

// fz_trie_get(root x0, hash x1, key word x2, key kind x3) -> x0 = value word, x1 = value kind;
// x1 = -1 when the key is absent, -2 when the search reaches a collision node.
        .globl _fz_trie_get
        .p2align 2
_fz_trie_get:
1:      ldr     x8, [x0]                // header
        tbnz    x8, #61, 8f             // a collision node: the runtime decides
        lsr     x9, x1, #60             // this level's slot
        lsl     x1, x1, #4              // the next level's slot to the top
        lsl     x11, x8, #44            // the data map alone, at the top
        popcount w12, x11               // the node's entries
        add     x13, x12, #7
        and     x13, x13, #-8           // their kind bytes, padded
        add     x14, x0, #8             // kind bytes
        add     x15, x14, x13           // keys
        add     x10, x9, #4             // the slot's data bit
        lsr     x16, x8, x10
        tbz     x16, #0, 3f             // no entry at the slot
        neg     x17, x10
        lsl     x16, x8, x17            // shifted by 60 - slot: the data bits below the slot, at the top
        popcount w16, x16               // the entry's index
        ldr     x17, [x15, x16, lsl #3]
        cmp     x17, x2
        b.ne    9f                      // another key holds the slot
        ldrb    w17, [x14, x16]
        cmp     x3, x17, lsr #4
        b.ne    9f                      // the same word of another kind
        add     x15, x15, x12, lsl #3   // values
        ldr     x0, [x15, x16, lsl #3]
        and     x1, x17, #0xf
        ret
3:      add     x10, x10, #16           // the slot's child bit
        lsr     x16, x8, x10
        tbz     x16, #0, 9f             // nothing at the slot
        neg     x17, x10
        lsl     x16, x8, x17            // shifted by 44 - slot: the child bits below the slot and every data bit
        popcount w16, x16               // the child's index plus the node's entries
        add     x15, x15, x12, lsl #3   // values
        ldr     x0, [x15, x16, lsl #3]  // values + entries is the first child word
        b       1b
8:      mov     x1, #-2
        ret
9:      mov     x1, #-1
        ret

// fz_trie_get_atom(root x0, atom id x1, process x2) -> as fz_trie_get. An atom's stored word is its
// id. The process holds the address of the node's cell that holds the address of the atom key hashes,
// one word per atom id; the cell stays where it is as the array grows, so the process keeps one
// address for its whole life.
        .globl _fz_trie_get_atom
        .p2align 2
_fz_trie_get_atom:
        ldr     x9, [x2]                // the cell
        ldr     x9, [x9]                // the array
        mov     x2, x1
        ldr     x1, [x9, x1, lsl #3]    // the atom's key hash
        mov     x3, #0xf                // ATOM
        b       _fz_trie_get
