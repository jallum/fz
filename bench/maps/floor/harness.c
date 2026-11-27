// Checks the hand-written sequences in flat.s, trie.s and walk.s against a reference, and runs them as the
// floor for the map probes. `harness test` checks; `harness <probe> <iterations> <keys>` runs a probe.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "keys.h"

typedef struct { uint8_t *top, *end; } Bump;
typedef struct { int64_t slot; uint64_t found; } Found;
typedef struct { uint64_t word; int64_t kind; } Got;
Got fz_flat_get(const uint8_t *map, uint64_t key, uint64_t kind);
int64_t fz_flat_scan(const uint8_t *map, uint64_t key, uint64_t kind);
int64_t fz_flat_place(const uint8_t *map, uint64_t kind, uint64_t order, const uint64_t *prefixes);
Found fz_flat_find(const uint8_t *map, uint64_t kind, uint64_t order, const uint64_t *prefixes, uint64_t key);
Found fz_flat_find_bin(const uint8_t *map, const uint64_t *key);
uint8_t *fz_flat_write(Bump *b, const uint8_t *map, uint64_t slot, uint64_t action, uint64_t key, uint64_t kkind, uint64_t value, uint64_t vkind);
Got fz_trie_get(const uint8_t *root, uint64_t hash, uint64_t key, uint64_t kind);
typedef struct { uint64_t **atom_key_hashes; } Process;
Got fz_trie_get_atom(const uint8_t *root, uint64_t atom, const Process *process);
uint64_t fz_map_keys(const uint8_t *map, Bump *b);
uint64_t fz_map_values(const uint8_t *map, Bump *b);
uint64_t fz_map_pairs(const uint8_t *map, Bump *b, uint64_t pair_header);
uint64_t fz_map_next_batch(const uint8_t *map, uint64_t index, Bump *b, uint64_t triple_header, uint64_t none);

enum { BITSTRING = 5, INT = 0xD, ATOM = 0xF };
enum { INSERT, REPLACE, SKIP };
#define SIGN 0x8000000000000000ull

static size_t pad8(size_t n) { return (n + 7) & ~7ul; }
static size_t count(const uint8_t *m) { return *(const uint64_t *)m >> 4; }
static const uint8_t *kinds(const uint8_t *m) { return m + 8; }
static const uint64_t *keys(const uint8_t *m) { return (const uint64_t *)(m + 8 + pad8(count(m))); }
static const uint64_t *vals(const uint8_t *m) { return keys(m) + count(m); }

static uint64_t prefixes[256];
static int ordered;
static uint64_t name_prefix(const char *name) {
    uint64_t p = 0; size_t n = strlen(name);
    for (size_t i = 0; i < 8; i++) p = p << 8 | (i < n ? (uint8_t)name[i] : 0);
    return p;
}
static uint64_t order_word(uint64_t kind, uint64_t key) { return kind == ATOM ? prefixes[key] : key ^ SIGN; }

static const uint8_t *put_word(Bump *b, const uint8_t *m, uint64_t key, uint64_t kind, uint64_t value) {
    if (ordered) {
        Found f = fz_flat_find(m, kind, order_word(kind, key), prefixes, key);
        return f.slot < 0 ? 0 : fz_flat_write(b, m, f.slot, f.found ? REPLACE : INSERT, key, kind, value, INT);
    }
    int64_t slot = fz_flat_scan(m, key, kind);
    if (slot >= 0) return fz_flat_write(b, m, slot, REPLACE, key, kind, value, INT);
    slot = fz_flat_place(m, kind, order_word(kind, key), prefixes);
    return slot < 0 ? 0 : fz_flat_write(b, m, slot, INSERT, key, kind, value, INT);
}
static const uint8_t *delete_word(Bump *b, const uint8_t *m, uint64_t key, uint64_t kind) {
    int64_t slot = fz_flat_scan(m, key, kind);
    return slot < 0 ? m : fz_flat_write(b, m, slot, SKIP, 0, 0, 0, 0);
}
static const uint8_t *put_bin(Bump *b, const uint8_t *m, const uint64_t *key, uint64_t value) {
    Found f = fz_flat_find_bin(m, key);
    if (f.slot < 0) return 0;
    return f.found ? fz_flat_write(b, m, f.slot, REPLACE, keys(m)[f.slot], BITSTRING, value, INT)
                   : fz_flat_write(b, m, f.slot, INSERT, (uint64_t)key, BITSTRING, value, INT);
}
static const uint8_t *delete_bin(Bump *b, const uint8_t *m, const uint64_t *key) {
    Found f = fz_flat_find_bin(m, key);
    return f.found ? fz_flat_write(b, m, f.slot, SKIP, 0, 0, 0, 0) : m;
}
static uint64_t *binary(const char *text) {
    size_t n = strlen(text);
    uint64_t *object = calloc(1 + pad8(n) / 8 + 1, 8);
    object[0] = n * 8;
    memcpy(object + 1, text, n);
    return object;
}

// Reference: entries kept in term order.
typedef struct { uint64_t kind, key, value; } E;
static int rank(uint64_t kind) { return kind == INT ? 0 : kind == ATOM ? 1 : 9; }
static int key_cmp(uint64_t ak, uint64_t a, uint64_t bk, uint64_t b) {
    if (rank(ak) != rank(bk)) return rank(ak) < rank(bk) ? -1 : 1;
    if (ak == BITSTRING) {
        const uint64_t *x = (const uint64_t *)a, *y = (const uint64_t *)b;
        size_t xn = x[0] / 8, yn = y[0] / 8;
        int c = memcmp(x + 1, y + 1, xn < yn ? xn : yn);
        return c ? c : xn < yn ? -1 : xn > yn;
    }
    uint64_t x = order_word(ak, a), y = order_word(bk, b);
    return x < y ? -1 : x > y;
}
static int ref_find(const E *e, int n, uint64_t kind, uint64_t key, int *at) {
    int i = 0;
    while (i < n && key_cmp(e[i].kind, e[i].key, kind, key) < 0) i++;
    *at = i;
    return i < n && key_cmp(e[i].kind, e[i].key, kind, key) == 0;
}
static void fail(const char *what) { printf("FAIL %s\n", what); exit(1); }
static void check(const uint8_t *m, const E *e, int n) {
    if (count(m) != (size_t)n) fail("count");
    for (int i = 0; i < n; i++) {
        if (kinds(m)[i] != ((e[i].kind << 4) | INT) || vals(m)[i] != e[i].value) fail("entry");
        if (key_cmp(e[i].kind, keys(m)[i], e[i].kind, e[i].key)) fail("key");
        if (e[i].kind == BITSTRING) {
            Found f = fz_flat_find_bin(m, (const uint64_t *)e[i].key);
            if (!f.found || f.slot != i) fail("find_bin");
        } else {
            if (fz_flat_scan(m, e[i].key, e[i].kind) != i) fail("scan");
            Got got = fz_flat_get(m, e[i].key, e[i].kind);
            if (got.kind != INT || got.word != e[i].value) fail("get");
        }
    }
    if (fz_flat_get(m, 0xFFFFFF, ATOM).kind != -1) fail("get of an absent key");
    for (size_t i = n; i < pad8(n); i++) if (kinds(m)[i]) fail("padding");
}
// The runtime's key hashes (runtime/src/term_hash.rs), so a trie here has the shape fz gives the
// same keys.
#define MULTIPLIER_A 0x87c37b91114253d5ull
#define MULTIPLIER_B 0x4cf5ad432745937full
#define SALT_INT 0x9e3779b97f4a7c15ull
#define SALT_ATOM 0xc2b2ae3d27d4eb4full
static uint64_t finalize(uint64_t x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdull; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ull;
    return x ^ (x >> 33);
}
static uint64_t rotl(uint64_t x, int r) { return x << r | x >> (64 - r); }
static uint64_t bytes_hash(const char *s, size_t n, uint64_t seed) {
    uint64_t h = seed ^ n * MULTIPLIER_A, w;
    size_t i = 0;
    for (; i + 8 <= n; i += 8) {
        memcpy(&w, s + i, 8);
        h ^= rotl(w * MULTIPLIER_A, 31) * MULTIPLIER_B;
        h = rotl(h, 27) * 5 + 0x52dce729;
    }
    if (i < n) { w = 0; memcpy(&w, s + i, n - i); h ^= rotl(w * MULTIPLIER_A, 31) * MULTIPLIER_B; }
    return finalize(h);
}
static uint64_t atom_key_hash(const char *name) { return finalize(bytes_hash(name, strlen(name), SALT_ATOM) ^ SALT_ATOM); }
static uint64_t int_key_hash(uint64_t i) { return finalize(i ^ SALT_INT); }

// A trie of entries with their hashes, by the runtime's rule: an entry sits in the node of the first
// level at which no other key shares its slot, and keys whose hashes are equal meet in a collision
// node after sixteen levels.
#define TRIE_FLAG (1ull << 62)
#define COLLISION_FLAG (1ull << 61)
typedef struct { uint64_t hash, kind, key, value; } H;
static uint8_t *alloc16(Bump *b, size_t bytes) {
    uint8_t *at = (uint8_t *)(((uintptr_t)b->top + 15) & ~(uintptr_t)15);
    if (at + bytes > b->end) fail("arena");
    b->top = at + bytes;
    return at;
}
static uint8_t *node_of(Bump *b, uint64_t header, const H *e, int ne, uint8_t *const *child, int nc) {
    uint8_t *m = alloc16(b, (8 + pad8(ne) + ne * 16 + nc * 8 + 15) & ~15ul);
    *(uint64_t *)m = header;
    memset(m + 8, 0, pad8(ne));
    uint64_t *k = (uint64_t *)(m + 8 + pad8(ne)), *v = k + ne, *c = v + ne;
    for (int i = 0; i < ne; i++) { m[8 + i] = e[i].kind << 4 | INT; k[i] = e[i].key; v[i] = e[i].value; }
    for (int i = 0; i < nc; i++) c[i] = (uint64_t)child[i];
    return m;
}
static uint8_t *trie_level(Bump *b, const H *e, int n, int level) {
    if (level == 16) return node_of(b, TRIE_FLAG | COLLISION_FLAG | (uint64_t)n << 36, e, n, 0, 0);
    H own[16], *group = malloc(n * sizeof(H)); uint8_t *child[16]; int ne = 0, nc = 0; uint64_t data = 0, kids = 0;
    for (int s = 0; s < 16; s++) {
        int g = 0;
        for (int i = 0; i < n; i++) if ((e[i].hash >> (60 - 4 * level) & 15) == (uint64_t)s) group[g++] = e[i];
        if (g == 1) { own[ne++] = group[0]; data |= 1u << s; }
        if (g > 1) { child[nc++] = trie_level(b, group, g, level + 1); kids |= 1u << s; }
    }
    free(group);
    return node_of(b, TRIE_FLAG | (uint64_t)n << 36 | kids << 20 | data << 4, own, ne, child, nc);
}

static uint64_t atom_hashes[512];
static uint64_t *atom_hash_array = atom_hashes;
static const Process process = {&atom_hash_array};
static Got trie_get(const uint8_t *root, uint64_t kind, uint64_t key) {
    return kind == ATOM ? fz_trie_get_atom(root, key, &process) : fz_trie_get(root, int_key_hash(key), key, kind);
}
static uint64_t key_hash(uint64_t kind, uint64_t key) { return kind == ATOM ? atom_hashes[key] : int_key_hash(key); }

// The entries of a map in the runtime's order: a node's own entries, then each child's in turn.
typedef struct { uint64_t kkind, key, vkind, value; } Entry;
static int entries_of(const uint8_t *m, Entry *out) {
    uint64_t h = *(const uint64_t *)m;
    int ne = !(h & TRIE_FLAG) ? (int)(h >> 4) : h & COLLISION_FLAG ? (int)(h >> 36 & 0x1ffffff) : __builtin_popcountll(h >> 4 & 0xffff);
    int nc = (h & TRIE_FLAG) && !(h & COLLISION_FLAG) ? __builtin_popcountll(h >> 20 & 0xffff) : 0;
    const uint64_t *k = (const uint64_t *)(m + 8 + pad8(ne)), *v = k + ne, *c = v + ne;
    int n = 0;
    for (int i = 0; i < ne; i++) out[n++] = (Entry){m[8 + i] >> 4, k[i], m[8 + i] & 15, v[i]};
    for (int i = 0; i < nc; i++) n += entries_of((const uint8_t *)c[i], out + n);
    return n;
}
#define LIST_KIND 1ull
#define STRUCT_KIND 3ull
#define PAIR_HEADER 0x0000002a00000000ull
static const uint64_t *cell_at(uint64_t word) { return (const uint64_t *)(word & 0x00fffffffffffff0ull); }
static void check_list(uint64_t list, const Entry *e, int n, int mode) {
    if (n == 0) { if (list != 8) fail("empty walk"); return; }
    if (list >> 56 != LIST_KIND) fail("list word");
    const uint64_t *cell = cell_at(list);
    for (int i = 0; i < n; i++) {
        uint64_t head = cell[0];
        if (mode == 0 && head != e[i].key) fail("key word");
        if (mode == 1 && head != e[i].value) fail("value word");
        if (mode == 2) {
            const uint64_t *pair = (const uint64_t *)head;
            if (pair[0] != PAIR_HEADER || pair[1] != e[i].key || pair[2] != e[i].value || pair[3] != (e[i].kkind | e[i].vkind << 8)) fail("pair");
        }
        uint64_t kind = mode == 0 ? e[i].kkind : mode == 1 ? e[i].vkind : STRUCT_KIND;
        uint64_t link = cell[1];
        if (link >> 56 != kind) fail("tail kind");
        if (i == n - 1) { if ((link & 0x00ffffffffffffffull) != 0) fail("last tail"); }
        else cell = cell_at(link);
    }
}
static void check_walks(const uint8_t *m, uint8_t *arena, size_t size) {
    static Entry e[400];
    int n = entries_of(m, e);
    for (int mode = 0; mode < 3; mode++) {
        Bump b = {arena, arena + size};
        uint64_t list = mode == 0 ? fz_map_keys(m, &b) : mode == 1 ? fz_map_values(m, &b) : fz_map_pairs(m, &b, PAIR_HEADER);
        check_list(list, e, n, mode);
        Bump tight = {arena, arena + (n ? 8 : 0)};
        if (n && (mode == 0 ? fz_map_keys(m, &tight) : mode == 1 ? fz_map_values(m, &tight) : fz_map_pairs(m, &tight, PAIR_HEADER)) != 0) fail("walk past the bump");
    }
}
#define TRIPLE_HEADER 0x0000002b00000000ull
#define NONE_ATOM 77ull
#define BATCH 32
#define MAP_KIND 2ull
#define INT_KIND 0xDull
#define LINK_TERMINATOR (1ull << 63)
// The batch from entry `index`: its tuples hold the entries in order, each leads to the one placed after it,
// and the last leads to the continuation or to none. A bump that cannot hold it places nothing.
static void check_batch(const uint8_t *m, const Entry *e, int n, int index, uint8_t *arena, size_t size) {
    int k = n - index < BATCH ? n - index : BATCH;
    int more = index + k < n;
    size_t used = (size_t)k * 48 + (more ? 32 : 0);
    Bump b = {arena, arena + size};
    uint64_t word = fz_map_next_batch(m, index, &b, TRIPLE_HEADER, NONE_ATOM);
    if (word >> 56 != STRUCT_KIND) fail("batch word");
    if ((size_t)(b.top - arena) != used) fail("batch size");
    for (int i = 0; i < k; i++) {
        const uint64_t *t = (const uint64_t *)(arena + (size_t)i * 48);
        const Entry *entry = e + index + i;
        int last = i == k - 1;
        uint64_t next_kind = !last ? STRUCT_KIND : more ? LIST_KIND : ATOM;
        if (t[0] != TRIPLE_HEADER || t[1] != entry->key || t[2] != entry->value) fail("batch tuple");
        if (t[4] != (entry->kkind | entry->vkind << 8 | next_kind << 16) || t[5] != 0) fail("batch kinds");
        if (!last) { if (t[3] != (uint64_t)(t + 6)) fail("batch next"); continue; }
        if (!more) { if (t[3] != NONE_ATOM) fail("batch none"); continue; }
        const uint64_t *cell = (const uint64_t *)t[3], *terminator = (const uint64_t *)(arena + used - 32);
        if (cell != (const uint64_t *)(arena + used - 16)) fail("continuation cell");
        if (cell[0] != (uint64_t)(index + k) || cell[1] != (INT_KIND << 56 | (uint64_t)terminator | LINK_TERMINATOR)) fail("continuation");
        if (terminator[0] != (uint64_t)m || terminator[1] != MAP_KIND << 56) fail("continuation tail");
    }
    Bump exact = {arena, arena + used};
    if (!fz_map_next_batch(m, index, &exact, TRIPLE_HEADER, NONE_ATOM)) fail("batch in exact room");
    Bump tight = {arena, arena + used - 1};
    if (fz_map_next_batch(m, index, &tight, TRIPLE_HEADER, NONE_ATOM) != 0) fail("batch past the bump");
}
static void check_batches(const uint8_t *m, uint8_t *arena, size_t size) {
    static Entry e[400];
    int n = entries_of(m, e);
    for (int index = 0; index < n; index++) check_batch(m, e, n, index, arena, size);
}
static int test_trie(void) {
    static uint8_t arena[1 << 22], walk_arena[1 << 16];
    static H e[400];
    for (int round = 0; round < 4000; round++) {
        for (int i = 0; i < 512; i++) atom_hashes[i] = (uint64_t)rand() << 42 ^ (uint64_t)rand() << 21 ^ (uint64_t)rand();
        for (int i = 0; i < 8; i++) atom_hashes[rand() % 512] = atom_hashes[rand() % 512];
        int n = 2 + rand() % 300, have = 0;
        while (have < n) {
            uint64_t kind = rand() % 3 ? ATOM : INT;
            uint64_t key = kind == ATOM ? (uint64_t)(rand() % 512) : (uint64_t)(int64_t)(rand() % 2000 - 1000);
            int dup = 0;
            for (int i = 0; i < have; i++) dup |= e[i].kind == kind && e[i].key == key;
            if (!dup) e[have++] = (H){key_hash(kind, key), kind, key, (uint64_t)rand()};
        }
        Bump b = {arena, arena + sizeof arena};
        const uint8_t *root = trie_level(&b, e, n, 0);
        for (int i = 0; i < n; i++) {
            Got got = trie_get(root, e[i].kind, e[i].key);
            int shared = 0;
            for (int j = 0; j < n; j++) shared |= j != i && e[j].hash == e[i].hash;
            if (shared ? got.kind != -2 : got.kind != INT || got.word != e[i].value) fail("trie get");
        }
        for (int probe = 0; probe < 200; probe++) {
            uint64_t kind = probe & 1 ? ATOM : INT;
            uint64_t key = kind == ATOM ? (uint64_t)(rand() % 512) : (uint64_t)(int64_t)(rand() % 2000 - 1000);
            int present = 0, same_hash = 0;
            for (int i = 0; i < n; i++) {
                present |= e[i].kind == kind && e[i].key == key;
                same_hash += e[i].hash == key_hash(kind, key);
            }
            Got got = trie_get(root, kind, key);
            if (!present && got.kind != (same_hash > 1 ? -2 : -1)) fail("trie get of an absent key");
        }
        check_walks(root, walk_arena, sizeof walk_arena);
        check_batches(root, walk_arena, sizeof walk_arena);
    }
    return 0;
}
static int test(void) {
    static uint8_t arena[1 << 20], walk_arena[1 << 12];
    static uint64_t empty[2];
    uint64_t *bins[40]; char text[8];
    srand(7);
    for (int i = 0; i < 64; i++) prefixes[i] = ((uint64_t)rand() << 20) ^ (uint64_t)i * 7919;
    for (int i = 0; i < 40; i++) {
        int n = rand() % 6;
        for (int c = 0; c < n; c++) text[c] = 'a' + rand() % 3;
        text[n] = 0; bins[i] = binary(text);
    }
    for (int round = 0; round < 20000; round++) {
        Bump b = {arena, arena + sizeof arena};
        memset(arena, 0xAA, 8192);
        E e[33]; int n = 0, at; const uint8_t *m = (const uint8_t *)empty;
        int ops = 1 + rand() % 80;
        for (int p = 0; p < ops; p++) {
            int which = rand() % 8, remove = rand() % 4 == 0;
            uint64_t kind = which < 4 ? ATOM : which < 6 ? INT : BITSTRING;
            uint64_t key = kind == ATOM ? (uint64_t)(rand() % 64) : kind == INT ? (uint64_t)(int64_t)(rand() % 40 - 20) : (uint64_t)bins[rand() % 40];
            uint64_t value = rand();
            int had = ref_find(e, n, kind, key, &at);
            const uint8_t *r;
            if (remove) {
                r = kind == BITSTRING ? delete_bin(&b, m, (const uint64_t *)key) : delete_word(&b, m, key, kind);
                if (had) { memmove(e + at, e + at + 1, (n - at - 1) * sizeof(E)); n--; } else if (r != m) fail("absent delete");
            } else {
                r = kind == BITSTRING ? put_bin(&b, m, (const uint64_t *)key, value) : put_word(&b, m, key, kind, value);
                if (n == 32 && !had) { if (r) fail("full"); continue; }
                if (!r) fail("null");
                if (had) e[at].value = value;
                else { memmove(e + at + 1, e + at, (n - at) * sizeof(E)); e[at] = (E){kind, key, value}; n++; }
            }
            m = r; check(m, e, n);
            check_walks(m, walk_arena, sizeof walk_arena);
            check_batches(m, walk_arena, sizeof walk_arena);
        }
    }
    test_trie();
    printf("ok\n");
    return 0;
}

// Turns a trie of k integer keys into a list n times; the answer is the number of cells placed.
static int walk_probe(const char *probe, long n, int k) {
    H *e = malloc(k * sizeof(H));
    for (int j = 0; j < k; j++) e[j] = (H){int_key_hash((uint64_t)(j + 1) * 7919), INT, (uint64_t)(j + 1) * 7919, (uint64_t)j};
    size_t size = (size_t)k * 64 + (1 << 20);
    uint8_t *nodes = malloc(size), *cells = malloc(size);
    Bump b = {nodes, nodes + size};
    const uint8_t *root = trie_level(&b, e, k, 0);
    int mode = probe[0] == 'k' ? 0 : probe[0] == 'v' ? 1 : 2;
    uint64_t answer = 0;
    for (long i = 0; i < n; i++) {
        Bump c = {cells, cells + size};
        uint64_t list = mode == 0 ? fz_map_keys(root, &c) : mode == 1 ? fz_map_values(root, &c) : fz_map_pairs(root, &c, PAIR_HEADER);
        if (!list) fail("bump");
        answer += (uint64_t)(c.top - cells) / (mode == 2 ? 48 : 16);
    }
    printf("%llu\n", (unsigned long long)answer);
    return 0;
}

int main(int argc, char **argv) {
    ordered = getenv("ORDERED") != 0;
    if (argc == 2 && !strcmp(argv[1], "test")) return test();
    if (argc != 4) { fprintf(stderr, "usage: harness test | harness <probe> <iterations> <keys>\n"); return 2; }
    const char *probe = argv[1]; long n = atol(argv[2]); int k = atoi(argv[3]);
    int binary_keys = probe[strlen(probe) - 1] == 'b';
    static uint8_t arenas[2][1 << 16];
    static uint64_t empty[2];
    uint64_t key[KEY_COUNT];
    for (int i = 0; i < KEY_COUNT; i++) {
        prefixes[40 + i] = name_prefix(KEY_NAMES[i]);
        key[i] = binary_keys ? (uint64_t)binary(KEY_NAMES[i]) : (uint64_t)(40 + i);
    }
    #define PUT(b, m, i, v) (binary_keys ? put_bin(b, m, (const uint64_t *)key[i], v) : put_word(b, m, key[i], ATOM, v))
    #define DEL(b, m, i) (binary_keys ? delete_bin(b, m, (const uint64_t *)key[i]) : delete_word(b, m, key[i], ATOM))
    Bump b = {arenas[0], arenas[0] + sizeof arenas[0]};
    const uint8_t *m = (const uint8_t *)empty;
    uint64_t answer = 0;
    if (!strncmp(probe, "keys", 4) || !strncmp(probe, "values", 6) || !strncmp(probe, "to_list", 7)) return walk_probe(probe, n, k);
    if (k > 32) {
        if (binary_keys || (strncmp(probe, "case", 4) && strncmp(probe, "get", 3))) {
            fprintf(stderr, "no trie floor for %s\n", probe); return 2;
        }
        H e[KEY_COUNT];
        for (int j = 0; j < k; j++) {
            atom_hashes[key[j]] = atom_key_hash(KEY_NAMES[j]);
            e[j] = (H){atom_hashes[key[j]], ATOM, key[j], (uint64_t)j};
        }
        const uint8_t *root = trie_level(&b, e, k, 0);
        for (long i = 0; i < n; i++)
            for (int j = 0; j < 6; j++) {
                Got got = fz_trie_get_atom(root, key[PICKS[j]], &process);
                if (got.kind != -1) answer += got.word;
            }
        printf("%llu\n", (unsigned long long)answer);
        return 0;
    }
    if (!strncmp(probe, "build", 5)) {
        for (long i = 0; i < n; i++) {
            b.top = arenas[0]; m = (const uint8_t *)empty;
            for (int j = 0; j < k; j++) m = PUT(&b, m, j, (uint64_t)i);
        }
        answer = count(m);
    } else {
        for (int j = 0; j < k; j++) m = PUT(&b, m, j, (uint64_t)j);
        for (long i = 0; i < n; i++) {
            b.top = arenas[(i & 1) + 0]; b.end = b.top + sizeof arenas[0];
            if (i == 0) b.top = (uint8_t *)m + 4096;
            if (!strncmp(probe, "case", 4) && !binary_keys) {
                for (int j = 0; j < 6; j++) {
                    Got got = fz_flat_get(m, key[PICKS[j]], ATOM);
                    if (got.kind != -1) answer += got.word;
                }
            } else if (!strncmp(probe, "get", 3) || !strncmp(probe, "case", 4)) {
                for (int j = 0; j < 6; j++) {
                    int64_t slot = binary_keys ? fz_flat_find_bin(m, (const uint64_t *)key[PICKS[j]]).slot : ordered ? fz_flat_find(m, ATOM, prefixes[key[PICKS[j]]], prefixes, key[PICKS[j]]).slot : fz_flat_scan(m, key[PICKS[j]], ATOM);
                    answer += vals(m)[slot];
                }
            } else if (!strncmp(probe, "replace", 7)) {
                for (int j = 0; j < 6; j++) m = PUT(&b, m, PICKS[j], (uint64_t)i);
            } else if (!strncmp(probe, "delete", 6)) {
                for (int j = 0; j < 3; j++) m = DEL(&b, m, PICKS[j]);
                for (int j = 0; j < 3; j++) m = PUT(&b, m, PICKS[j], (uint64_t)i);
            } else { fprintf(stderr, "unknown probe %s\n", probe); return 2; }
        }
        if (strncmp(probe, "get", 3) && strncmp(probe, "case", 4)) answer = count(m);
    }
    printf("%llu\n", (unsigned long long)answer);
    return 0;
}
