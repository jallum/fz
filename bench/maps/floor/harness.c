// Checks the hand-written sequences in flat.s against a reference, and runs them as the floor
// for the map probes. `harness test` checks; `harness <probe> <iterations> <keys>` runs a probe.
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
static int test(void) {
    static uint8_t arena[1 << 20];
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
        }
    }
    printf("ok\n");
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
