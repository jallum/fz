// Floor harness for targets.s: builds binaries in the proposed layout, checks every target
// against a plain C reference over random inputs ("test"), and runs one target's loop
// ("NAME N") so its instructions per iteration can be measured as a slope.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { uint64_t hp, hlimit; uint32_t reds, pad; uint64_t arena, mbox_head, mbox_tail; } Proc;
typedef struct { uint64_t refcount; uint8_t *bytes; uint64_t bytes_len; void *destructor; uint64_t room; } SharedBin;
typedef uint64_t T(uint64_t, Proc *, uint64_t, uint64_t);
T t_empty, t_byte_size, t_byte_size_today, t_eq, t_ctor_byte, t_ctor_segments, t_slice, t_append, t_through_call, t_eq_wide, t_interp, t_match_tail, t_concat, t_match_sum, t_send_self;
#define ADDR 0x00ffffffffffffffull
static uint64_t *obj(size_t bytes) { void *p; if (posix_memalign(&p, 16, (bytes + 15) & ~15ull)) abort(); memset(p, 0xAA, (bytes + 15) & ~15ull); return p; }
static uint64_t mk_inline(const uint8_t *b, size_t n) { uint64_t *o = obj(8 + n); o[0] = (uint64_t)n << 7; memcpy(o + 1, b, n); return (5ull << 56) | (uint64_t)o; }
static uint64_t mk_view_on(SharedBin *sb, uint8_t *first, size_t n) {
  uint64_t *br = obj(16); br[0] = (uint64_t)sb; br[1] = 0;
  uint64_t *v = obj(32); v[0] = (uint64_t)n << 7; v[1] = (uint64_t)first; v[2] = (11ull << 56) | (uint64_t)br; return (6ull << 56) | (uint64_t)v; }
static SharedBin *mk_buf(const uint8_t *b, size_t n, size_t room) { SharedBin *sb = (SharedBin *)obj(48); uint8_t *bytes = malloc(room + 1); memcpy(bytes, b, n); bytes[n] = 0;
  sb->refcount = 1; sb->bytes = bytes; sb->bytes_len = n; sb->destructor = 0; sb->room = room; return sb; }
static uint64_t mk_view(const uint8_t *b, size_t n) { SharedBin *sb = mk_buf(b, n, n); return mk_view_on(sb, sb->bytes, n); }
static uint64_t mk_today_view(const uint8_t *b, size_t n) { uint64_t *v = obj(32); v[0] = 0; v[1] = (uint64_t)b; v[2] = (uint64_t)n << 3; return (6ull << 56) | (uint64_t)v; }
static size_t len_of(uint64_t w) { return ((uint64_t *)(w & ADDR))[0] >> 7; }
static const uint8_t *bytes_of(uint64_t w) { uint64_t *o = (uint64_t *)(w & ADDR); return (w >> 57) & 1 ? (const uint8_t *)o[1] : (const uint8_t *)(o + 1); }
static Proc proc(size_t arena) { Proc p; p.arena = (uint64_t)obj(arena); p.hp = p.arena; p.hlimit = p.arena + arena; p.reds = 4000; p.pad = 0; p.mbox_head = p.mbox_tail = 0; return p; }
#define CHECK(c, ...) do { if (!(c)) { printf("FAIL: " __VA_ARGS__); printf("\n"); exit(1); } } while (0)
static int test(void) {
  srandom(7); uint8_t a[256], b[256]; long rounds = 0;
  for (int r = 0; r < 200000; r++) {
    size_t n = random() % 201, m = random() % 4 ? n : (size_t)(random() % 201);
    for (size_t i = 0; i < n; i++) a[i] = random();
    memcpy(b, a, n < m ? n : m); for (size_t i = n; i < m; i++) b[i] = random();
    if (m && random() % 2) b[random() % m] ^= 1 << (random() % 8);
    uint64_t wa = random() % 2 ? mk_inline(a, n) : mk_view(a, n), wb = random() % 2 ? mk_inline(b, m) : mk_view(b, m);
    Proc p = proc(64);
    uint64_t want = n == m && memcmp(a, b, n) == 0;
    CHECK(t_eq(1, &p, wa, wb) == want, "eq n=%zu m=%zu want=%llu", n, m, want);
    CHECK(t_eq(1, &p, wa, wa) == 1, "eq identity");
    { uint64_t ma = random() % 2 ? mk_inline(a, n) : mk_view(a, n), mb = random() % 2 ? mk_inline(b, m) : mk_view(b, m); // marked copies
      if (random() % 2) ((uint64_t *)(ma & ADDR))[0] |= 1ull << 60; if (random() % 2) ((uint64_t *)(mb & ADDR))[0] |= 1ull << 60;
      CHECK(t_eq_wide(1, &p, ma, mb) == want, "eq_wide n=%zu m=%zu want=%llu", n, m, want); }
    { Proc q = proc(64); CHECK(t_match_tail(1, &q, wa, 0) == 0 && q.reds == 4000 - n - 1, "match_tail n=%zu reds=%u", n, q.reds); }
    if (n + m + 1 <= 64) { Proc q = proc(96); CHECK(t_interp(1, &q, wa, wb) == n + m + 1, "interp size"); uint64_t *o = (uint64_t *)q.arena; const uint8_t *ob = (const uint8_t *)(o + 1);
      CHECK(o[0] >> 7 == n + m + 1 && memcmp(ob, a, n) == 0 && ob[n] == '-' && memcmp(ob + n + 1, b, m) == 0, "interp bytes n=%zu m=%zu", n, m); }
    { Proc q = proc(64); uint64_t sum = 0; for (size_t i = 0; i < n; i++) sum += a[i];
      CHECK(t_match_sum(1, &q, wa, 0) == sum && q.reds == 4000 - n - 1, "match_sum n=%zu", n); }
    if (n + m <= 64) { Proc q = proc(96); CHECK(t_concat(1, &q, wa, wb) == n + m, "concat size"); uint64_t *o = (uint64_t *)q.arena; const uint8_t *ob = (const uint8_t *)(o + 1);
      CHECK(o[0] >> 7 == n + m && memcmp(ob, a, n) == 0 && memcmp(ob + n, b, m) == 0, "concat bytes n=%zu m=%zu", n, m); }
    { Proc q = proc(64); CHECK(t_send_self(3, &q, wa, 0) == 3 * n && q.mbox_head == 0 && q.mbox_tail == 0, "send_self n=%zu", n); }
    CHECK(t_byte_size(1, &p, wa, 0) == n, "byte_size");
    if (!(wa >> 57 & 1)) CHECK(t_byte_size_today(1, &p, wa, 0) == n, "byte_size_today inline");
    CHECK(t_byte_size_today(1, &p, mk_today_view(a, n), 0) == n, "byte_size_today view");
    if (n <= 61) { // constructor: <<rem(k,256)::8, k::16, a::binary>>
      uint64_t k = random() % 100000 + 1; p = proc(96);
      CHECK(t_ctor_segments(k + 1, &p, 0, wa) >= n + 3, "ctor size");
      // the last object built is for loop value k' = 0..: rebuild one with n=1 to inspect
      p.hp = p.arena; t_ctor_segments(1, &p, 0, wa); uint64_t *o = (uint64_t *)p.arena; const uint8_t *ob = (const uint8_t *)(o + 1);
      CHECK(o[0] >> 7 == n + 3 && ob[0] == 0 && ob[1] == 0 && ob[2] == 0 && memcmp(ob + 3, a, n) == 0, "ctor bytes n=%zu", n);
    }
    if (n >= 7) { p = proc(64); t_slice(1, &p, wa, 0); uint64_t *o = (uint64_t *)p.arena; CHECK(o[0] >> 7 == 4 && memcmp(o + 1, a + 3, 4) == 0, "slice"); }
    rounds++;
  }
  { Proc p = proc(64); t_ctor_byte(1, &p, 0, 0); uint64_t *o = (uint64_t *)p.arena; CHECK(o[0] >> 7 == 1 && (uint8_t)o[1] == 0, "ctor_byte"); }
  { // append: 1000 appends into a buffer with room; bytes and length must match, NUL after
    SharedBin *sb = mk_buf((const uint8_t *)"x", 1, 4096); uint64_t acc = mk_view_on(sb, sb->bytes, 1); Proc p = proc(64);
    t_append(1000, &p, acc, 0);
    CHECK(sb->bytes_len == 2001 && sb->bytes[0] == 'x' && sb->bytes[2001] == 0, "append len");
    for (int i = 0; i < 1000; i++) CHECK(sb->bytes[1 + 2 * i] == 'a' && sb->bytes[2 + 2 * i] == 'b', "append bytes");
    uint64_t *v = (uint64_t *)(p.hp - 32); CHECK(v[0] >> 7 == 2001 && (uint8_t *)v[1] == sb->bytes, "append view");
  }
  printf("ok: %ld random rounds\n", rounds); return 0;
}
int main(int argc, char **argv) {
  if (argc == 2 && !strcmp(argv[1], "test")) return test();
  uint64_t n = strtoull(argv[2], 0, 10); const char *t = argv[1]; Proc p = proc(1 << 16); uint8_t x[256]; memset(x, 'x', 256); uint64_t r;
  if (!strcmp(t, "empty")) r = t_empty(n, &p, 0, 0);
  else if (!strcmp(t, "byte_size")) r = t_byte_size(n, &p, mk_inline(x, 22), 0);
  else if (!strcmp(t, "byte_size_view")) r = t_byte_size(n, &p, mk_view(x, 202), 0);
  else if (!strcmp(t, "byte_size_today")) r = t_byte_size_today(n, &p, mk_inline(x, 22), 0);
  else if (!strcmp(t, "eq_small")) r = t_eq(n, &p, mk_inline(x, 11), mk_inline(x, 11));
  else if (!strcmp(t, "eq_large")) r = t_eq(n, &p, mk_view(x, 201), mk_view(x, 201));
  else if (!strcmp(t, "eq_same")) { uint64_t a = mk_inline(x, 11); r = t_eq(n, &p, a, a); }
  else if (!strcmp(t, "eq_length")) r = t_eq(n, &p, mk_inline(x, 11), mk_inline(x, 12));
  else if (!strcmp(t, "eqw_small")) r = t_eq_wide(n, &p, mk_inline(x, 11), mk_inline(x, 11));
  else if (!strcmp(t, "eqw_large")) r = t_eq_wide(n, &p, mk_view(x, 201), mk_view(x, 201));
  else if (!strcmp(t, "eqw_length")) r = t_eq_wide(n, &p, mk_inline(x, 11), mk_inline(x, 12));
  else if (!strcmp(t, "eqw_literal")) r = t_eq_wide(n, &p, mk_inline(x, 4), mk_inline(x, 4));
  else if (!strcmp(t, "eqw_differ")) { uint8_t y[11]; memset(y, 'x', 11); y[10] = 'y'; r = t_eq_wide(n, &p, mk_inline(x, 11), mk_inline(y, 11)); }
  else if (!strcmp(t, "match_tail")) { uint8_t big[1000]; memset(big, 'x', 1000); r = t_match_tail(n / 1000, &p, mk_view(big, 1000), 0); }
  else if (!strcmp(t, "match_sum")) { uint8_t big[1000]; memset(big, 'x', 1000); r = t_match_sum(n / 1000, &p, mk_view(big, 1000), 0); }
  else if (!strcmp(t, "concat")) r = t_concat(n, &p, mk_inline(x, 10), mk_inline(x, 2));
  else if (!strcmp(t, "send_self")) r = t_send_self(n, &p, mk_inline(x, 22), 0);
  else if (!strcmp(t, "interp")) r = t_interp(n, &p, mk_inline(x, 10), mk_inline(x, 2));
  else if (!strcmp(t, "ctor_byte")) r = t_ctor_byte(n, &p, 0, 0);
  else if (!strcmp(t, "ctor_segments")) r = t_ctor_segments(n, &p, 0, mk_inline(x, 22));
  else if (!strcmp(t, "slice")) r = t_slice(n, &p, mk_view(x, 202), 0);
  else if (!strcmp(t, "append")) { SharedBin *sb = mk_buf(x, 1, 2 * n + 16); r = t_append(n, &p, mk_view_on(sb, sb->bytes, 1), 0) + sb->bytes_len; }
  else if (!strcmp(t, "through_call")) r = t_through_call(n, &p, mk_inline(x, 22), 0);
  else { printf("unknown target %s\n", t); return 1; }
  printf("%llu\n", r); return 0;
}
