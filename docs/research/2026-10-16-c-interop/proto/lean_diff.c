/* lean_diff.c -- the C reader and writer against Lean's own compiled `Val.decode` and
   `Val.encode`, called from C.

   What it is: a differential with an outside oracle. The core's shared library
   (libeffect4_Effect4, built by Lake from the pinned toolchain) holds Lean's compiled code for
   `Store.Val.decode` and `Store.Val.encode` (src/Effect4/Store/Carrier/Val.lean), as the C
   symbols the compiler names `lp_effect4_Effect4_Store_Val_decode` and `..._encode`. This driver
   initializes Lean's runtime and that one module, then, for each input, compares the two
   verdicts: whether the input reads, and the bytes written back. It is route (a) of the C
   interop note at its smallest scale: Lean's compiled code, called from C over bytes.
   Depends on: e4val, fixture; lean.h and libleanshared from the toolchain; libeffect4_Effect4.

   Properties:
   D1  On every input, the C reader accepts exactly when Lean's decoder answers `some`.   tested
   D2  On every accepted input, the C writer's bytes are Lean's encoder's bytes.         tested
   D3  The inputs: every fixture frame, its byte flips (three masks, a spread of positions), its
       proper prefixes, and seeded random frames, nested, with a corrupted length now and then.
       The run reports how many inputs each side accepted, so D1 is not vacuous.         tested

   What it does not establish: anything past the inputs run. The symbol names are the
   compiler's mangled names, which move with a namespace; the C face of row 391 names its entries
   with `@[export]` instead. The run reads the library a Lake build left; it runs no Lake. */

#include <lean/lean.h>

#include "e4val.h"
#include "fixture.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Exported by libleanshared; the generated mains declare it, as lean.h of v4.33.1 does not. */
extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_effect4_Effect4_Store_Carrier_Val(uint8_t builtin);
extern lean_object *lp_effect4_Effect4_Store_Val_decode(lean_object *bytes);
extern lean_object *lp_effect4_Effect4_Store_Val_encode(lean_object *v);

/* `Store.Bytes` is `List UInt8`: a cons cell per byte, each byte boxed. */
static lean_object *list_of_bytes(const uint8_t *p, size_t n) {
  lean_object *l = lean_box(0);
  for (size_t i = n; i-- > 0;) {
    lean_object *cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, lean_box(p[i]));
    lean_ctor_set(cell, 1, l);
    l = cell;
  }
  return l;
}

static void bytes_of_list(lean_object *l, e4_buf *out) {
  while (!lean_is_scalar(l)) {
    uint8_t b = (uint8_t)lean_unbox(lean_ctor_get(l, 0));
    e4_buf_append(out, &b, 1);
    l = lean_ctor_get(l, 1);
  }
}

/* Lean's verdict. Both functions take their argument owned (the emitted C has no borrowed
   wrapper): `decode` passes the list on, `encode` releases the value. */
static bool lean_side(const uint8_t *p, size_t n, e4_buf *out) {
  lean_object *r = lp_effect4_Effect4_Store_Val_decode(list_of_bytes(p, n));
  if (lean_is_scalar(r)) return false;
  lean_object *v = lean_ctor_get(r, 0);
  lean_inc(v);
  lean_dec(r);
  lean_object *bytes = lp_effect4_Effect4_Store_Val_encode(v);
  bytes_of_list(bytes, out);
  lean_dec(bytes);
  return true;
}

static bool c_side(const uint8_t *p, size_t n, e4_buf *out) {
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  e4_val *v = e4_decode(&a, p, n, &why);
  bool ok = v && e4_encode(v, out, &why);
  e4_arena_free(&a);
  return ok;
}

static size_t inputs = 0, both_accept = 0, both_refuse = 0, disagree = 0;

static void compare(const uint8_t *p, size_t n, const char *origin) {
  e4_buf lb = {0}, cb = {0};
  bool l = lean_side(p, n, &lb), c = c_side(p, n, &cb);
  inputs++;
  bool same = l == c && (!l || (lb.len == cb.len && memcmp(lb.ptr, cb.ptr, lb.len) == 0));
  if (!same) {
    disagree++;
    if (disagree <= 10) {
      e4_buf hex = {0};
      e4_hex(p, n < 64 ? n : 64, &hex);
      printf("FAIL %s: Lean %s, C %s, input %.*s%s\n", origin, l ? "reads" : "refuses",
             c ? "reads" : "refuses", (int)hex.len, (const char *)hex.ptr, n > 64 ? "..." : "");
      e4_buf_free(&hex);
    }
  } else if (l) both_accept++;
  else both_refuse++;
  e4_buf_free(&lb);
  e4_buf_free(&cb);
}

/* ---- Seeded random frames -------------------------------------------------------------- */

static uint64_t seed = 0x9e3779b97f4a7c15u;

static uint64_t next_random(void) {
  seed ^= seed << 13;
  seed ^= seed >> 7;
  seed ^= seed << 17;
  return seed;
}

static void put_be64(e4_buf *b, uint64_t n) {
  uint8_t p[8];
  for (int i = 7; i >= 0; i--) { p[i] = (uint8_t)(n & 0xff); n >>= 8; }
  e4_buf_append(b, p, 8);
}

/* One frame: a tag in 0..15, and a payload of random bytes, or of child frames for the tags
   that carry them; its length is corrupted by one now and then. */
static void random_frame(e4_buf *out, int depth) {
  uint8_t tag = (uint8_t)(next_random() % 16);
  e4_buf payload = {0};
  bool children = (tag == E4_LIST || tag == E4_PAIR || tag == E4_SOME || tag == E4_CTOR) && depth < 4;
  if (children) {
    if (tag == E4_CTOR) {
      uint8_t ix = (uint8_t)(next_random() % 4);
      uint8_t head[9] = {E4_NAT, 0, 0, 0, 0, 0, 0, 0, ix ? 1 : 0};
      e4_buf_append(&payload, head, 9);
      if (ix) e4_buf_append(&payload, &ix, 1);
    }
    int k = tag == E4_PAIR ? 2 : tag == E4_SOME ? 1 : (int)(next_random() % 4);
    if (next_random() % 8 == 0) k++;
    for (int i = 0; i < k; i++) random_frame(&payload, depth + 1);
  } else {
    size_t n = tag == E4_FLOAT ? 8 : (size_t)(next_random() % 6);
    if (next_random() % 8 == 0) n++;
    for (size_t i = 0; i < n; i++) {
      uint64_t r = next_random();
      /* bias toward the boundary bytes the bodies test: 0, 1, ASCII, UTF-8 leads */
      static const uint8_t picks[] = {0, 1, 0x41, 0x7f, 0x80, 0xc2, 0xe0, 0xed, 0xf0, 0xf4, 0xff};
      uint8_t byte = (r % 3) ? picks[(r >> 8) % sizeof picks] : (uint8_t)(r >> 16);
      e4_buf_append(&payload, &byte, 1);
    }
  }
  uint64_t len = payload.len;
  if (next_random() % 16 == 0) len = len ? len - 1 : 1;
  e4_buf_append(out, &tag, 1);
  put_be64(out, len);
  e4_buf_append(out, payload.ptr, payload.len);
  e4_buf_free(&payload);
}

int main(int argc, char **argv) {
  lean_initialize_runtime_module();
  lean_object *res = initialize_effect4_Effect4_Store_Carrier_Val(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();

  for (int i = 1; i < argc; i++)
    if (fixture_load(argv[i]) < 0) { printf("FAIL cannot open %s\n", argv[i]); return 1; }
  printf("read %zu fixture frames\n", fixture_count);

  static const uint8_t masks[3] = {0x01, 0x80, 0xff};
  for (size_t i = 0; i < fixture_count; i++) {
    const fixture_frame *f = &fixture_frames[i];
    compare(f->ptr, f->len, f->origin);
    uint8_t *m = malloc(f->len + 1);
    size_t step = f->len <= 512 ? 1 : f->len / 199;
    for (size_t pos = 0; pos < f->len; pos += step) {
      for (int k = 0; k < 3; k++) {
        memcpy(m, f->ptr, f->len);
        m[pos] ^= masks[k];
        compare(m, f->len, f->origin);
      }
    }
    for (size_t cut = 0; cut < f->len; cut += step) compare(f->ptr, cut, f->origin);
    memcpy(m, f->ptr, f->len);
    m[f->len] = 0;
    compare(m, f->len + 1, f->origin);
    free(m);
  }
  size_t from_fixtures = inputs, read_from_fixtures = both_accept;
  for (int i = 0; i < 20000; i++) {
    e4_buf b = {0};
    random_frame(&b, 0);
    compare(b.ptr, b.len, "random");
    e4_buf_free(&b);
  }
  printf("%s D1 D2 %zu inputs (%zu from the fixtures, %zu random): both read %zu, both refuse %zu, "
         "disagree %zu\n", disagree ? "FAIL" : "PASS", inputs, from_fixtures, inputs - from_fixtures,
         both_accept, both_refuse, disagree);
  bool vacuous = both_accept == 0 || both_refuse == 0;
  printf("%s D3 both sides read some inputs and refuse others: of the fixtures' inputs %zu read, "
         "of the random %zu read\n", vacuous ? "FAIL" : "PASS", read_from_fixtures,
         both_accept - read_from_fixtures);
  fixture_free();
  return disagree || vacuous ? 1 : 0;
}
