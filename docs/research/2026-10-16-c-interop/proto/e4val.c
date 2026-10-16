/* e4val.c -- the Val wire frames in C. The header e4val.h carries the property list. Each stage
   names the Lean declaration of src/Effect4/Store/Carrier/Val.lean (or Utf8.lean, Digits.lean)
   that it transcribes. */

#include "e4val.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---- The arena ------------------------------------------------------------------------- */

struct e4_arena_block {
  e4_arena_block *next;
  size_t used;
  size_t cap;
  _Alignas(16) unsigned char data[];
};

#define E4_BLOCK 65536

void e4_arena_init(e4_arena *a) { a->head = NULL; }

void e4_arena_free(e4_arena *a) {
  e4_arena_block *b = a->head;
  while (b) {
    e4_arena_block *next = b->next;
    free(b);
    b = next;
  }
  a->head = NULL;
}

void *e4_arena_alloc(e4_arena *a, size_t size) {
  size = (size + 15) & ~(size_t)15;
  if (size == 0) size = 16;
  e4_arena_block *b = a->head;
  if (!b || b->cap - b->used < size) {
    size_t cap = size > E4_BLOCK ? size : E4_BLOCK;
    b = malloc(sizeof(e4_arena_block) + cap);
    if (!b) { fputs("e4_arena_alloc: out of memory\n", stderr); abort(); }
    b->next = a->head;
    b->used = 0;
    b->cap = cap;
    a->head = b;
  }
  void *p = b->data + b->used;
  b->used += size;
  memset(p, 0, size);
  return p;
}

/* ---- The output buffer ----------------------------------------------------------------- */

static void buf_reserve(e4_buf *b, size_t extra) {
  if (b->cap - b->len >= extra) return;
  size_t cap = b->cap ? b->cap : 256;
  while (cap - b->len < extra) cap *= 2;
  uint8_t *p = realloc(b->ptr, cap);
  if (!p) { fputs("e4_buf: out of memory\n", stderr); abort(); }
  b->ptr = p;
  b->cap = cap;
}

void e4_buf_append(e4_buf *b, const void *p, size_t n) {
  buf_reserve(b, n);
  if (n) memcpy(b->ptr + b->len, p, n);
  b->len += n;
}

#define buf_append e4_buf_append

static void buf_byte(e4_buf *b, uint8_t x) { buf_append(b, &x, 1); }

static void buf_str(e4_buf *b, const char *s) { buf_append(b, s, strlen(s)); }

void e4_buf_free(e4_buf *b) {
  free(b->ptr);
  b->ptr = NULL;
  b->len = b->cap = 0;
}

/* ---- Digits (Digits.lean) -------------------------------------------------------------- */

/* `natOfDigits` on eight bytes: the length prefix. */
static uint64_t be64_read(const uint8_t *p) {
  uint64_t n = 0;
  for (int i = 0; i < 8; i++) n = (n << 8) | p[i];
  return n;
}

/* `be64`: eight big-endian bytes. */
static void be64_write(uint8_t *p, uint64_t n) {
  for (int i = 7; i >= 0; i--) { p[i] = (uint8_t)(n & 0xff); n >>= 8; }
}

bool e4_nat_u64(e4_slice digits, uint64_t *out) {
  if (digits.len > 8) return false;
  uint64_t n = 0;
  for (size_t i = 0; i < digits.len; i++) n = (n << 8) | digits.ptr[i];
  *out = n;
  return true;
}

/* `natBytes`: base-256 digits, big-endian, no leading zero; 0 is no digits. Writes into p[8] and
   returns the digit count; the digits are the last `count` bytes of p. */
static size_t nat_bytes(uint8_t p[8], uint64_t n) {
  be64_write(p, n);
  size_t lead = 0;
  while (lead < 8 && p[lead] == 0) lead++;
  return 8 - lead;
}

/* ---- The binary64 frame's domain: `Val.floatFrame` ------------------------------------- */

bool e4_float_frame(uint64_t bits) {
  uint64_t exponent = (bits >> 52) & 0x7ff;
  uint64_t fraction = bits & ((UINT64_C(1) << 52) - 1);
  if (exponent == 2047) return true;
  if (exponent == 0) return fraction != 0 || (bits >> 63) != 0;
  if (exponent < 1023) return true;
  if (exponent >= 1075) return false;
  return (fraction & ((UINT64_C(1) << (1075 - exponent)) - 1)) != 0;
}

/* ---- Strict UTF-8: `utf8Chars` (Utf8.lean) --------------------------------------------- */

static int cont_bits(uint8_t b) { return (b >= 0x80 && b < 0xc0) ? (int)(b - 0x80) : -1; }

/* Returns the offset of the first refused sequence's lead byte, or len; *reason names why. */
static size_t utf8_check(const uint8_t *p, size_t len, const char **reason) {
  size_t i = 0;
  while (i < len) {
    uint8_t b0 = p[i];
    if (b0 < 0x80) { i++; continue; }
    if (b0 < 0xc2) {
      *reason = "a UTF-8 lead byte 0x80-0xC1: a continuation byte, or an overlong two-byte form";
      return i;
    }
    if (b0 < 0xe0) {
      if (i + 1 >= len) { *reason = "a cut UTF-8 sequence"; return i; }
      if (cont_bits(p[i + 1]) < 0) { *reason = "a UTF-8 sequence without its continuation byte"; return i; }
      i += 2;
      continue;
    }
    if (b0 < 0xf0) {
      if (i + 2 >= len) { *reason = "a cut UTF-8 sequence"; return i; }
      int c1 = cont_bits(p[i + 1]), c2 = cont_bits(p[i + 2]);
      if (c1 < 0 || c2 < 0) { *reason = "a UTF-8 sequence without its continuation byte"; return i; }
      uint32_t cp = (uint32_t)(b0 - 0xe0) * 4096 + (uint32_t)c1 * 64 + (uint32_t)c2;
      if (cp < 0x800) { *reason = "an overlong three-byte UTF-8 form"; return i; }
      if (cp >= 0xd800 && cp <= 0xdfff) { *reason = "a UTF-8 surrogate"; return i; }
      i += 3;
      continue;
    }
    if (b0 < 0xf5) {
      if (i + 3 >= len) { *reason = "a cut UTF-8 sequence"; return i; }
      int c1 = cont_bits(p[i + 1]), c2 = cont_bits(p[i + 2]), c3 = cont_bits(p[i + 3]);
      if (c1 < 0 || c2 < 0 || c3 < 0) {
        *reason = "a UTF-8 sequence without its continuation byte";
        return i;
      }
      uint32_t cp = (uint32_t)(b0 - 0xf0) * 262144 + (uint32_t)c1 * 4096 + (uint32_t)c2 * 64 +
                    (uint32_t)c3;
      if (cp < 0x10000) { *reason = "an overlong four-byte UTF-8 form"; return i; }
      if (cp > 0x10ffff) { *reason = "a code point past U+10FFFF"; return i; }
      i += 4;
      continue;
    }
    *reason = "a UTF-8 lead byte 0xF5-0xFF";
    return i;
  }
  return len;
}

size_t e4_utf8_prefix(const uint8_t *p, size_t len) {
  const char *reason = NULL;
  return utf8_check(p, len, &reason);
}

/* ---- The reader ------------------------------------------------------------------------ */

typedef struct {
  e4_arena *arena;
  const uint8_t *base;
  e4_refusal *why;
  size_t depth;               /* the current nesting */
  size_t path[E4_PATH_MAX];
} reader;

static bool refuse(reader *r, const uint8_t *at, const char *reason) {
  e4_refusal *w = r->why;
  w->offset = (size_t)(at - r->base);
  w->depth = r->depth;
  size_t keep = r->depth < E4_PATH_MAX ? r->depth : E4_PATH_MAX;
  memcpy(w->path, r->path, keep * sizeof(size_t));
  w->reason = reason;
  return false;
}

/* `readFrame`: one frame off the front: the tag, the payload, the bytes consumed. */
static bool read_frame(reader *r, const uint8_t *p, size_t n, uint8_t *tag, e4_slice *payload,
                       size_t *consumed) {
  if (n == 0) return refuse(r, p, "no frame where one is due");
  if (n - 1 < 8) return refuse(r, p, "a frame header shorter than nine bytes");
  uint64_t len = be64_read(p + 1);
  if (len > (uint64_t)(n - 9)) return refuse(r, p, "a payload longer than the bytes left");
  *tag = p[0];
  payload->ptr = p + 9;
  payload->len = (size_t)len;
  *consumed = 9 + (size_t)len;
  return true;
}

static bool read_one(reader *r, const uint8_t *p, size_t n, e4_val *out, size_t *consumed);

static bool leading_zero(e4_slice s) { return s.len > 0 && s.ptr[0] == 0; }

/* `decodeSeq`: frames back to back until the bytes are used up. A first pass counts the frames by
   their headers; the second reads each. A child's extent is fixed by its header, as in Lean. */
static bool read_seq(reader *r, e4_slice s, e4_val **items, size_t *count) {
  size_t k = 0, at = 0;
  while (at < s.len) {
    uint8_t tag;
    e4_slice payload;
    size_t used;
    if (!read_frame(r, s.ptr + at, s.len - at, &tag, &payload, &used)) return false;
    at += used;
    k++;
  }
  e4_val *xs = k ? e4_arena_alloc(r->arena, k * sizeof(e4_val)) : NULL;
  at = 0;
  for (size_t i = 0; i < k; i++) {
    size_t used;
    if (r->depth < E4_PATH_MAX) r->path[r->depth] = i;
    r->depth++;
    bool ok = read_one(r, s.ptr + at, s.len - at, &xs[i], &used);
    r->depth--;
    if (!ok) return false;
    at += used;
  }
  *items = xs;
  *count = k;
  return true;
}

static bool read_child(reader *r, size_t position, const uint8_t *p, size_t n, e4_val **out,
                       size_t *used) {
  e4_val *v = e4_arena_alloc(r->arena, sizeof(e4_val));
  if (r->depth < E4_PATH_MAX) r->path[r->depth] = position;
  r->depth++;
  bool ok = read_one(r, p, n, v, used);
  r->depth--;
  *out = v;
  return ok;
}

/* `decodeBody`: one frame's payload read for its tag. */
static bool read_body(reader *r, uint8_t tag, e4_slice pl, e4_val *out) {
  out->tag = tag;
  switch (tag) {
  case E4_UNIT:
    return pl.len == 0 || refuse(r, pl.ptr, "a payload under unit");
  case E4_BOOL:
    if (pl.len != 1 || pl.ptr[0] > 1)
      return refuse(r, pl.ptr, "a boolean payload other than the one byte 0 or 1");
    out->as.b = pl.ptr[0] == 1;
    return true;
  case E4_NAT:
  case E4_INT:
    if (leading_zero(pl)) return refuse(r, pl.ptr, "a leading zero digit");
    out->as.digits = pl;
    return true;
  case E4_STRING: {
    const char *reason = NULL;
    size_t ok = utf8_check(pl.ptr, pl.len, &reason);
    if (ok != pl.len) return refuse(r, pl.ptr + ok, reason);
    out->as.str = pl;
    return true;
  }
  case E4_BYTES:
    out->as.bytes = pl;
    return true;
  case E4_LIST:
    return read_seq(r, pl, &out->as.list.items, &out->as.list.count);
  case E4_PAIR: {
    size_t u1, u2;
    if (pl.len == 0) return refuse(r, pl.ptr, "a pair payload with no frame");
    if (!read_child(r, 0, pl.ptr, pl.len, &out->as.pair.fst, &u1)) return false;
    if (u1 == pl.len) return refuse(r, pl.ptr + u1, "a pair payload with one frame");
    if (!read_child(r, 1, pl.ptr + u1, pl.len - u1, &out->as.pair.snd, &u2)) return false;
    if (u1 + u2 != pl.len) return refuse(r, pl.ptr + u1 + u2, "a pair payload with a third frame");
    return true;
  }
  case E4_NONE:
    return pl.len == 0 || refuse(r, pl.ptr, "a payload under none");
  case E4_SOME: {
    size_t u;
    if (pl.len == 0) return refuse(r, pl.ptr, "a some payload with no frame");
    if (!read_child(r, 0, pl.ptr, pl.len, &out->as.some, &u)) return false;
    if (u != pl.len) return refuse(r, pl.ptr + u, "a some payload with a second frame");
    return true;
  }
  case E4_CTOR: {
    uint8_t t;
    e4_slice digits;
    size_t u;
    if (!read_frame(r, pl.ptr, pl.len, &t, &digits, &u)) return false;
    if (t != E4_NAT) return refuse(r, pl.ptr, "a constructor index frame whose tag is not nat");
    if (leading_zero(digits)) return refuse(r, digits.ptr, "a leading zero digit in a constructor index");
    out->as.ctor.index = digits;
    e4_slice rest = {pl.ptr + u, pl.len - u};
    return read_seq(r, rest, &out->as.ctor.args, &out->as.ctor.count);
  }
  case E4_REF:
    if (pl.len == 0) return refuse(r, pl.ptr, "an empty ref payload");
    out->as.ref.kind = pl.ptr[0];
    out->as.ref.digest = (e4_slice){pl.ptr + 1, pl.len - 1};
    return true;
  case E4_HANDLE: {
    if (pl.len == 0) return refuse(r, pl.ptr, "an empty handle payload");
    e4_slice digits = {pl.ptr + 1, pl.len - 1};
    if (leading_zero(digits)) return refuse(r, digits.ptr, "a leading zero digit in a handle index");
    out->as.handle.kind = pl.ptr[0];
    out->as.handle.index = digits;
    return true;
  }
  case E4_FLOAT:
    if (pl.len != 8) return refuse(r, pl.ptr, "a binary64 payload that is not eight bytes");
    out->as.bits = be64_read(pl.ptr);
    if (!e4_float_frame(out->as.bits))
      return refuse(r, pl.ptr, "an integral double in the binary64 frame: its value is its integer image");
    return true;
  default:
    return refuse(r, pl.ptr - 9, "an unknown tag");
  }
}

/* `decodeOne`: one value off the front. The nesting limit stands where Lean's fuel stands. */
static bool read_one(reader *r, const uint8_t *p, size_t n, e4_val *out, size_t *consumed) {
  if (r->depth > E4_MAX_DEPTH) return refuse(r, p, "nesting deeper than the reader's limit E4_MAX_DEPTH");
  uint8_t tag;
  e4_slice payload;
  if (!read_frame(r, p, n, &tag, &payload, consumed)) return false;
  return read_body(r, tag, payload, out);
}

/* `Val.decode`: the whole input is one value and nothing else. */
e4_val *e4_decode(e4_arena *a, const uint8_t *in, size_t len, e4_refusal *why) {
  reader r = {.arena = a, .base = in, .why = why, .depth = 0};
  e4_val *v = e4_arena_alloc(a, sizeof(e4_val));
  size_t used;
  if (!read_one(&r, in, len, v, &used)) return NULL;
  if (used != len) { refuse(&r, in + used, "bytes after the value"); return NULL; }
  return v;
}

/* ---- The checker and the writer -------------------------------------------------------- */

typedef struct {
  e4_refusal *why;
  size_t depth;
  size_t path[E4_PATH_MAX];
} checker;

static const char *check_refuse(checker *c, const char *reason) {
  if (c->why) {
    c->why->offset = 0;
    c->why->depth = c->depth;
    size_t keep = c->depth < E4_PATH_MAX ? c->depth : E4_PATH_MAX;
    memcpy(c->why->path, c->path, keep * sizeof(size_t));
    c->why->reason = reason;
  }
  return reason;
}

static const char *check_at(checker *c, const e4_val *v);

static const char *check_child(checker *c, size_t position, const e4_val *v) {
  if (!v) return check_refuse(c, "a missing child");
  if (c->depth < E4_PATH_MAX) c->path[c->depth] = position;
  c->depth++;
  const char *bad = check_at(c, v);
  c->depth--;
  return bad;
}

static const char *check_items(checker *c, const e4_val *items, size_t count) {
  if (count && !items) return check_refuse(c, "a missing child array");
  for (size_t i = 0; i < count; i++) {
    const char *bad = check_child(c, i, &items[i]);
    if (bad) return bad;
  }
  return NULL;
}

static const char *check_at(checker *c, const e4_val *v) {
  switch (v->tag) {
  case E4_UNIT: case E4_NONE: case E4_BYTES: case E4_REF:
    return NULL;
  case E4_BOOL:
    return NULL;
  case E4_NAT: case E4_INT:
    return leading_zero(v->as.digits) ? check_refuse(c, "a natural with a leading zero digit") : NULL;
  case E4_STRING: {
    const char *reason = NULL;
    return utf8_check(v->as.str.ptr, v->as.str.len, &reason) == v->as.str.len
               ? NULL : check_refuse(c, reason);
  }
  case E4_LIST:
    return check_items(c, v->as.list.items, v->as.list.count);
  case E4_PAIR: {
    const char *bad = check_child(c, 0, v->as.pair.fst);
    return bad ? bad : check_child(c, 1, v->as.pair.snd);
  }
  case E4_SOME:
    return check_child(c, 0, v->as.some);
  case E4_CTOR:
    if (leading_zero(v->as.ctor.index)) return check_refuse(c, "a constructor index with a leading zero digit");
    return check_items(c, v->as.ctor.args, v->as.ctor.count);
  case E4_HANDLE:
    return leading_zero(v->as.handle.index) ? check_refuse(c, "a handle index with a leading zero digit") : NULL;
  case E4_FLOAT:
    return e4_float_frame(v->as.bits) ? NULL
               : check_refuse(c, "an integral double in the binary64 frame: its value is its integer image");
  default:
    return check_refuse(c, "an unknown tag");
  }
}

const char *e4_check(const e4_val *v, e4_refusal *why) {
  checker c = {.why = why, .depth = 0};
  return v ? check_at(&c, v) : check_refuse(&c, "a missing value");
}

static void write_one(const e4_val *v, e4_buf *out);

/* `framed`: the tag, the length after the payload is written, the payload. */
static size_t frame_open(e4_buf *out, uint8_t tag) {
  buf_byte(out, tag);
  size_t at = out->len;
  uint8_t zero[8] = {0};
  buf_append(out, zero, 8);
  return at;
}

static void frame_close(e4_buf *out, size_t at) {
  be64_write(out->ptr + at, (uint64_t)(out->len - at - 8));
}

static void write_slice_frame(e4_buf *out, uint8_t tag, e4_slice s) {
  size_t at = frame_open(out, tag);
  buf_append(out, s.ptr, s.len);
  frame_close(out, at);
}

/* `Val.encode`. */
static void write_one(const e4_val *v, e4_buf *out) {
  size_t at;
  switch (v->tag) {
  case E4_UNIT: case E4_NONE:
    at = frame_open(out, v->tag);
    frame_close(out, at);
    return;
  case E4_BOOL:
    at = frame_open(out, E4_BOOL);
    buf_byte(out, v->as.b ? 1 : 0);
    frame_close(out, at);
    return;
  case E4_NAT: case E4_INT:
    write_slice_frame(out, v->tag, v->as.digits);
    return;
  case E4_STRING:
    write_slice_frame(out, E4_STRING, v->as.str);
    return;
  case E4_BYTES:
    write_slice_frame(out, E4_BYTES, v->as.bytes);
    return;
  case E4_LIST:
    at = frame_open(out, E4_LIST);
    for (size_t i = 0; i < v->as.list.count; i++) write_one(&v->as.list.items[i], out);
    frame_close(out, at);
    return;
  case E4_PAIR:
    at = frame_open(out, E4_PAIR);
    write_one(v->as.pair.fst, out);
    write_one(v->as.pair.snd, out);
    frame_close(out, at);
    return;
  case E4_SOME:
    at = frame_open(out, E4_SOME);
    write_one(v->as.some, out);
    frame_close(out, at);
    return;
  case E4_CTOR:
    at = frame_open(out, E4_CTOR);
    write_slice_frame(out, E4_NAT, v->as.ctor.index);
    for (size_t i = 0; i < v->as.ctor.count; i++) write_one(&v->as.ctor.args[i], out);
    frame_close(out, at);
    return;
  case E4_REF:
    at = frame_open(out, E4_REF);
    buf_byte(out, v->as.ref.kind);
    buf_append(out, v->as.ref.digest.ptr, v->as.ref.digest.len);
    frame_close(out, at);
    return;
  case E4_HANDLE:
    at = frame_open(out, E4_HANDLE);
    buf_byte(out, v->as.handle.kind);
    buf_append(out, v->as.handle.index.ptr, v->as.handle.index.len);
    frame_close(out, at);
    return;
  case E4_FLOAT: {
    uint8_t p[8];
    be64_write(p, v->as.bits);
    at = frame_open(out, E4_FLOAT);
    buf_append(out, p, 8);
    frame_close(out, at);
    return;
  }
  }
}

/* `Val.encode?`: the bytes of a tree in the image; nothing otherwise. A payload's length is a
   size_t, so on a 64-bit target the condition `Val.WF` adds (every payload under 2^64) holds of
   every tree in memory. */
bool e4_encode(const e4_val *v, e4_buf *out, e4_refusal *why) {
  if (e4_check(v, why)) return false;
  write_one(v, out);
  return true;
}

/* ---- Equality -------------------------------------------------------------------------- */

static bool slice_eq(e4_slice x, e4_slice y) {
  return x.len == y.len && (x.len == 0 || memcmp(x.ptr, y.ptr, x.len) == 0);
}

static bool items_eq(const e4_val *xs, size_t m, const e4_val *ys, size_t n) {
  if (m != n) return false;
  for (size_t i = 0; i < m; i++)
    if (!e4_equal(&xs[i], &ys[i])) return false;
  return true;
}

bool e4_equal(const e4_val *x, const e4_val *y) {
  if (x->tag != y->tag) return false;
  switch (x->tag) {
  case E4_UNIT: case E4_NONE: return true;
  case E4_BOOL: return x->as.b == y->as.b;
  case E4_NAT: case E4_INT: return slice_eq(x->as.digits, y->as.digits);
  case E4_STRING: return slice_eq(x->as.str, y->as.str);
  case E4_BYTES: return slice_eq(x->as.bytes, y->as.bytes);
  case E4_LIST: return items_eq(x->as.list.items, x->as.list.count, y->as.list.items, y->as.list.count);
  case E4_PAIR: return e4_equal(x->as.pair.fst, y->as.pair.fst) && e4_equal(x->as.pair.snd, y->as.pair.snd);
  case E4_SOME: return e4_equal(x->as.some, y->as.some);
  case E4_CTOR:
    return slice_eq(x->as.ctor.index, y->as.ctor.index) &&
           items_eq(x->as.ctor.args, x->as.ctor.count, y->as.ctor.args, y->as.ctor.count);
  case E4_REF: return x->as.ref.kind == y->as.ref.kind && slice_eq(x->as.ref.digest, y->as.ref.digest);
  case E4_HANDLE:
    return x->as.handle.kind == y->as.handle.kind && slice_eq(x->as.handle.index, y->as.handle.index);
  case E4_FLOAT: return x->as.bits == y->as.bits;
  default: return false;
  }
}

/* ---- Rendering, as `Val.render` writes the value ---------------------------------------- */

/* A natural's digits in decimal, by repeated division of a copy. */
static void render_digits(e4_slice d, e4_buf *out) {
  if (d.len == 0) { buf_byte(out, '0'); return; }
  uint8_t *n = malloc(d.len);
  char *dec = malloc(d.len * 3 + 1);
  memcpy(n, d.ptr, d.len);
  size_t len = d.len, k = 0;
  while (len > 0) {
    unsigned rem = 0;
    for (size_t i = 0; i < len; i++) {
      unsigned cur = rem * 256 + n[i];
      n[i] = (uint8_t)(cur / 10);
      rem = cur % 10;
    }
    dec[k++] = (char)('0' + rem);
    size_t lead = 0;
    while (lead < len && n[lead] == 0) lead++;
    memmove(n, n + lead, len - lead);
    len -= lead;
  }
  while (k > 0) buf_byte(out, (uint8_t)dec[--k]);
  free(n);
  free(dec);
}

static void render_u64(uint64_t x, e4_buf *out) {
  char s[24];
  snprintf(s, sizeof s, "%llu", (unsigned long long)x);
  buf_str(out, s);
}

/* `String.quote`: `\n`, `\t`, `\\`, `\"`, and `\x` for a control character. */
static void render_quoted(e4_slice s, e4_buf *out) {
  static const char hexdig[] = "0123456789abcdef";
  buf_byte(out, '"');
  for (size_t i = 0; i < s.len; i++) {
    uint8_t c = s.ptr[i];
    if (c == '\n') buf_str(out, "\\n");
    else if (c == '\t') buf_str(out, "\\t");
    else if (c == '\\') buf_str(out, "\\\\");
    else if (c == '"') buf_str(out, "\\\"");
    else if (c <= 31 || c == 0x7f) {
      buf_str(out, "\\x");
      buf_byte(out, (uint8_t)hexdig[c >> 4]);
      buf_byte(out, (uint8_t)hexdig[c & 15]);
    } else buf_byte(out, c);
  }
  buf_byte(out, '"');
}

static void render_bytes(e4_slice s, e4_buf *out) {
  buf_byte(out, '[');
  for (size_t i = 0; i < s.len; i++) {
    if (i) buf_str(out, ", ");
    render_u64(s.ptr[i], out);
  }
  buf_byte(out, ']');
}

static void render_items(const e4_val *xs, size_t n, e4_buf *out) {
  buf_byte(out, '[');
  for (size_t i = 0; i < n; i++) {
    if (i) buf_str(out, ", ");
    e4_render(&xs[i], out);
  }
  buf_byte(out, ']');
}

void e4_render(const e4_val *v, e4_buf *out) {
  switch (v->tag) {
  case E4_UNIT: buf_str(out, "Val.unit"); return;
  case E4_NONE: buf_str(out, "Val.none"); return;
  case E4_BOOL: buf_str(out, v->as.b ? "(Val.bool true)" : "(Val.bool false)"); return;
  case E4_NAT: buf_str(out, "(Val.nat "); render_digits(v->as.digits, out); buf_byte(out, ')'); return;
  case E4_INT: buf_str(out, "(Val.negInt "); render_digits(v->as.digits, out); buf_byte(out, ')'); return;
  case E4_STRING: buf_str(out, "(Val.str "); render_quoted(v->as.str, out); buf_byte(out, ')'); return;
  case E4_BYTES: buf_str(out, "(Val.bytes "); render_bytes(v->as.bytes, out); buf_byte(out, ')'); return;
  case E4_LIST:
    buf_str(out, "(Val.list ");
    render_items(v->as.list.items, v->as.list.count, out);
    buf_byte(out, ')');
    return;
  case E4_PAIR:
    buf_str(out, "(Val.pair ");
    e4_render(v->as.pair.fst, out);
    buf_byte(out, ' ');
    e4_render(v->as.pair.snd, out);
    buf_byte(out, ')');
    return;
  case E4_SOME: buf_str(out, "(Val.some "); e4_render(v->as.some, out); buf_byte(out, ')'); return;
  case E4_CTOR:
    buf_str(out, "(Val.ctor ");
    render_digits(v->as.ctor.index, out);
    buf_byte(out, ' ');
    render_items(v->as.ctor.args, v->as.ctor.count, out);
    buf_byte(out, ')');
    return;
  case E4_REF:
    buf_str(out, "(Val.ref ");
    render_u64(v->as.ref.kind, out);
    buf_byte(out, ' ');
    render_bytes(v->as.ref.digest, out);
    buf_byte(out, ')');
    return;
  case E4_HANDLE:
    buf_str(out, "(Val.handle ");
    render_u64(v->as.handle.kind, out);
    buf_byte(out, ' ');
    render_digits(v->as.handle.index, out);
    buf_byte(out, ')');
    return;
  case E4_FLOAT: buf_str(out, "(Val.float "); render_u64(v->as.bits, out); buf_byte(out, ')'); return;
  default: buf_str(out, "(unknown tag)"); return;
  }
}

/* ---- Constructors ---------------------------------------------------------------------- */

static e4_val *mk(e4_arena *a, uint8_t tag) {
  e4_val *v = e4_arena_alloc(a, sizeof(e4_val));
  v->tag = tag;
  return v;
}

static e4_slice digits_u64(e4_arena *a, uint64_t n) {
  uint8_t tmp[8];
  size_t k = nat_bytes(tmp, n);
  uint8_t *p = e4_arena_alloc(a, 8);
  memcpy(p, tmp + 8 - k, k);
  return (e4_slice){p, k};
}

e4_val *e4_mk_unit(e4_arena *a) { return mk(a, E4_UNIT); }
e4_val *e4_mk_none(e4_arena *a) { return mk(a, E4_NONE); }

e4_val *e4_mk_bool(e4_arena *a, bool b) {
  e4_val *v = mk(a, E4_BOOL);
  v->as.b = b;
  return v;
}

e4_val *e4_mk_nat_u64(e4_arena *a, uint64_t n) {
  e4_val *v = mk(a, E4_NAT);
  v->as.digits = digits_u64(a, n);
  return v;
}

e4_val *e4_mk_str(e4_arena *a, const uint8_t *ptr, size_t len) {
  e4_val *v = mk(a, E4_STRING);
  v->as.str = (e4_slice){ptr, len};
  return v;
}

e4_val *e4_mk_some(e4_arena *a, e4_val *inner) {
  e4_val *v = mk(a, E4_SOME);
  v->as.some = inner;
  return v;
}

e4_val *e4_mk_pair(e4_arena *a, e4_val *fst, e4_val *snd) {
  e4_val *v = mk(a, E4_PAIR);
  v->as.pair.fst = fst;
  v->as.pair.snd = snd;
  return v;
}

e4_val *e4_mk_list(e4_arena *a, size_t count) {
  e4_val *v = mk(a, E4_LIST);
  v->as.list.count = count;
  v->as.list.items = count ? e4_arena_alloc(a, count * sizeof(e4_val)) : NULL;
  return v;
}

e4_val *e4_mk_ctor_u64(e4_arena *a, uint64_t index, size_t count) {
  e4_val *v = mk(a, E4_CTOR);
  v->as.ctor.index = digits_u64(a, index);
  v->as.ctor.count = count;
  v->as.ctor.args = count ? e4_arena_alloc(a, count * sizeof(e4_val)) : NULL;
  return v;
}

/* ---- Hexadecimal ----------------------------------------------------------------------- */

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

bool e4_unhex(const char *hex, size_t hexlen, e4_buf *out) {
  if (hexlen % 2) return false;
  buf_reserve(out, hexlen / 2);
  for (size_t i = 0; i < hexlen; i += 2) {
    int hi = hexval(hex[i]), lo = hexval(hex[i + 1]);
    if (hi < 0 || lo < 0) return false;
    out->ptr[out->len++] = (uint8_t)(hi * 16 + lo);
  }
  return true;
}

void e4_hex(const uint8_t *p, size_t len, e4_buf *out) {
  static const char hexdig[] = "0123456789abcdef";
  buf_reserve(out, len * 2);
  for (size_t i = 0; i < len; i++) {
    out->ptr[out->len++] = (uint8_t)hexdig[p[i] >> 4];
    out->ptr[out->len++] = (uint8_t)hexdig[p[i] & 15];
  }
}
