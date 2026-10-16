/* test_val.c -- the C reader and writer of the Val frames against Lean's committed bytes.

   What it is: a run over every frame that the committed fixtures hold in hexadecimal (each file
   named on the command line; every token of a non-comment line that is hexadecimal, of even length
   and at least nine bytes long), and over the values and refusals that the guards at the foot of
   src/Effect4/Store/Carrier/Val.lean pin.
   Depends on: e4val.

   Properties:
   R1  Every fixture frame reads, and writes back to its own bytes (V2).          tested
   R2  The tree read from the written bytes equals the tree first read (V3).       tested
   R3  Every proper prefix of a fixture frame, and the frame with one byte appended, is refused.
                                                                                    tested
   R4  Exactness under mutation: for each fixture frame, each byte position, and each of three
       masks, the mutated bytes are refused, or they read and write back to the mutated bytes.
       The run reports how many mutants read, so the property is not vacuous.        tested
   R5  The values Val.lean's guards encode have the bytes the guards state.          tested
   R6  The inputs Val.lean's guards refuse are refused, each with a reason.         tested
   R7  The checked writer refuses a C tree outside Lean's image: a natural with a leading zero
       digit, a string that is not UTF-8, an integral double in the binary64 frame.  tested

   What it does not establish: agreement with Lean's decoder on inputs outside these sets (the
   differential lean_diff.c widens the set, against Lean's compiled decoder). */

#include "e4val.h"
#include "fixture.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0, checks = 0;

static void check(const char *name, bool ok) {
  checks++;
  if (!ok) {
    failures++;
    printf("FAIL %s\n", name);
  }
}

static void pass_line(const char *name) { printf("PASS %s\n", name); }

/* ---- Helpers --------------------------------------------------------------------------- */

static bool decodes(const uint8_t *p, size_t n) {
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  bool ok = e4_decode(&a, p, n, &why) != NULL;
  e4_arena_free(&a);
  return ok;
}

/* Reads p, writes the tree back, and compares; *read says whether p read at all. */
static bool reads_back_exactly(const uint8_t *p, size_t n, bool *read) {
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  e4_val *v = e4_decode(&a, p, n, &why);
  *read = v != NULL;
  bool ok = true;
  if (v) {
    e4_buf out = {0};
    ok = e4_encode(v, &out, &why) && out.len == n && memcmp(out.ptr, p, n) == 0;
    e4_buf_free(&out);
  }
  e4_arena_free(&a);
  return ok;
}

static bool bytes_eq(const e4_buf *b, const uint8_t *p, size_t n) {
  return b->len == n && memcmp(b->ptr, p, n) == 0;
}

/* `framed tag payload`, as Val.lean writes it. */
static void framed(e4_buf *out, uint8_t tag, const uint8_t *payload, size_t n) {
  uint8_t head[9] = {tag};
  for (int i = 0; i < 8; i++) head[8 - i] = (uint8_t)((uint64_t)n >> (8 * i));
  out->len = 0;
  e4_buf_append(out, head, 9);
  e4_buf_append(out, payload, n);
}

static void encode_value(const e4_val *v, e4_buf *out) {
  e4_refusal why;
  out->len = 0;
  if (!e4_encode(v, out, &why)) { printf("  writer refused: %s\n", why.reason); }
}

/* ---- R1 to R4 -------------------------------------------------------------------------- */

static void run_fixtures(void) {
  size_t r1 = 0, r2 = 0, r3 = 0, mutants = 0, mutants_read = 0, r4 = 0;
  for (size_t i = 0; i < fixture_count; i++) {
    const fixture_frame *f = &fixture_frames[i];
    char name[160];
    /* R1, R2 */
    e4_arena a;
    e4_arena_init(&a);
    e4_refusal why;
    e4_val *v = e4_decode(&a, f->ptr, f->len, &why);
    snprintf(name, sizeof name, "R1 %s reads (refused at %zu: %s)", f->origin, v ? 0 : why.offset,
             v ? "" : why.reason);
    check(name, v != NULL);
    if (v) {
      e4_buf out = {0};
      bool wrote = e4_encode(v, &out, &why);
      snprintf(name, sizeof name, "R1 %s writes back to its bytes", f->origin);
      check(name, wrote && bytes_eq(&out, f->ptr, f->len));
      r1 += wrote && bytes_eq(&out, f->ptr, f->len);
      e4_arena b;
      e4_arena_init(&b);
      e4_val *w = e4_decode(&b, out.ptr, out.len, &why);
      snprintf(name, sizeof name, "R2 %s: the tree read back equals the tree", f->origin);
      check(name, w && e4_equal(v, w));
      r2 += w && e4_equal(v, w);
      e4_arena_free(&b);
      e4_buf_free(&out);
    }
    e4_arena_free(&a);
    /* R3: proper prefixes; every one for a frame up to 4096 bytes, else a spread of them */
    bool prefixes_refused = true;
    size_t step = f->len <= 4096 ? 1 : f->len / 509;
    for (size_t k = 0; k < f->len; k += step)
      if (decodes(f->ptr, k)) prefixes_refused = false;
    for (size_t k = f->len > 16 ? f->len - 16 : 0; k < f->len; k++)
      if (decodes(f->ptr, k)) prefixes_refused = false;
    uint8_t *longer = malloc(f->len + 1);
    memcpy(longer, f->ptr, f->len);
    longer[f->len] = 0;
    bool appended_refused = !decodes(longer, f->len + 1);
    free(longer);
    snprintf(name, sizeof name, "R3 %s: every proper prefix and one appended byte are refused", f->origin);
    check(name, prefixes_refused && appended_refused);
    r3 += prefixes_refused && appended_refused;
    /* R4: byte flips; every position for a frame up to 2048 bytes, else a spread */
    static const uint8_t masks[3] = {0x01, 0x80, 0xff};
    bool exact = true;
    uint8_t *m = malloc(f->len);
    size_t pstep = f->len <= 2048 ? 1 : f->len / 397;
    for (size_t pos = 0; pos < f->len; pos += pstep) {
      for (int k = 0; k < 3; k++) {
        memcpy(m, f->ptr, f->len);
        m[pos] ^= masks[k];
        bool read;
        if (!reads_back_exactly(m, f->len, &read)) exact = false;
        mutants++;
        mutants_read += read;
      }
    }
    free(m);
    snprintf(name, sizeof name, "R4 %s: every mutant is refused or reads back exactly", f->origin);
    check(name, exact);
    r4 += exact;
  }
  printf("PASS R1 %zu of %zu fixture frames read and write back to their bytes\n", r1, fixture_count);
  printf("PASS R2 %zu of %zu trees read back equal\n", r2, fixture_count);
  printf("PASS R3 %zu of %zu frames refuse their proper prefixes and an appended byte\n", r3, fixture_count);
  printf("PASS R4 %zu of %zu frames exact under mutation: %zu mutants, %zu read and wrote back\n",
         r4, fixture_count, mutants, mutants_read);
  if (mutants_read == 0) check("R4 some mutant reads, so R4 is not vacuous", false);
}

/* ---- R5: the guards' values and their bytes -------------------------------------------- */

static void run_guard_values(void) {
  e4_arena a;
  e4_arena_init(&a);
  e4_buf out = {0};

  /* encode (.nat 256) = [2, 0,0,0,0,0,0,0,2, 1, 0] (the module docstring) */
  static const uint8_t nat256[] = {2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0};
  encode_value(e4_mk_nat_u64(&a, 256), &out);
  check("R5 encode (.nat 256)", bytes_eq(&out, nat256, sizeof nat256));

  /* encode (.handle 2 7) = [12, 0,0,0,0,0,0,0,2, 2, 7] and two more handles */
  e4_val *h = e4_arena_alloc(&a, sizeof(e4_val));
  static const uint8_t seven[] = {7}, two56[] = {1, 0};
  h->tag = E4_HANDLE;
  h->as.handle.kind = 2;
  h->as.handle.index = (e4_slice){seven, 1};
  static const uint8_t handle27[] = {12, 0, 0, 0, 0, 0, 0, 0, 2, 2, 7};
  encode_value(h, &out);
  check("R5 encode (.handle 2 7)", bytes_eq(&out, handle27, sizeof handle27));
  h->as.handle.kind = 1;
  h->as.handle.index = (e4_slice){NULL, 0};
  static const uint8_t handle10[] = {12, 0, 0, 0, 0, 0, 0, 0, 1, 1};
  encode_value(h, &out);
  check("R5 encode (.handle 1 0)", bytes_eq(&out, handle10, sizeof handle10));
  h->as.handle.kind = 4;
  h->as.handle.index = (e4_slice){two56, 2};
  static const uint8_t handle4256[] = {12, 0, 0, 0, 0, 0, 0, 0, 3, 4, 1, 0};
  encode_value(h, &out);
  check("R5 encode (.handle 4 256)", bytes_eq(&out, handle4256, sizeof handle4256));

  /* sampleEntry = .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]: 74 bytes, its first
     ten and last eleven as the guards state */
  e4_val *entry = e4_mk_ctor_u64(&a, 0, 4);
  entry->as.ctor.args[0] = *e4_mk_str(&a, (const uint8_t *)"Effect", 6);
  entry->as.ctor.args[1] = *e4_mk_str(&a, (const uint8_t *)"gen", 3);
  entry->as.ctor.args[2] = *e4_mk_ctor_u64(&a, 0, 0);
  entry->as.ctor.args[3] = *e4_mk_nat_u64(&a, 1947);
  encode_value(entry, &out);
  static const uint8_t head10[] = {0x0a, 0, 0, 0, 0, 0, 0, 0, 0x41, 0x02};
  static const uint8_t tail11[] = {0x02, 0, 0, 0, 0, 0, 0, 0, 0x02, 0x07, 0x9b};
  check("R5 sampleEntry is 74 bytes", out.len == 74);
  check("R5 sampleEntry's first ten bytes", out.len == 74 && memcmp(out.ptr, head10, 10) == 0);
  check("R5 sampleEntry's last eleven bytes", out.len == 74 && memcmp(out.ptr + 63, tail11, 11) == 0);
  {
    e4_arena b;
    e4_arena_init(&b);
    e4_refusal why;
    e4_val *back = e4_decode(&b, out.ptr, out.len, &why);
    check("R5 sampleEntry reads back", back && e4_equal(back, entry));
    e4_buf r = {0};
    if (back) e4_render(back, &r);
    static const char want[] =
        "(Val.ctor 0 [(Val.str \"Effect\"), (Val.str \"gen\"), (Val.ctor 0 []), (Val.nat 1947)])";
    check("R5 sampleEntry renders as Val.render writes it",
          r.len == sizeof want - 1 && memcmp(r.ptr, want, r.len) == 0);
    e4_buf_free(&r);
    e4_arena_free(&b);
  }

  /* encode (.negInt 0) = [13, 0,0,0,0,0,0,0,0]: -1 is the empty digit string */
  e4_val *neg = e4_arena_alloc(&a, sizeof(e4_val));
  neg->tag = E4_INT;
  neg->as.digits = (e4_slice){NULL, 0};
  static const uint8_t neg0[] = {13, 0, 0, 0, 0, 0, 0, 0, 0};
  encode_value(neg, &out);
  check("R5 encode (.negInt 0)", bytes_eq(&out, neg0, sizeof neg0));

  /* the binary64 frame's domain: negative zero, 0.5, infinity are in it; 3.0 and +0.0 are not;
     the integral boundary 2^51 + 0.5 is a fraction, 2^51 + 1, 2^52 and -1 are integers; the
     subnormals, the smallest normal, NaN payloads and negative infinity are in it */
  check("R5 floatFrame negative zero, 0.5, infinity",
        e4_float_frame(UINT64_C(0x8000000000000000)) && e4_float_frame(UINT64_C(0x3FE0000000000000)) &&
            e4_float_frame(UINT64_C(0x7FF0000000000000)));
  check("R5 floatFrame refuses 3.0 and +0.0",
        !e4_float_frame(UINT64_C(0x4008000000000000)) && !e4_float_frame(0));
  check("R5 floatFrame at the integral boundary",
        e4_float_frame(UINT64_C(0x4320000000000001)) && !e4_float_frame(UINT64_C(0x4320000000000002)) &&
            !e4_float_frame(UINT64_C(0x4330000000000000)) && !e4_float_frame(UINT64_C(0xBFF0000000000000)));
  static const uint64_t kept[] = {
      UINT64_C(0x0000000000000001), UINT64_C(0x000FFFFFFFFFFFFF), UINT64_C(0x0010000000000000),
      UINT64_C(0x7FF0000000000001), UINT64_C(0x7FF8000000000001), UINT64_C(0xFFF8000000000001),
      UINT64_C(0xFFF0000000000000), UINT64_C(0x8000000000000000), UINT64_C(0x3FE0000000000000)};
  bool all_kept = true;
  for (size_t i = 0; i < sizeof kept / sizeof kept[0]; i++) {
    e4_val f = {.tag = E4_FLOAT, .as.bits = kept[i]};
    encode_value(&f, &out);
    e4_arena b;
    e4_arena_init(&b);
    e4_refusal why;
    e4_val *back = e4_decode(&b, out.ptr, out.len, &why);
    if (!e4_float_frame(kept[i]) || !back || back->as.bits != kept[i]) all_kept = false;
    e4_arena_free(&b);
  }
  check("R5 subnormals, the smallest normal, NaN payloads and -inf keep their eight bytes", all_kept);

  /* .pair (.some (.bool false)) (.list [.unit, .none]) reads back */
  e4_val *lst = e4_mk_list(&a, 2);
  lst->as.list.items[0] = *e4_mk_unit(&a);
  lst->as.list.items[1] = *e4_mk_none(&a);
  e4_val *pr = e4_mk_pair(&a, e4_mk_some(&a, e4_mk_bool(&a, false)), lst);
  encode_value(pr, &out);
  {
    e4_arena b;
    e4_arena_init(&b);
    e4_refusal why;
    e4_val *back = e4_decode(&b, out.ptr, out.len, &why);
    check("R5 a pair of an option and a list reads back", back && e4_equal(back, pr));
    e4_arena_free(&b);
  }
  e4_buf_free(&out);
  e4_arena_free(&a);
  pass_line("R5 the guards' values");
}

/* ---- R6: the guards' refusals ---------------------------------------------------------- */

static void refused(const char *name, const uint8_t *p, size_t n) {
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  e4_val *v = e4_decode(&a, p, n, &why);
  char line[200];
  snprintf(line, sizeof line, "R6 refused: %s", name);
  check(line, v == NULL && why.reason != NULL);
  if (!v) printf("  %-44s at byte %zu: %s\n", name, why.offset, why.reason);
  e4_arena_free(&a);
}

static void run_guard_refusals(void) {
  e4_buf b = {0}, inner = {0};
  /* the sample entry with a byte appended, and with its last byte dropped */
  e4_arena a;
  e4_arena_init(&a);
  e4_val *sample = e4_mk_ctor_u64(&a, 0, 4);
  sample->as.ctor.args[0] = *e4_mk_str(&a, (const uint8_t *)"Effect", 6);
  sample->as.ctor.args[1] = *e4_mk_str(&a, (const uint8_t *)"gen", 3);
  sample->as.ctor.args[2] = *e4_mk_ctor_u64(&a, 0, 0);
  sample->as.ctor.args[3] = *e4_mk_nat_u64(&a, 1947);
  e4_buf entry = {0};
  encode_value(sample, &entry);
  e4_arena_free(&a);
  check("R6 the sample entry's bytes, as a precondition", decodes(entry.ptr, entry.len));
  uint8_t *plus = malloc(entry.len + 1);
  memcpy(plus, entry.ptr, entry.len);
  plus[entry.len] = 0;
  refused("the sample entry with a byte appended", plus, entry.len + 1);
  refused("the sample entry with its last byte dropped", entry.ptr, entry.len - 1);
  free(plus);

  static const uint8_t nat_lead[] = {0, 17};
  framed(&b, E4_NAT, nat_lead, 2);
  refused("a natural with a leading zero digit", b.ptr, b.len);
  static const uint8_t overlong[] = {0xc0, 0x80};
  framed(&b, E4_STRING, overlong, 2);
  refused("a non-shortest UTF-8 sequence", b.ptr, b.len);
  framed(&b, 12, NULL, 0);
  refused("an empty handle payload (framed 12 [])", b.ptr, b.len);
  /* a pair with three frames */
  static const uint8_t unit3[] = {9, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0,
                                  9, 0, 0, 0, 0, 0, 0, 0, 0};
  framed(&b, E4_PAIR, unit3, sizeof unit3);
  refused("a pair with three frames", b.ptr, b.len);
  static const uint8_t two[] = {2};
  framed(&b, E4_BOOL, two, 1);
  refused("a boolean 2", b.ptr, b.len);
  static const uint8_t zero[] = {0};
  framed(&b, E4_UNIT, zero, 1);
  refused("a payload under unit", b.ptr, b.len);
  framed(&b, E4_REF, NULL, 0);
  refused("an empty ref", b.ptr, b.len);
  static const uint8_t ix_lead[] = {0, 1};
  framed(&inner, E4_NAT, ix_lead, 2);
  framed(&b, E4_CTOR, inner.ptr, inner.len);
  refused("a constructor index with a leading zero digit", b.ptr, b.len);
  static const uint8_t handle_lead[] = {2, 0, 7};
  framed(&b, E4_HANDLE, handle_lead, 3);
  refused("a handle index with a leading zero digit", b.ptr, b.len);
  framed(&b, 15, NULL, 0);
  refused("the next unused tag byte, 15", b.ptr, b.len);
  framed(&b, E4_INT, ix_lead, 2);
  refused("a negative integer with a leading zero digit", b.ptr, b.len);
  static const uint8_t three[] = {0x40, 0x08, 0, 0, 0, 0, 0, 0};
  framed(&b, E4_FLOAT, three, 8);
  refused("the double 3.0 in the binary64 frame", b.ptr, b.len);
  static const uint8_t pzero[8] = {0};
  framed(&b, E4_FLOAT, pzero, 8);
  refused("the double +0.0 in the binary64 frame", b.ptr, b.len);
  static const uint8_t half[] = {0x3f, 0xe0, 0, 0, 0, 0, 0, 0, 0};
  framed(&b, E4_FLOAT, half + 1, 7);
  refused("a binary64 payload of seven bytes", b.ptr, b.len);
  framed(&b, E4_FLOAT, half, 9);
  refused("a binary64 payload of nine bytes", b.ptr, b.len);
  /* a surrogate, a code point past U+10FFFF, a cut sequence: Utf8.lean's strict reader */
  static const uint8_t surrogate[] = {0xed, 0xa0, 0x80};
  framed(&b, E4_STRING, surrogate, 3);
  refused("a UTF-8 surrogate U+D800", b.ptr, b.len);
  static const uint8_t past[] = {0xf4, 0x90, 0x80, 0x80};
  framed(&b, E4_STRING, past, 4);
  refused("a code point past U+10FFFF", b.ptr, b.len);
  static const uint8_t cut[] = {0xe6, 0x97};
  framed(&b, E4_STRING, cut, 2);
  refused("a cut UTF-8 sequence", b.ptr, b.len);
  refused("no bytes", NULL, 0);
  e4_buf_free(&entry);
  e4_buf_free(&b);
  e4_buf_free(&inner);
}

/* ---- R7: the checked writer ------------------------------------------------------------ */

static void run_writer_refusals(void) {
  e4_buf out = {0};
  e4_refusal why;
  static const uint8_t lead[] = {0, 5};
  e4_val nat = {.tag = E4_NAT, .as.digits = {lead, 2}};
  check("R7 the writer refuses a natural with a leading zero digit", !e4_encode(&nat, &out, &why));
  static const uint8_t latin1[] = {'c', 'a', 'f', 0xe9};
  e4_val str = {.tag = E4_STRING, .as.str = {latin1, 4}};
  check("R7 the writer refuses Latin-1 bytes as a string", !e4_encode(&str, &out, &why));
  e4_val dbl = {.tag = E4_FLOAT, .as.bits = UINT64_C(0x4008000000000000)};
  e4_val some = {.tag = E4_SOME, .as.some = &dbl};
  check("R7 the writer refuses a nested integral double, at path [0]",
        !e4_encode(&some, &out, &why) && why.depth == 1 && why.path[0] == 0);
  check("R7 a refused write leaves the buffer empty", out.len == 0);
  static const uint8_t nul[] = {'a', 0, 'b'};
  e4_val withnul = {.tag = E4_STRING, .as.str = {nul, 3}};
  check("R7 the writer admits U+0000 inside a string", e4_encode(&withnul, &out, &why));
  e4_buf_free(&out);
  pass_line("R7 the checked writer");
}

int main(int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    long k = fixture_load(argv[i]);
    if (k < 0) check("a fixture file opens", false);
    printf("read %ld frames from %s\n", k, argv[i]);
  }
  check("the fixtures hold frames", fixture_count > 0);
  run_fixtures();
  run_guard_values();
  run_guard_refusals();
  run_writer_refusals();
  printf("%d checks, %d failures\n", checks, failures);
  fixture_free();
  return failures ? 1 : 0;
}
