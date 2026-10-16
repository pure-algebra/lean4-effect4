/* test_host.c -- the C host against Lean's to-do host run (ocaml/engine/test/todo/todo-host.txt).

   What it is: for each request block of the fixture, the C repository starts from the block's
   `state`, answers each call that Lean's run recorded in `result` (row, request), through the byte
   entry `e4_serve_bytes`, and the test compares the C answer, packaged as the lane packages it
   (`answerVal`, Test/Dogfood/Scenario/Todo/HostRun.lean), with Lean's bytes. Then it compares the
   C repository's state with Lean's next state, as `repoVal` writes it. The C host plays the role
   of test_todo.ml's T11 (a typed host written in the native language) and T13 (its broken twin).
   Depends on: e4host, e4val.

   Properties:
   C1  The C model's answer to every recorded call is Lean's, byte for byte, and its state after
       each request is Lean's (H2).                                                   tested
   C2  The fixture's `answer` line (the first call's success value) is the C model's first answer,
       byte for byte.                                                                 tested
   C3  The broken C host gives Lean's `broken` result on every request (H3).          tested
   C4  Red control: the forgetful repository's result differs from the C model's on some request,
       so C1 compares values that tell hosts apart.                                   tested
   C5  A request that does not read is declined, as `Typed.model`'s reactor declines it (H1).
                                                                                       tested
   C6  An id past uint64_t is declined with a located refusal at the field (H4).      tested

   What it does not establish: the run, which is Lean's; the root's exit, which is the machine's. */

#define _POSIX_C_SOURCE 200809L
#include "e4host.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0, checks = 0;

static void check(const char *name, bool ok) {
  checks++;
  printf("%s %s\n", ok ? "PASS" : "FAIL", name);
  if (!ok) failures++;
}

/* ---- The fixture ----------------------------------------------------------------------- */

typedef struct {
  char entry[32];
  e4_buf names, state, result, broken, forgetful, answer;
  bool has_answer;
} block;

static block blocks[32];
static size_t nblocks = 0;

static void read_fixture(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) { printf("FAIL cannot open %s\n", path); exit(1); }
  char *line = NULL;
  size_t cap = 0;
  ssize_t got;
  block *cur = NULL;
  while ((got = getline(&line, &cap, f)) > 0) {
    if (line[0] == '#') continue;
    line[strcspn(line, "\r\n")] = 0;
    char *sp = strchr(line, ' ');
    if (!sp) continue;
    *sp = 0;
    char *rest = sp + 1;
    char *end = strchr(rest, ' ');
    size_t n = end ? (size_t)(end - rest) : strlen(rest);
    if (strcmp(line, "request") == 0) {
      if (nblocks == sizeof blocks / sizeof blocks[0]) break;
      cur = &blocks[nblocks++];
      memset(cur, 0, sizeof *cur);
      snprintf(cur->entry, sizeof cur->entry, "%s", rest);
      continue;
    }
    if (!cur) continue;
    e4_buf *into = NULL;
    if (strcmp(line, "names") == 0) into = &cur->names;
    else if (strcmp(line, "state") == 0) into = &cur->state;
    else if (strcmp(line, "result") == 0) into = &cur->result;
    else if (strcmp(line, "broken") == 0) into = &cur->broken;
    else if (strcmp(line, "forgetful") == 0) into = &cur->forgetful;
    else if (strcmp(line, "answer") == 0) { into = &cur->answer; cur->has_answer = true; }
    if (into && !e4_unhex(rest, n, into)) { printf("FAIL not hexadecimal: %s\n", line); failures++; }
  }
  free(line);
  fclose(f);
}

/* ---- The lane's packaging of an answer ------------------------------------------------- */

/* `answerVal (.ofExit exit)` = [0, exitImage exit]; `exitImage` writes `success v` as
   `ctor 0 [v]` and `failure c` as `ctor 1 [causeImage c]` (src/Effect4/Machine/Alphabets.lean).
   The failure a typed method writes is `Cause.fail (errOf v)` (src/Effect4/Run/Method.lean): one
   reason, `ctor 0 [errImage, ctor 0 [list []]]` with no annotation, under the cause's `ctor 0
   [list reasons]`. `errOf` reads the two-string list as `Err.tagged`, constructor 2. Only that
   error shape is packaged here; it is the one the rows' error column writes. */
static e4_val *answer_val(e4_arena *a, e4_status status, e4_val *v) {
  e4_val *out = e4_mk_list(a, 2);
  out->as.list.items[0] = *e4_mk_nat_u64(a, 0);
  e4_val *exit;
  if (status == E4_SUCCESS) {
    exit = e4_mk_ctor_u64(a, 0, 1);
    exit->as.ctor.args[0] = *v;
  } else {
    if (v->tag != E4_LIST || v->as.list.count != 2) return NULL;
    e4_val *err = e4_mk_ctor_u64(a, 2, 2);
    err->as.ctor.args[0] = v->as.list.items[0];
    err->as.ctor.args[1] = v->as.list.items[1];
    e4_val *annotations = e4_mk_ctor_u64(a, 0, 1);
    annotations->as.ctor.args[0] = *e4_mk_list(a, 0);
    e4_val *reason = e4_mk_ctor_u64(a, 0, 2);
    reason->as.ctor.args[0] = *err;
    reason->as.ctor.args[1] = *annotations;
    e4_val *reasons = e4_mk_list(a, 1);
    reasons->as.list.items[0] = *reason;
    e4_val *cause = e4_mk_ctor_u64(a, 0, 1);
    cause->as.ctor.args[0] = *reasons;
    exit = e4_mk_ctor_u64(a, 1, 1);
    exit->as.ctor.args[0] = *cause;
  }
  out->as.list.items[1] = *exit;
  return out;
}

static bool same_bytes(const e4_val *x, const e4_val *y) {
  e4_buf bx = {0}, by = {0};
  e4_refusal why;
  bool ok = e4_encode(x, &bx, &why) && e4_encode(y, &by, &why) && bx.len == by.len &&
            memcmp(bx.ptr, by.ptr, bx.len) == 0;
  e4_buf_free(&bx);
  e4_buf_free(&by);
  return ok;
}

/* ---- One request, over one host -------------------------------------------------------- */

typedef struct {
  bool answers_match;   /* every recorded call answered with Lean's bytes */
  bool state_matches;   /* the C state after the request is Lean's */
  e4_buf first;         /* the first answer's frames, when it succeeded */
} outcome;

static outcome run_block(const block *b, const todo_host *vtable, const e4_buf *expected) {
  outcome o = {.answers_match = true, .state_matches = false};
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  e4_val *names = e4_decode(&a, b->names.ptr, b->names.len, &why);
  e4_val *state = e4_decode(&a, b->state.ptr, b->state.len, &why);
  e4_val *result = e4_decode(&a, expected->ptr, expected->len, &why);
  repo_t repo;
  if (!names || !state || !result || !repo_read(state, &repo, &why)) {
    o.answers_match = false;
    e4_arena_free(&a);
    return o;
  }
  todo_bound bound = {vtable, &repo};
  const e4_val *calls = &result->as.list.items[0];
  for (size_t i = 0; i < calls->as.list.count; i++) {
    const e4_val *call = &calls->as.list.items[i];
    uint64_t row = 0;
    e4_nat_u64(call->as.list.items[0].as.digits, &row);
    const e4_val *spelling = &names->as.list.items[row].as.list.items[0];
    e4_buf req = {0}, ans = {0};
    e4_encode(&call->as.list.items[1], &req, &why);
    e4_status status = e4_serve_bytes(todo_methods, 4, &bound, spelling->as.str, req.ptr, req.len,
                                      &ans, &why);
    bool match = false;
    if (status != E4_DECLINED) {
      e4_val *v = e4_decode(&a, ans.ptr, ans.len, &why);
      e4_val *packaged = v ? answer_val(&a, status, v) : NULL;
      match = packaged && same_bytes(packaged, &call->as.list.items[2]);
      if (i == 0 && status == E4_SUCCESS) e4_buf_append(&o.first, ans.ptr, ans.len);
    }
    if (!match) o.answers_match = false;
    e4_buf_free(&req);
    e4_buf_free(&ans);
  }
  o.state_matches = same_bytes(repo_write(&a, &repo), &result->as.list.items[2]);
  repo_free(&repo);
  e4_arena_free(&a);
  return o;
}

/* ---- The declines ---------------------------------------------------------------------- */

static void run_declines(void) {
  repo_t repo;
  repo_init(&repo, 3);
  repo_push(&repo, 1, (const uint8_t *)"milk", 4, false);
  todo_bound bound = {&repo_model, &repo};
  e4_arena a;
  e4_arena_init(&a);
  e4_refusal why;
  e4_buf req = {0}, ans = {0};

  /* C5: `model.reactor row (.nat 3)` declines insert (Typed.lean's control) */
  e4_encode(e4_mk_nat_u64(&a, 3), &req, &why);
  e4_slice insert = {(const uint8_t *)"TodoRepo.insert", 15};
  e4_status s = e4_serve_bytes(todo_methods, 4, &bound, insert, req.ptr, req.len, &ans, &why);
  check("C5 insert declines a natural, as Typed.model's reactor does", s == E4_DECLINED && ans.len == 0);
  e4_slice other = {(const uint8_t *)"TodoRepo.rename", 15};
  s = e4_serve_bytes(todo_methods, 4, &bound, other, req.ptr, req.len, &ans, &why);
  check("C5 a row with no method is declined", s == E4_DECLINED);
  check("C5 a decline changes no state", repo.next == 3 && repo.count == 1);

  /* C6: setDone [2^64, true]: Lean's model answers `none`; the C host declines at the field */
  static const uint8_t two64[] = {1, 0, 0, 0, 0, 0, 0, 0, 0};
  e4_val *big = e4_arena_alloc(&a, sizeof(e4_val));
  big->tag = E4_NAT;
  big->as.digits = (e4_slice){two64, sizeof two64};
  e4_val *pair = e4_mk_list(&a, 2);
  pair->as.list.items[0] = *big;
  pair->as.list.items[1] = *e4_mk_bool(&a, true);
  req.len = 0;
  e4_encode(pair, &req, &why);
  e4_slice set_done = {(const uint8_t *)"TodoRepo.setDone", 16};
  s = e4_serve_bytes(todo_methods, 4, &bound, set_done, req.ptr, req.len, &ans, &why);
  printf("  setDone [2^64, true]: declined at path [%zu]: %s\n", why.path[0], why.reason);
  check("C6 an id past uint64_t is declined, located at field 0",
        s == E4_DECLINED && why.depth == 1 && why.path[0] == 0);
  /* and 2^64 - 1 still reads: the range is exactly [0, 2^64) */
  static const uint8_t max64[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
  pair->as.list.items[0].as.digits = (e4_slice){max64, sizeof max64};
  req.len = 0;
  e4_encode(pair, &req, &why);
  s = e4_serve_bytes(todo_methods, 4, &bound, set_done, req.ptr, req.len, &ans, &why);
  check("C6 the id 2^64 - 1 reads, and setDone answers none", s == E4_SUCCESS && ans.len == 9 &&
        ans.ptr[0] == E4_NONE);
  e4_buf_free(&req);
  e4_buf_free(&ans);
  e4_arena_free(&a);
  repo_free(&repo);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: test_host todo-host.txt\n"); return 2; }
  read_fixture(argv[1]);
  char name[160];
  snprintf(name, sizeof name, "the fixture holds %zu requests", nblocks);
  check(name, nblocks > 0);
  bool forgetful_differs = false;
  for (size_t i = 0; i < nblocks; i++) {
    const block *b = &blocks[i];
    outcome m = run_block(b, &repo_model, &b->result);
    snprintf(name, sizeof name, "C1 %zu %s: every recorded call answered with Lean's bytes", i, b->entry);
    check(name, m.answers_match);
    snprintf(name, sizeof name, "C1 %zu %s: the C state after the request is Lean's", i, b->entry);
    check(name, m.state_matches);
    if (b->has_answer) {
      snprintf(name, sizeof name, "C2 %zu %s: the first answer is the fixture's answer line", i, b->entry);
      check(name, m.first.len == b->answer.len && memcmp(m.first.ptr, b->answer.ptr, m.first.len) == 0);
    }
    e4_buf_free(&m.first);
    outcome k = run_block(b, &repo_broken, &b->broken);
    snprintf(name, sizeof name, "C3 %zu %s: the broken C host gives Lean's broken result", i, b->entry);
    check(name, k.answers_match && k.state_matches);
    e4_buf_free(&k.first);
    outcome f = run_block(b, &repo_model, &b->forgetful);
    if (!f.answers_match || !f.state_matches) forgetful_differs = true;
    e4_buf_free(&f.first);
  }
  check("C4 red control: the forgetful repository's result differs from the C model's on some request",
        forgetful_differs);
  run_declines();
  printf("%d checks, %d failures\n", checks, failures);
  for (size_t i = 0; i < nblocks; i++) {
    e4_buf_free(&blocks[i].names);
    e4_buf_free(&blocks[i].state);
    e4_buf_free(&blocks[i].result);
    e4_buf_free(&blocks[i].broken);
    e4_buf_free(&blocks[i].forgetful);
    e4_buf_free(&blocks[i].answer);
  }
  return failures ? 1 : 0;
}
