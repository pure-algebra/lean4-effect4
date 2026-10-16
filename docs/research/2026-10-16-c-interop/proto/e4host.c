/* e4host.c -- a C host over the Val wire frames. The header e4host.h carries the property list. */

#include "e4host.h"

#include <stdlib.h>
#include <string.h>

/* ---- The method layer ------------------------------------------------------------------ */

static e4_answer declined(const char *reason) {
  e4_answer a = {.status = E4_DECLINED, .value = NULL};
  a.why.reason = reason;
  return a;
}

e4_answer e4_serve(const e4_method *methods, size_t count, void *host, e4_slice row,
                   const e4_val *request, e4_arena *arena) {
  for (size_t i = 0; i < count; i++) {
    size_t n = strlen(methods[i].spelling);
    if (n == row.len && memcmp(methods[i].spelling, row.ptr, n) == 0)
      return methods[i].answer(host, request, arena);
  }
  return declined("no method answers this row");
}

e4_status e4_serve_bytes(const e4_method *methods, size_t count, void *host, e4_slice row,
                         const uint8_t *request, size_t request_len, e4_buf *answer,
                         e4_refusal *why) {
  e4_arena a;
  e4_arena_init(&a);
  e4_status status = E4_DECLINED;
  e4_val *req = e4_decode(&a, request, request_len, why);
  if (req) {
    e4_answer ans = e4_serve(methods, count, host, row, req, &a);
    if (ans.status == E4_DECLINED) *why = ans.why;
    else if (!e4_encode(ans.value, answer, why)) status = E4_DECLINED;
    else status = ans.status;
  }
  e4_arena_free(&a);
  return status;
}

/* ---- Reading helpers: each refusal names its reason; the caller's path is the field's ---- */

static bool refuse(e4_refusal *why, size_t field, const char *reason) {
  why->offset = 0;
  why->depth = 1;
  why->path[0] = field;
  why->reason = reason;
  return false;
}

static bool is_str(const e4_val *v, const char *s) {
  size_t n = strlen(s);
  return v->tag == E4_STRING && v->as.str.len == n && memcmp(v->as.str.ptr, s, n) == 0;
}

/* A natural as uint64_t: the C type's range is [0, 2^64), a refusal outside it (H4). */
static bool read_u64(const e4_val *v, uint64_t *out, e4_refusal *why, size_t field) {
  if (v->tag != E4_NAT) return refuse(why, field, "a value where a natural stands");
  if (!e4_nat_u64(v->as.digits, out))
    return refuse(why, field, "a natural past uint64_t: outside the C profile's range");
  return true;
}

/* ---- The to-do codecs: the staged image of `Todo`, written as a deriver would ----------- */

/* The field names in canonical order: "done" < "id" < "title" by their UTF-8 bytes. */
static const char *const todo_names[3] = {"done", "id", "title"};

e4_val *todo_write(e4_arena *a, const todo_t *t) {
  e4_val *rec = e4_mk_ctor_u64(a, 0, 2);
  e4_val *names = &rec->as.ctor.args[0];
  e4_val *values = &rec->as.ctor.args[1];
  *names = *e4_mk_list(a, 3);
  for (int i = 0; i < 3; i++)
    names->as.list.items[i] = *e4_mk_str(a, (const uint8_t *)todo_names[i], strlen(todo_names[i]));
  *values = *e4_mk_list(a, 3);
  values->as.list.items[0] = *e4_mk_bool(a, t->done);
  values->as.list.items[1] = *e4_mk_nat_u64(a, t->id);
  values->as.list.items[2] = *e4_mk_str(a, t->title.ptr, t->title.len);
  return rec;
}

bool todo_read(const e4_val *v, todo_t *out, e4_refusal *why) {
  if (v->tag != E4_CTOR || v->as.ctor.index.len != 0 || v->as.ctor.count != 2)
    return refuse(why, 0, "not a record frame: ctor 0 [names, values]");
  const e4_val *names = &v->as.ctor.args[0], *values = &v->as.ctor.args[1];
  if (names->tag != E4_LIST || names->as.list.count != 3)
    return refuse(why, 0, "a record whose names are not the three of Todo");
  for (int i = 0; i < 3; i++)
    if (!is_str(&names->as.list.items[i], todo_names[i]))
      return refuse(why, 0, "a record whose names are not done, id, title in canonical order");
  if (values->tag != E4_LIST || values->as.list.count != 3)
    return refuse(why, 1, "a record with other than three values");
  const e4_val *d = &values->as.list.items[0], *id = &values->as.list.items[1],
               *title = &values->as.list.items[2];
  if (d->tag != E4_BOOL) return refuse(why, 1, "a value where the Bool `done` stands");
  if (!read_u64(id, &out->id, why, 1)) return false;
  if (title->tag != E4_STRING) return refuse(why, 1, "a value where the String `title` stands");
  out->done = d->as.b;
  out->title = title->as.str;
  return true;
}

/* `SqlTag × String`: the enum's code is `lit "SqlError"`, whose value is the string; a pair of
   two leaves is the two-element list that `errOf` reads as `Err.tagged` (src/Effect4/Machine/
   Term.lean). */
e4_val *sql_error_write(e4_arena *a, const sql_error_t *e) {
  e4_val *v = e4_mk_list(a, 2);
  v->as.list.items[0] = *e4_mk_str(a, (const uint8_t *)"SqlError", 8);
  v->as.list.items[1] = *e4_mk_str(a, e->message.ptr, e->message.len);
  return v;
}

/* ---- The adapter: `Reactor.fallible` per row -------------------------------------------- */

static e4_answer failed(e4_arena *a, const sql_error_t *err) {
  return (e4_answer){.status = E4_FAILURE, .value = sql_error_write(a, err)};
}

static e4_answer succeeded(e4_val *v) { return (e4_answer){.status = E4_SUCCESS, .value = v}; }

/* TodoRepo.insert : String → Todo */
static e4_answer m_insert(void *host, const e4_val *req, e4_arena *a) {
  const todo_bound *h = host;
  if (req->tag != E4_STRING) return declined("insert: a request that is not a String");
  todo_t ok;
  sql_error_t err;
  if (h->vtable->insert(h->self, req->as.str, &ok, &err) == TODO_ERROR) return failed(a, &err);
  return succeeded(todo_write(a, &ok));
}

/* TodoRepo.all : Unit → List Todo */
static e4_answer m_all(void *host, const e4_val *req, e4_arena *a) {
  const todo_bound *h = host;
  if (req->tag != E4_UNIT) return declined("all: a request that is not Unit");
  todo_t *items = NULL;
  size_t count = 0;
  sql_error_t err;
  if (h->vtable->all(h->self, a, &items, &count, &err) == TODO_ERROR) return failed(a, &err);
  e4_val *list = e4_mk_list(a, count);
  for (size_t i = 0; i < count; i++) list->as.list.items[i] = *todo_write(a, &items[i]);
  return succeeded(list);
}

/* TodoRepo.setDone : Nat × Bool → Option Todo */
static e4_answer m_set_done(void *host, const e4_val *req, e4_arena *a) {
  const todo_bound *h = host;
  e4_answer no = declined("setDone: a request that is not a pair of a Nat and a Bool");
  if (req->tag != E4_LIST || req->as.list.count != 2) return no;
  uint64_t id;
  if (!read_u64(&req->as.list.items[0], &id, &no.why, 0)) return no;
  if (req->as.list.items[1].tag != E4_BOOL) return no;
  bool found = false;
  todo_t ok;
  sql_error_t err;
  if (h->vtable->set_done(h->self, id, req->as.list.items[1].as.b, &found, &ok, &err) == TODO_ERROR)
    return failed(a, &err);
  return succeeded(found ? e4_mk_some(a, todo_write(a, &ok)) : e4_mk_none(a));
}

/* TodoRepo.delete : Nat → Bool */
static e4_answer m_remove(void *host, const e4_val *req, e4_arena *a) {
  const todo_bound *h = host;
  e4_answer no = declined("delete: a request that is not a Nat");
  uint64_t id;
  if (!read_u64(req, &id, &no.why, 0)) return no;
  bool existed = false;
  sql_error_t err;
  if (h->vtable->remove(h->self, id, &existed, &err) == TODO_ERROR) return failed(a, &err);
  return succeeded(e4_mk_bool(a, existed));
}

const e4_method todo_methods[4] = {
    {"TodoRepo.insert", m_insert},
    {"TodoRepo.all", m_all},
    {"TodoRepo.setDone", m_set_done},
    {"TodoRepo.delete", m_remove},
};

/* ---- The repository written in C ------------------------------------------------------- */

void repo_init(repo_t *r, uint64_t next) {
  r->next = next;
  r->items = NULL;
  r->count = r->cap = 0;
}

void repo_free(repo_t *r) {
  for (size_t i = 0; i < r->count; i++) free(r->items[i].title);
  free(r->items);
  repo_init(r, 0);
}

void repo_push(repo_t *r, uint64_t id, const uint8_t *title, size_t len, bool done) {
  if (r->count == r->cap) {
    r->cap = r->cap ? r->cap * 2 : 8;
    r->items = realloc(r->items, r->cap * sizeof(repo_item));
  }
  repo_item *it = &r->items[r->count++];
  it->id = id;
  it->title = malloc(len ? len : 1);
  if (len) memcpy(it->title, title, len);
  it->title_len = len;
  it->done = done;
}

static todo_t todo_of(const repo_item *it) {
  return (todo_t){.id = it->id, .title = {it->title, it->title_len}, .done = it->done};
}

/* `Typed.model`: insert appends (next, title, false) and answers it. */
static todo_result model_insert(void *self, e4_slice title, todo_t *ok, sql_error_t *err) {
  (void)err;
  repo_t *r = self;
  repo_push(r, r->next, title.ptr, title.len, false);
  *ok = todo_of(&r->items[r->count - 1]);
  r->next++;
  return TODO_OK;
}

static todo_result model_all(void *self, e4_arena *a, todo_t **items, size_t *count, sql_error_t *err) {
  (void)err;
  repo_t *r = self;
  *count = r->count;
  *items = r->count ? e4_arena_alloc(a, r->count * sizeof(todo_t)) : NULL;
  for (size_t i = 0; i < r->count; i++) (*items)[i] = todo_of(&r->items[i]);
  return TODO_OK;
}

static todo_result model_set_done(void *self, uint64_t id, bool done, bool *found, todo_t *ok,
                                  sql_error_t *err) {
  (void)err;
  repo_t *r = self;
  *found = false;
  for (size_t i = 0; i < r->count; i++) {
    if (r->items[i].id == id) {
      if (!*found) *ok = (todo_t){.id = id, .title = {r->items[i].title, r->items[i].title_len}, .done = done};
      *found = true;
      r->items[i].done = done;
    }
  }
  return TODO_OK;
}

static todo_result model_remove(void *self, uint64_t id, bool *existed, sql_error_t *err) {
  (void)err;
  repo_t *r = self;
  size_t kept = 0;
  *existed = false;
  for (size_t i = 0; i < r->count; i++) {
    if (r->items[i].id == id) {
      *existed = true;
      free(r->items[i].title);
    } else r->items[kept++] = r->items[i];
  }
  r->count = kept;
  return TODO_OK;
}

static todo_result broken_insert(void *self, e4_slice title, todo_t *ok, sql_error_t *err) {
  (void)self;
  (void)title;
  (void)ok;
  static const char disk_full[] = "disk full";
  err->message = (e4_slice){(const uint8_t *)disk_full, sizeof disk_full - 1};
  return TODO_ERROR;
}

const todo_host repo_model = {model_insert, model_all, model_set_done, model_remove};
const todo_host repo_broken = {broken_insert, model_all, model_set_done, model_remove};

/* ---- The repository's state as `repoVal` writes it ------------------------------------- */

e4_val *repo_write(e4_arena *a, const repo_t *r) {
  e4_val *v = e4_mk_list(a, 2);
  v->as.list.items[0] = *e4_mk_nat_u64(a, r->next);
  e4_val *items = &v->as.list.items[1];
  *items = *e4_mk_list(a, r->count);
  for (size_t i = 0; i < r->count; i++) {
    e4_val *row = &items->as.list.items[i];
    *row = *e4_mk_list(a, 3);
    row->as.list.items[0] = *e4_mk_nat_u64(a, r->items[i].id);
    row->as.list.items[1] = *e4_mk_str(a, r->items[i].title, r->items[i].title_len);
    row->as.list.items[2] = *e4_mk_bool(a, r->items[i].done);
  }
  return v;
}

bool repo_read(const e4_val *v, repo_t *out, e4_refusal *why) {
  if (v->tag != E4_LIST || v->as.list.count != 2) return refuse(why, 0, "a state that is not [next, items]");
  uint64_t next;
  if (!read_u64(&v->as.list.items[0], &next, why, 0)) return false;
  const e4_val *items = &v->as.list.items[1];
  if (items->tag != E4_LIST) return refuse(why, 1, "items that are not a list");
  repo_init(out, next);
  for (size_t i = 0; i < items->as.list.count; i++) {
    const e4_val *row = &items->as.list.items[i];
    uint64_t id;
    if (row->tag != E4_LIST || row->as.list.count != 3 || !read_u64(&row->as.list.items[0], &id, why, 1) ||
        row->as.list.items[1].tag != E4_STRING || row->as.list.items[2].tag != E4_BOOL) {
      repo_free(out);
      return refuse(why, 1, "an item that is not [id, title, done]");
    }
    repo_push(out, id, row->as.list.items[1].as.str.ptr, row->as.list.items[1].as.str.len,
              row->as.list.items[2].as.b);
  }
  return true;
}
