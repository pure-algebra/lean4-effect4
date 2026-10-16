/* e4host.h -- a C host: a provider of a row table, whose methods read requests and write answers
   through the Val wire frames.

   What it is: the C reading of `Run.Reactor` (src/Effect4/Run/Basic.lean) and of the typed host
   of decisions row 405 (`Reactor.method`, `Reactor.fallible`, `Reactor.first`,
   src/Effect4/Run/Method.lean). Two layers:

   * The method layer (untyped): a host is a table of methods, one per row spelling. A method takes
     the request as a value tree and answers a success value, a failure's error value, or declines.
     `e4_serve` is `Reactor.first`; `e4_serve_bytes` is the same at the byte boundary.
   * The typed layer: a host written against native C types (here the to-do repository's four rows
     over `todo_t`), and the codecs that a C deriver of `Modeled` would write from each type's
     staged image. The adapter reads each request by its codec and declines a request that does not
     read, as `Reactor.method` does; it writes each answer by its codec.

   Properties:
   H1  A method answers its row only; any other row, and a request that does not read, is
       declined, never guessed.                                     by construction, and tested
   H2  The to-do host's answers, packaged as the lane packages them (`answerVal`,
       Test/Dogfood/Scenario/Todo/HostRun.lean), are Lean's bytes for each recorded call of
       ocaml/engine/test/todo/todo-host.txt, and its state after each request is Lean's.  tested
   H3  The broken host (insert fails with the rows' error) gives Lean's bytes for `Typed.broken`.
                                                                                          tested
   H4  The C types are narrower than Lean's at one place: an id is a `uint64_t`. A request whose
       natural passes 2^64 - 1 does not read, so the C host declines where Lean's model answers.
       This is a profile-support refusal (row 108), located at the field.            tested

   What it does not establish: the run. The machine is Lean's; the test answers the calls that
   Lean's run recorded, in order, and compares the answers and the state. The completion that
   wraps an answer (`.ofExit (.success v)`, `.ofExit (.failure (Cause.fail (errOf v)))`) is the
   session's to build; test_host.c builds the lane's packaging of it for the comparison. */

#ifndef E4HOST_H
#define E4HOST_H

#include "e4val.h"

/* ---- The method layer ------------------------------------------------------------------ */

typedef enum { E4_DECLINED = 0, E4_SUCCESS = 1, E4_FAILURE = 2 } e4_status;

typedef struct {
  e4_status status;
  e4_val *value;          /* the success value, or the failure's error value; NULL if declined */
  e4_refusal why;         /* when declined: why the request did not read */
} e4_answer;

/* One method: the row it answers, and the function over values. `host` is the provider's state,
   which the method may change: a C host keeps its state in place, where Lean's reactor threads
   `σ`. */
typedef struct {
  const char *spelling;
  e4_answer (*answer)(void *host, const e4_val *request, e4_arena *arena);
} e4_method;

/* `Reactor.first`: the first method whose spelling is the row's answers; none declines. */
e4_answer e4_serve(const e4_method *methods, size_t count, void *host, e4_slice row,
                   const e4_val *request, e4_arena *arena);

/* The same at the byte boundary: the request's frames in, the answer's frames out. A request
   whose bytes do not read is declined with the reader's refusal. */
e4_status e4_serve_bytes(const e4_method *methods, size_t count, void *host, e4_slice row,
                         const uint8_t *request, size_t request_len, e4_buf *answer,
                         e4_refusal *why);

/* ---- The typed layer: the to-do repository (Test/Dogfood/Scenario/Todo/Typed.lean) -------- */

/* `Todo`: the record { done : Bool, id : Nat, title : String }. Its value is the record frame,
   `ctor 0 [list names, list values]`, the names in canonical (UTF-8 byte) order (row 165 (a)).
   C narrows `id` to uint64_t (H4); `title` borrows its bytes. */
typedef struct {
  uint64_t id;
  e4_slice title;
  bool done;
} todo_t;

/* `SqlError := SqlTag × String`: a one-constructor enum (code `lit "SqlError"`) and a message. */
typedef struct {
  e4_slice message;
} sql_error_t;

typedef enum { TODO_OK = 0, TODO_ERROR = 1 } todo_result;

/* `Typed.Host σ`: one function per row of `TodoRepo`, over native types. A list answer is
   allocated in the arena given. */
typedef struct {
  todo_result (*insert)(void *self, e4_slice title, todo_t *ok, sql_error_t *err);
  todo_result (*all)(void *self, e4_arena *arena, todo_t **items, size_t *count, sql_error_t *err);
  todo_result (*set_done)(void *self, uint64_t id, bool done, bool *found, todo_t *ok,
                          sql_error_t *err);
  todo_result (*remove)(void *self, uint64_t id, bool *existed, sql_error_t *err);
} todo_host;

/* A typed host bound to its state: what the adapter's methods receive as `host`. */
typedef struct {
  const todo_host *vtable;
  void *self;
} todo_bound;

/* The row table of the typed host: four methods, `Host.reactor`'s order. */
extern const e4_method todo_methods[4];

/* The codecs a C deriver of `Modeled` would write from the staged images. Each reader is exact:
   it accepts only the writer's image, and refuses anything else with a located reason. */
e4_val *todo_write(e4_arena *a, const todo_t *t);
bool todo_read(const e4_val *v, todo_t *out, e4_refusal *why);
e4_val *sql_error_write(e4_arena *a, const sql_error_t *e);

/* ---- A native provider: the repository written in C ------------------------------------ */

typedef struct {
  uint64_t id;
  uint8_t *title;       /* owned copy */
  size_t title_len;
  bool done;
} repo_item;

typedef struct {
  uint64_t next;
  repo_item *items;
  size_t count, cap;
} repo_t;

void repo_init(repo_t *r, uint64_t next);
void repo_free(repo_t *r);
void repo_push(repo_t *r, uint64_t id, const uint8_t *title, size_t len, bool done);

/* The reference model (`Typed.model`) and the broken one (`Typed.broken`), over repo_t. */
extern const todo_host repo_model;
extern const todo_host repo_broken;

/* The repository's state as `repoVal` writes it: [next, [[id, title, done], ...]]. */
e4_val *repo_write(e4_arena *a, const repo_t *r);
bool repo_read(const e4_val *v, repo_t *out, e4_refusal *why);

#endif
