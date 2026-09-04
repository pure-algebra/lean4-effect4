/* e4_stubs.c — the C face of Bridge.lean, as OCaml externals.
 *
 * What it is: one C function per Lean export of `Bridge.lean` (`@[export e4_…]`), plus the
 * runtime entry points a host needs (module init, per-thread init/finalize, release).
 * Depends on: `lean/lean.h` (the Lean C ABI), `Bridge.o` and the Lean static libraries at
 * link time (`tools/lean-flags.sh` writes the flags), the OCaml 5 runtime headers.
 *
 * Properties (each `by construction` unless marked):
 *   C1  Ownership. A Lean export takes its `lean_object*` arguments OWNED. Every call that
 *       keeps the session alive on the OCaml side does `lean_inc` first; every string result
 *       is copied into the OCaml heap and the Lean string `lean_dec`'d. Strings cross by
 *       copy in both directions; the machine never crosses.
 *   C2  Release is explicit and idempotent. `caml_e4_release` drops the reference and nulls
 *       the pointer; the GC finalizer is then a no-op; any later use of a released session
 *       raises `Invalid_argument`, never touches freed memory. (tested: `bridge-release`)
 *   C3  No OCaml value is touched while the Lean call runs. Inputs are copied to C buffers
 *       first, the call runs inside `caml_enter/leave_blocking_section` (so a Lean step on
 *       one domain never stalls another domain's stop-the-world), and results are boxed
 *       after. The session pointer is a raw pointer, unaffected by the OCaml GC.
 *   C4  One Lean thread per OCaml domain. A worker domain calls `caml_e4_thread_init`
 *       (`lean_initialize_thread`: the thread-local heap) before its first Lean call and
 *       `caml_e4_thread_finalize` after its last; the main domain is initialized by
 *       `caml_e4_init`, exactly once (the second call is a no-op).
 *   C5  Decisions the Lean side does not parse are applied as the identity (`e4_step`
 *       returns the session unchanged): the OCaml side owns the decision grammar
 *       (`E4_bridge.to_wire`), so every wire string it produces is parsed.
 *   C6  The bytes path (`e4_program_hex`, `e4_load_hex`, `e4_name`) crosses as text only:
 *       hex in, hex out, the session's name out — same ownership and copying as C1, same
 *       blocking section as C3, same release as C2. `e4_load_hex` is total on the Lean
 *       side: bytes it will not run come back as a session NAMED `!refused:<reason>`, and
 *       the C face does not read that name — turning it into an error, and releasing the
 *       session so it can never be stepped, is `E4_bridge.load_hex`'s job (B7).
 *       (tested: bridge-hex-refuses, bridge-hex-tamper)
 */
#include <lean/lean.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/signals.h>
#include <string.h>
#include <stdlib.h>

/* The Lean side (Bridge.lean, `@[export …]`). */
extern lean_object* e4_program_names(lean_object* unit);
extern lean_object* e4_load(lean_object* name, uint32_t fuel);
extern lean_object* e4_step(lean_object* session, lean_object* decision, uint32_t fuel);
extern lean_object* e4_drive(lean_object* session, uint32_t fuel);
extern lean_object* e4_snapshot(lean_object* session);
extern lean_object* e4_armed(lean_object* session);
extern uint8_t      e4_finished(lean_object* session);
extern lean_object* e4_fibers(lean_object* session);
extern uint32_t     e4_trace_len(lean_object* session);
extern lean_object* e4_events(lean_object* session, uint32_t cursor);
/* The bytes path (C6): a program's canonical bytes as hex, a machine loaded from hex, and
 * the session's name (a table name, `bytes`, or `!refused:<reason>`). */
extern lean_object* e4_name(lean_object* session);
extern lean_object* e4_load_hex(lean_object* hex, uint32_t fuel);
extern lean_object* e4_program_hex(lean_object* name);

/* Module initializer emitted by Lean's C backend for `Bridge`, and the runtime entry
 * points. The two thread entries are exported by libleanrt (`nm` shows them as C symbols)
 * but not declared in lean.h, so they are declared here. */
extern lean_object* initialize_Bridge(uint8_t builtin, lean_object* w);
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

#define Session_val(v) (*((lean_object**) Data_custom_val(v)))

static void session_finalize(value v) {
  lean_object* s = Session_val(v);
  if (s != NULL) { Session_val(v) = NULL; lean_dec(s); }
}

static struct custom_operations session_ops = {
  "effect4.bridge.session", session_finalize, custom_compare_default,
  custom_hash_default, custom_serialize_default, custom_deserialize_default,
  custom_compare_ext_default, custom_fixed_length_default
};

static value box_session(lean_object* s) {
  value v = caml_alloc_custom(&session_ops, sizeof(lean_object*), 0, 1);
  Session_val(v) = s;
  return v;
}

/* The live pointer of a session, or an OCaml exception if it was released (C2). */
static lean_object* session_of(value v) {
  lean_object* s = Session_val(v);
  if (s == NULL) caml_invalid_argument("E4_bridge: session already released");
  return s;
}

/* An OCaml string as a fresh C buffer: the OCaml value is not touched afterwards (C3). */
static char* copy_string(value s) {
  size_t n = caml_string_length(s);
  char* buf = (char*) malloc(n + 1);
  if (buf == NULL) caml_raise_out_of_memory();
  memcpy(buf, String_val(s), n);
  buf[n] = '\0';
  return buf;
}

/* A Lean string as an OCaml string; the Lean string is consumed (C1). */
static value string_of_lean(lean_object* s) {
  value r = caml_copy_string(lean_string_cstr(s));
  lean_dec(s);
  return r;
}

static uint32_t fuel_of(value fuel) {
  long f = Long_val(fuel);
  if (f < 0 || f > 0xFFFFFFFFL) caml_invalid_argument("E4_bridge: fuel must fit in 32 bits");
  return (uint32_t) f;
}

/* ---- runtime ---- */

static int initialized = 0;

CAMLprim value caml_e4_init(value unit) {
  CAMLparam1(unit);
  if (!initialized) {
    initialized = 1;
    lean_initialize_runtime_module();
    lean_object* res = initialize_Bridge(1 /* builtin */, lean_io_mk_world());
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
    } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      caml_failwith("Lean module initialization failed");
    }
    lean_io_mark_end_initialization();
  }
  CAMLreturn(Val_unit);
}

CAMLprim value caml_e4_thread_init(value unit) {
  CAMLparam1(unit);
  lean_initialize_thread();
  CAMLreturn(Val_unit);
}

CAMLprim value caml_e4_thread_finalize(value unit) {
  CAMLparam1(unit);
  lean_finalize_thread();
  CAMLreturn(Val_unit);
}

/* ---- the exports ---- */

CAMLprim value caml_e4_program_names(value unit) {
  CAMLparam1(unit);
  CAMLreturn(string_of_lean(e4_program_names(lean_box(0))));
}

CAMLprim value caml_e4_load(value name, value fuel) {
  CAMLparam2(name, fuel);
  char* n = copy_string(name);
  uint32_t f = fuel_of(fuel);
  lean_object* s;
  caml_enter_blocking_section();
  s = e4_load(lean_mk_string(n), f);
  caml_leave_blocking_section();
  free(n);
  CAMLreturn(box_session(s));
}

CAMLprim value caml_e4_step(value session, value decision, value fuel) {
  CAMLparam3(session, decision, fuel);
  lean_object* s = session_of(session);
  char* d = copy_string(decision);
  uint32_t f = fuel_of(fuel);
  lean_object* s2;
  lean_inc(s);  /* e4_step consumes its argument; the OCaml block keeps its own reference */
  caml_enter_blocking_section();
  s2 = e4_step(s, lean_mk_string(d), f);
  caml_leave_blocking_section();
  free(d);
  CAMLreturn(box_session(s2));
}

CAMLprim value caml_e4_drive(value session, value fuel) {
  CAMLparam2(session, fuel);
  lean_object* s = session_of(session);
  uint32_t f = fuel_of(fuel);
  lean_object* s2;
  lean_inc(s);
  caml_enter_blocking_section();
  s2 = e4_drive(s, f);
  caml_leave_blocking_section();
  CAMLreturn(box_session(s2));
}

/* A string-valued projection of the session: inc, call, copy out. */
#define E4_STRING_PROJECTION(cname, lname)                    \
  CAMLprim value cname(value session) {                       \
    CAMLparam1(session);                                      \
    lean_object* s = session_of(session);                     \
    lean_object* r;                                           \
    lean_inc(s);                                              \
    caml_enter_blocking_section();                            \
    r = lname(s);                                             \
    caml_leave_blocking_section();                            \
    CAMLreturn(string_of_lean(r));                            \
  }

E4_STRING_PROJECTION(caml_e4_snapshot, e4_snapshot)
E4_STRING_PROJECTION(caml_e4_armed, e4_armed)
E4_STRING_PROJECTION(caml_e4_fibers, e4_fibers)
E4_STRING_PROJECTION(caml_e4_name, e4_name)

CAMLprim value caml_e4_finished(value session) {
  CAMLparam1(session);
  lean_object* s = session_of(session);
  uint8_t r;
  lean_inc(s);
  caml_enter_blocking_section();
  r = e4_finished(s);
  caml_leave_blocking_section();
  CAMLreturn(Val_bool(r != 0));
}

CAMLprim value caml_e4_trace_len(value session) {
  CAMLparam1(session);
  lean_object* s = session_of(session);
  uint32_t r;
  lean_inc(s);
  caml_enter_blocking_section();
  r = e4_trace_len(s);
  caml_leave_blocking_section();
  CAMLreturn(Val_long((long) r));
}

CAMLprim value caml_e4_events(value session, value cursor) {
  CAMLparam2(session, cursor);
  lean_object* s = session_of(session);
  long c = Long_val(cursor);
  if (c < 0 || c > 0xFFFFFFFFL) caml_invalid_argument("E4_bridge: cursor must fit in 32 bits");
  lean_object* r;
  lean_inc(s);
  caml_enter_blocking_section();
  r = e4_events(s, (uint32_t) c);
  caml_leave_blocking_section();
  CAMLreturn(string_of_lean(r));
}

/* ---- the bytes path (C6) ---- */

/* The canonical bytes of a table program as hex; the Lean side answers "" for a name the
 * table lacks. A string in, a string out — no session is involved. */
CAMLprim value caml_e4_program_hex(value name) {
  CAMLparam1(name);
  char* n = copy_string(name);
  lean_object* r;
  caml_enter_blocking_section();
  r = e4_program_hex(lean_mk_string(n));
  caml_leave_blocking_section();
  free(n);
  CAMLreturn(string_of_lean(r));
}

/* A machine from a program's canonical bytes (hex). Total on the Lean side: bytes it
 * refuses come back as a session named `!refused:<reason>` holding p42's machine, which
 * `E4_bridge.load_hex` releases rather than hand out (B7). */
CAMLprim value caml_e4_load_hex(value hex, value fuel) {
  CAMLparam2(hex, fuel);
  char* h = copy_string(hex);
  uint32_t f = fuel_of(fuel);
  lean_object* s;
  caml_enter_blocking_section();
  s = e4_load_hex(lean_mk_string(h), f);
  caml_leave_blocking_section();
  free(h);
  CAMLreturn(box_session(s));
}

/* ---- release (C2) ---- */

CAMLprim value caml_e4_release(value session) {
  CAMLparam1(session);
  lean_object* s = Session_val(session);
  if (s != NULL) { Session_val(session) = NULL; lean_dec(s); }
  CAMLreturn(Val_unit);
}

CAMLprim value caml_e4_is_released(value session) {
  CAMLparam1(session);
  CAMLreturn(Val_bool(Session_val(session) == NULL));
}
