# Seat W2: `effect4d`, a daemon for Effect programs and for Effect understanding

Status: 2026-09-04. Built at `workshop/OCaml5/server/`, protocol documented in
`workshop/OCaml5/server/README.md`. Nothing committed by this seat; nothing under
`workshop/OCaml5/avatar/`, `harness/`, `scripts/`, `generated/` or `lakefile.toml` written.

Everything below is what the coordinator reproduced or can reproduce with
`W2_AVATAR_REV=tree bash workshop/OCaml5/server/tests/run-tests.sh`.

---

## 1. Headline

The avatar is now a service. One OCaml executable, built for three hosts from one module
list, speaks newline-delimited JSON and answers 19 requests over the avatar's programs: run
them, step the machine, project under the estate's masks, diff two row lists by the estate's
own rule, and say for each row which avatar arm produced it and which Lean line that arm
cites.

- **14 677 checks pass** across bytecode, native and js_of_ocaml-under-node, on 60 programs
  per host (25 committed goldens, 9 `fiber` and 6 `extra` avatar faces, 20 corpus programs),
  plus TCP, a batch session, an OCaml library test and a node module test.
- **The three hosts agree on all 60 programs**, and every one matches the committed reference
  row for row, under all three masks and byte for byte.
- **The js_of_ocaml build is `require`-able from node** and runs forking, racing, parking
  programs from inside a JavaScript call — the case spike A0's probe C said would be
  `Unhandled` if the handler were installed outside the call. It is installed inside.
- Three findings fell out that are about the avatar, not the daemon: **drive fuel is not a
  monotone step counter**, the avatar's bare `:N` citations have **drifted 8 to 65 lines** from
  `Effect4/Deep/Fibers.lean`, and seat W1's checkpoint-1 store cases **carry no Lean
  citation** (§7).

---

## 2. The protocol

`README.md` is the specification; this is the shape.

One JSON object per line in, one per line out, in order. A response always carries
`protocol`, `ok`, `request`, `id`, `host`, and the golden header block both as TSV lines and
as an object — so a daemon answer can be written next to a `generated/traces/*.tsv` golden and
compared by the estate's own rule with no translation. `face` is `ocaml`, because the rows
*are* the avatar's.

The 19 requests, in the estate's `OpSpec` shape (`schema` answers them as data):

| group | requests |
| --- | --- |
| identity | `ping`, `version`, `pins`, `schema` |
| catalogue | `families`, `masks`, `programs`, `load`, `inspect` |
| running | `run`, `step` |
| understanding | `explain`, `why`, `reachable`, `budget` |
| comparison | `diff` |
| streaming | `pull`, `streams` |
| session | `reset` |

A program is named by `source`: `fixture` (the avatar's committed tables), `corpus` (the
adversarial DSL, by name or from a text the request carries), `golden` (a golden's own header
block, from which the program, tape and rules are read), or `loaded` (a `programId` from a
previous `load`).

Three transports, one loop: stdin/stdout on all three hosts, TCP on the POSIX ones (one
connection at a time, each its own session), and the library surface with no wire at all.

---

## 3. The stated behaviour

Per the user's ruling, every component states its behaviour up front. The list is
`README.md` §0, it is answered by the `schema` request as data, and each row carries how it
holds and the Lean theorem shape W4 would state over the same carrier.

| | property | how | theorem shape |
| --- | --- | --- | --- |
| W1 | a reply carries the request's `id` back | by construction | `(step s q).reply.id = q.id` |
| W2 | a replayed request with the same non-null `id` returns the recorded reply and changes nothing | by construction + tested | `q.id ≠ null → step (fst (step s q)) q = step s q` |
| W3 | replies in request order, one per request, per session | by construction + tested | `pump = List.foldl step` |
| W4 | at most **1** request in flight per session | by construction | no interleaving to state |
| W5 | the reply journal is bounded at **64** ids | by construction + tested | `‖journal s‖ ≤ 64` |
| R1 | `run` is deterministic in (program, tape, maxOps, fuel, rounds) | by construction + tested | `run p t b = run p t b` |
| R2 | `step` is prefix-closed in `rounds`, **not** in `fuel` | tested both ways | `rows (step p r) <+: rows (step p (r+1))` |
| R3 | `run` and `step` at full bounds agree up to the terminal row | by construction + tested | `rows (run p) = rows (step p full) ++ [terminal p]` |
| S1 | stream chunks are FIFO | by construction + tested | `pull s c = (s', Chunk _) → c = s.delivered ∧ s'.delivered = c+1` |
| S2 | at most once per chunk | by construction + tested | `delivered` monotone; `pull` refuses `c < delivered` |
| S3 | bounded buffer: **100 000** items, **8** open streams | by construction + tested | `‖s.chunks‖ · s.chunk_size ≤ 100000 ∧ ‖streams‖ ≤ 8` |
| S4 | back-pressure: nothing produced until pulled | by construction | `pull` is pure |
| S5 | every stream ends with an explicit `Halt` or `Fail` | by construction + tested | `∀ c ≥ ‖s.chunks‖, snd (pull s c) = Halt _` |

The machine is `Effect4_daemon.step : session -> request -> session * response`. No ambient
state, no clock, no randomness. The only mutable cell in the daemon is the `session ref` each
transport holds; `E4d_server_loop.pump` is a fold over the input lines and the TCP listener
builds a fresh session per connection.

The one exception, stated: **the avatar's own module-level state is not a parameter**. The
avatar is consumed read-only (seat W1 owns it), so `E4d_reset.all` clears it at the head of
every run instead. That is what makes R1 true rather than a hope, and it is what makes W4's
bound 1 rather than a choice.

Writing the properties first found a real protocol bug: `id` was both the request id and the
program handle, so every request naming a loaded program looked like a replay of the `load`
that minted it. The program handle is `programId` now.

---

## 4. The architecture

Thirteen modules, 4 779 lines including tests and generators. Five modules are **generated at
build time** so that nothing in an answer is a hand-made copy of something the estate already
states.

```
e4d_json.ml         a JSON value, parser, printer          -> Yojson at the swap
e4d_wire.ml         the trace wire: headers, row kinds, masks, projection, comparison
e4d_protocol.ml     the request/response carriers and codec -> deriving at the swap
e4d_stream.ml       streaming replies as a pull carrier (S1-S5)
e4d_alphabet.ml     the daemon's own OpSpec rows and the stated properties
e4d_server_loop.ml  the loop, with the transport as a parameter -> Eio at the swap
e4d_reset.ml        resetting the avatar's module-level state between requests
e4d_catalog.ml      the programs, and `inspect`
e4d_snapshot.ml     RunMachine as JSON, field for field
effect4_daemon.ml   the session, the state machine, every handler, the library surface
effect4d.ml         the POSIX transport (stdin/stdout, TCP)
effect4d_js.ml      the node transport, and the module exports
server_runtime.js   the four JavaScript externals of the jsoo build
```

Generated:

| module | from | what it carries |
| --- | --- | --- |
| `corpus_data.ml` | `avatar/corpus/programs.txt` | the corpus text, compiled in (no file to open under jsoo) |
| `e4d_masks_data.ml` | `generated/traces/masks.tsv`, `avatar/corpus/known-divergences.tsv` | the mask table and the classified divergences |
| `e4d_families_data.ml` | the committed `harness/trace/*fixture*.ts` | the five families' `OpSpec` rows, 34 operations |
| `e4d_armmap.ml` | every avatar module + every `Effect4/Deep/*.lean` | 131 dispatch cases, 32 row-name tables, 37 corpus step ops, 51 enclosing links, 23 Lean symbol resolutions, 108 handler docs with their citations |
| `e4d_pins.ml` | the avatar, the server, `masks.tsv`, `Fibers.lean` | the rc.112 pin and 29 per-file SHA-256 digests |

The module list *and its order* are read out of `avatar/build-avatar.sh`'s `modules=` line, so
a module seat W1 adds is compiled where the avatar says. That mattered within the hour:
alphabetical order would have put `deep_layer.ml` before `deep_stores.ml`, which does not
compile.

---

## 5. Counts

`W2_AVATAR_REV=tree bash workshop/OCaml5/server/tests/run-tests.sh`, against seat W1's working
tree (checkpoint 1 of the Deep port, with `deep_stores.ml` and `deep_layer.ml` split out):

```
the library surface, bytecode            PASS  0 failures  (13 checks)
the library surface, native              PASS  0 failures  (13 checks)
the js_of_ocaml build, as a node module  PASS  0 failures  (13 checks)
the protocol, bytecode                   60 programs
the protocol, native                     60 programs
the protocol, js_of_ocaml                60 programs
                                         14 677 checks, 0 failures
```

The 60 programs per host: **25 committed goldens** (`ref` 7, `deferred` 6, `scope` 4,
`layer` 8), **9 `fiber`** and **6 `extra`** programs against the avatar's committed faces, and
**20 corpus** programs against theirs.

What is asserted per program: the daemon's `run` rows equal the reference **byte for byte**,
and equal it **under each of the three masks** by the client's own independent transcription
of `compare.py`; the daemon's own `diff` agrees; `why` finds no divergence; `explain` gives
every service row a handler and reports an honest citation count; `step` returns a snapshot
with every carrier field at three round settings; `reachable` and `budget` answer; and the
response carries the golden's header fields with `face ocaml` and the rc.112 pin.

Cross-cutting: **`hosts-agree` on all 60 program names** (the three hosts' row lists are
identical), `determinism-in-one-session`, `batch-state-is-reset` (one node process, five
requests, the repeated program identical each time), `tcp-ok`, and the 17 property checks of
§3.

Citation coverage, per run, as the daemon reports it (`explain` → `citations`):

| program | service rows | with a handler | with a Lean site |
| --- | --- | --- | --- |
| `fiber.parentInterruptDuringChildWait` | 12 | 12 | 12 |
| `deferred.deferredSucceedAwait` | 6 | 6 | 4 |
| `layer.buildOnce` | 4 | 4 | 2 |
| `ref.makeGet` | 4 | 4 | 0 |
| `scope.lifo` | 10 | 10 | 0 |

Of the 32 citation tokens the avatar's handlers carry: 16 `exact`, 12 `byLine` (unverified),
4 `unresolved`.

---

## 6. What is exposed

**Running.** `run` (rows, projections per mask, outcome, the `RunEvent` trace, the whole TSV
ready to write next to a golden, and verdicts against an `expect`), `step` (a `RunMachine`
snapshot under a fuel or round bound), `diff` (the `compare.py` rule in OCaml, so the daemon
needs no python and works on the node host), `load`/`inspect`/`programs`/`families`/`masks`,
`version`/`pins`/`schema`.

**Understanding.** Four requests, all of them built from the same records the avatar uses —
nothing is hand-copied:

- `explain` — per row: the avatar handler (`arm_fork`, or `case Rref_make` for a dispatch case
  that pushes its own row), the effect constructors that reach it, its doc, its citations each
  resolved against every `Effect4/Deep/*.lean` module with file, line and enclosing
  declaration, the Lean declarations its doc names *by name*, and the `RunEvent`s in its
  bucket. Plus a count of how far the chain actually reached.
- `why` — given rc.112's rows, the first differing row under a mask, three rows of context on
  each side, the avatar's event trace up to it, the handlers of the differing row, and the
  entry from `known-divergences.tsv` if the program has one.
- `reachable` — per fiber: resumable and with which token, armed and how many tasks queued,
  what it is parked on (a fiber with the countdown remaining, a Deferred, a race, a countdown,
  a bare async), interruptible, interrupt pending, children, and the observers others hold on
  it.
- `budget` — the op counter and the yield injection points, per fiber and along the run, with
  the caveat that `currentOpCount` resets at every `Cmd.evaluate`.

**As a library.** `Effect4_daemon.run_program : program -> tape -> masks -> result` returns
the rows, the header, the projections, the events, the outcome and the avatar's own
`run_machine` — not a copy. `handle : Json -> Json` is the whole protocol without the wire.
`tests/lib_test.ml` exercises both on bytecode and native; `tests/node_module_demo.mjs`
exercises the same surface through `require("./effect4d.js")`.

**Streaming.** A `run` with `"chunk": n` hands the rows over as a pull stream instead of
inline. The carrier is data — a list of chunks, a terminator and a delivery mark, with
`pull : t -> int -> t * item` a total function of two first-order arguments — deliberately not
a closure, so its Lean counterpart is a list and an index. The shape mirrors rc.112's
`Channel` (`fromPull`, `transformPull`, `DefaultChunkSize`).

---

## 7. Three findings about the avatar

**(a) Drive fuel is not a monotone step counter.** `fiber.parentInterruptDuringChildWait` at
tape `0:0,1:0` emits 4 rows at fuel 1 and 2, **14 at fuel 3, 11 at fuel 4**, and 14 at fuel 5.
A nested `drive` inside `continue k` spends the same budget as its caller (the avatar's
DIVERGENCE 4), so a truncation at one point sends the run down a different path. `rounds` is
monotone; `fuel` is not. The daemon's row-to-event correlation checks this and refuses the
fuel scan when it fails, and `step` documents that a fuel-bounded snapshot is *a* reachable
state and not a prefix.

**(b) The avatar's bare `:N` citations have drifted.** They were written against
`workshop/Deep/Fibers.lean` before the promotion to `Effect4/Deep/`:

| the avatar cites | `Effect4/Deep/Fibers.lean` declares it at | drift |
| --- | --- | --- |
| `interruptRecord` `:550` | 558 | 8 |
| `countdownPark` `:576` | 584 | 8 |
| `spawn` `:622` | 631 | 9 |
| `exitFiber` `:992` | 1057 | 65 |
| `drive` `:1025` | 1090 | 65 |

(The right-hand column is what the daemon resolved on the run this report records; the Lean
file is under edit, and `exitFiber`/`drive` moved from 1031 to 1057 and 1064 to 1090 while
this was being written. That is the point: the daemon resolves the declaration by name every
build, so the drift is a number it reports rather than a number anyone maintains.)

The four- and five-digit citations (`:5264-5284`, `:5291`, `:859`) are rc.112
`internal/effect.ts` lines that the Lean file cites too, so those resolve exactly — the
daemon finds the Lean line by matching the citation token, not by trusting a number. This is
why `explain` reports `leanDeclarations` by *name* as well: a name survives an edit, a line
number does not. Path D of the state-and-paths doc lists "the OCaml5 docs' `workshop/Deep`
citations repointed to `Effect4/Deep`"; this is the same repoint, in the avatar's arm
comments, and it is measurable now.

**(c) The store cases carry no Lean citation.** Seat W1's checkpoint 1 moved the four store
families behind one `Op_store` carrying a `store_request`, and the cases (`case Rref_make`,
`case Rscope_close`, …) were moved unchanged — which means they carry the section banners they
had inside the `effc` table and no citation. `store_arm`, the function whose match they are
cases of, has none either. So a `ref` or `scope` run resolves its rows to an avatar handler
and no further: 0 of 4 for `ref.makeGet`, 0 of 10 for `scope.lifo`. `explain` reports the
number rather than implying the chain is complete. Giving each `store_request` case the
`Stores.lean` line it is the port of would take the `ref` and `scope` families from 0 to full
coverage with no change to the daemon.

---

## 8. Concurrency with seat W1

W1 restructured `deep_fibers.ml` under the daemon three times during the build. What made
that survivable:

1. `W2_AVATAR_REV` — `tree` (the working tree), a git revision, or unset, which tries the tree
   and falls back to `HEAD` with a loud message naming the failure. A build that silently used
   yesterday's avatar would be worse than one that says so.
2. The module list and order are read from `avatar/build-avatar.sh`'s own `modules=` line.
3. `tools/gen_armmap.py` reads *every* avatar module and finds handlers wherever they live, so
   the store arms moving from `deep_fibers.ml` to `deep_stores.ml` cost one generator change
   (a label is now either a named function or a dispatch case) and no table edit.
4. `e4d_snapshot.ml` compiles against the avatar's records, so a field that moves is a compile
   error and not a silently missing field.

The daemon's coupling to the avatar is three files and is listed in each: `e4d_reset.ml` (the
module-level state to clear, now largely W1's own `Deep_stores.store_reset` and
`Deep_layer.layers_reset`), `e4d_snapshot.ml` (the carriers to serialise) and
`effect4_daemon.ml`'s `reachable` (the Deferred store's waiter list). Everything else goes
through the avatar's public functions.

---

## 9. Representability: every construct, and its Lean counterpart

Per the user's ruling that everything must be directly representable in the Lean model, and
that each module should be something W3's `Ml.Check.profile` would admit.

| construct used | where | Lean counterpart, or the refusal |
| --- | --- | --- |
| plain records | `session`, `request`, `response`, `E4d_stream.t`, `E4d_wire.mask`, `E4d_alphabet.row` | `structure` |
| plain variants | `E4d_json.t`, `E4d_stream.item`, `outcome`, `E4d_wire.mask_verdict` | `inductive` |
| `list` | everywhere: rows, chunks, the journal, the session tables | `List` |
| association list | `session.loaded`, `session.streams`, `session.journal`, every generated table | `List (α × β)` with `List.lookup`. **Refusal row:** should be `Base.Map` once the switch exists, against W4's `workshop/OCaml5/Lib/Map.lean` as the Lean carrier; an association list is the same finite map with worse complexity and the same laws. |
| `option`, `result` | `tape_of`, `request_of_line`, `E4d_wire.mask_verdict` | `Option`, `Except` |
| `array` | `correlation.buckets`, `correlation.bucket_events` (index-addressed, built once) | `Array` / `List` with `List.get?` |
| `Printf.sprintf` | message text only, never a value | string append |
| exceptions | `Bad_request`, and catching `Failure`/`Stack_overflow` from the avatar | **Refusal row:** `Except` in the model. The daemon's own errors are one exception caught at exactly one place (`answer_request`); the avatar's are not the daemon's to remove. |
| one `ref` | the transport's `session ref` | **Stated, not refused:** the I/O shell of the ruling. `step` itself is `session -> request -> session * response`. |
| `Hashtbl` | never in a daemon module; read-only in `e4d_snapshot.ml` and `e4d_reset.ml` over the avatar's own tables | **Refusal row:** the avatar's, not the daemon's. `Deep_layer.layer_state` uses `Hashtbl`; the daemon folds over it and sorts, so its answers are order-stable. |
| closures | `E4d_server_loop.transport`'s three fields | **Refusal row:** a transport is I/O, at the outermost shell; the loop above it is a fold. Everything else in the daemon is first-order — the stream carrier is data with a `pull` function, not a `unit -> step`. |
| `Obj`, `Marshal`, functors, polymorphic compare on an abstract type | none | — |
| `Lazy` | `builtin_masks`, `builtin_corpus` (parse once) | a memoised total function; the value is the same either way |

Structural comparison (`=`) is used on `E4d_json.t`, `run_event list` and `string list`, all of
which are first-order concrete types where structural equality is the intended one.

---

## 10. What a "full suite" still lacks

Each is a stated item, not a claim.

1. **Authentication and authorisation.** None. The TCP listener binds `127.0.0.1` and accepts
   anything. There is no notion of a caller, a token or a permission.
2. **Transport security.** None. Plain TCP on loopback, plain pipes.
3. **Persistence.** None. The session dies with the process or the connection; nothing is
   written to disk, and there is no way to resume a session or to recover a `programId` after
   a restart.
4. **Streaming is pull-only and reply-only.** S1–S5 hold for a chunked reply. There is no
   server push, no cancellation of a request in flight, and no streaming *input* — a large
   corpus text still arrives as one line.
5. **Concurrency.** One request at a time, one connection at a time, and the reason is the
   avatar: its tape, row sink, stores and handle space are module-level. Until they are a
   parameter, a concurrent daemon would need a mutex around every run, which is the same bound
   with more machinery.
6. **Multi-program sessions in the machine sense.** `load` remembers programs, but `step`
   re-runs from the start under a larger bound rather than continuing a held machine. The
   continuations are ordinary OCaml one-shot continuations and would survive a request; the
   global state around them would not.
7. **The package swap.** The `effect4` opam switch of
   `docs/research/2026-09-04-ocaml-packages-plan.md` did not exist while this was built. The
   seams are cut and each names its replacement in its own header: `e4d_json.ml` → Yojson
   (the accessor API is a subset of `Yojson.Safe.Util` with the same names),
   `e4d_protocol.ml` → `[@@deriving sexp, bin_io, yojson]` on `request`/`response`,
   `e4d_server_loop.ml` → `Eio.Buf_read`/`Eio.Net` building the same `transport` record,
   `effect4d.ml` → `Core.Command`, `tests/` → `%expect`. No dune project yet: `build-server.sh`
   reads the avatar's module list dynamically, which a static `dune` stanza cannot, and the
   jsoo build needs `-no-check-prims` against a compiler that is not an opam package.
8. **`%expect` tests.** The protocol conformance tests are a python client (622 lines) rather
   than inline expect blocks, for the same reason. Every check it makes is one `[%expect]`
   block away once `ppx_expect` exists.
9. **No `fiber` golden in this checkout.** `generated/traces/` has no `fiber/` directory, so
   the nine fiber programs are checked against the avatar's own committed faces
   (`workshop/OCaml5/avatar/out/`) rather than against a Lean golden.
10. **The daemon adds no semantics, and inherits every gap.** The three classified divergences
    of `known-divergences.tsv` (`Fiber.awaitAll` argument order, the cross-dispatcher flush
    order, `raceAll` host interrupt) are the avatar's; `diff` and `why` report them by class
    and do not fix them.
11. **Row-to-event correlation is by replay.** `buckets: 1` means one bucket for the whole run.
    A hook in the avatar's `push_row` would make it exact; the avatar is read-only here.

---

## 11. What the next packet would do

1. **The switch, when it lands.** A dune project against `effect4`, `request`/`response` as
   derived carriers, the python client's checks as `%expect` blocks, `Core.Command`, `Eio` for
   the native loop. The four seams are cut and named.
2. **Cite the store cases** (§7c). One `Stores.lean` line per `store_request` case takes the
   `ref`, `scope` and `deferred` families from 0-of-N to full citation coverage, with no daemon
   change: the generator already reads whatever doc is there.
3. **Repoint the avatar's bare `:N` citations** (§7b) — 8 to 39 lines of drift, measurable now,
   and Path D of the state-and-paths doc already owns the repoint.
4. **Match W4's `Stream` carrier** when `workshop/OCaml5/Lib/` has one — at the time of this
   run it carries `Map.lean`, `Set.lean` and `Order.lean`, and no `Stream`. The daemon's is a
   record of `{ chunks : Json list; terminal : Json; delivered : int; finished : bool }` with
   `pull : t -> int -> t * item` and `item = Chunk | Halt | Fail`; S1–S5 are the laws it should
   satisfy.
5. **A gate face.** `check-trace-host.sh` could run the daemon's `run` over the committed
   goldens as a fourth face, stamped, which is A1 of the state-and-paths doc reached through
   the daemon instead of through `build-avatar.sh`.
