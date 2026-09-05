# `effect4d` — a daemon for Effect programs, and for understanding them

`effect4d` is one OCaml executable that runs Effect programs on the avatar
(`ocaml/avatar/`, the OCaml 5 transcription of `src/Effect4/Machine/*.lean`, called
`src/Effect4/Machine/*.lean` until "Prod cleanup 3") and answers questions about the runs, over
newline-delimited JSON.

It is built for three hosts from one module list:

| host | artefact | run it |
| --- | --- | --- |
| bytecode | `effect4d.byte` | `ocamlrun effect4d.byte` |
| native | `effect4d.native` | `./effect4d.native` |
| js_of_ocaml `--enable effects` | `effect4d.js` | `node effect4d.js`, or `require("./effect4d.js")` |

All three speak the same protocol and produce the same rows. The js_of_ocaml build is also a
node module: `require("./effect4d.js")` returns `{ request, runProgram, version, families,
programs }`.

```
tools/dune-build.sh                    # all three hosts, with dune, into ocaml/_build
tools/dune-test.sh                     # build, then every test on every host this machine reaches
```

The build is dune's since 2026-09-04: `BUILD-DUNE.md` is the account (what changed from
the earlier shell build, the generated modules, the archived inputs). The two
superseded shell build/test drivers were retired on 2026-09-05. The avatar is not
copied into this directory: `effect4d_lib` links the avatar's own library by its public name
`effect4-avatar`, and dune compiles those fifteen modules once (BUILD-DUNE.md §4).

---

## 0. The behaviour, stated

These are the properties the daemon holds itself to. Each says how it holds — `by
construction` or `tested` — and each is answered by the `schema` request, so a caller reads
them off the daemon rather than off this file. The Lean theorem shape beside each is what
would be stated over the same carrier once `src/OCaml5/Lib/` has one.

### The wire

| | property | how |
| --- | --- | --- |
| **W1** | Every request may carry an `id`, of any JSON type. The reply carries the same `id` back, unchanged; a request with no `id` gets `null`. | by construction (`E4d_protocol`) |
| **W2** | At-least-once delivery is safe. A request replayed with the same non-null `id` in the same session returns **the recorded reply** and leaves the session unchanged — so a client that retries on a dropped connection cannot mint two program handles or consume two stream chunks. | by construction (the session's reply journal); tested (`W2-replay-is-identical`, `W2-a-new-id-is-a-new-request`) |
| **W3** | Replies are in request order, one per request, per session. | by construction (`E4d_server_loop.pump` is a fold over the input lines); tested (`W3-replies-in-order`) |
| **W4** | **At most one request is in flight per session; the bound is 1.** The loop reads a request, answers it, and only then reads the next. The TCP listener accepts one connection at a time, and each connection is its own session. | by construction |
| **W5** | The reply journal is bounded at **64** ids per session, most recent kept. A replay older than that is answered afresh — safe for every request except `load`, which mints a new handle. | by construction; tested (`W5-journal-is-bounded`) |

The state machine behind these is `Effect4_daemon.step : session -> request -> session *
response`. It has no ambient state, no clock and no randomness; the only mutable cell in the
daemon is the `session ref` each transport holds.

### Running

| | property | how |
| --- | --- | --- |
| **R1** | `run` is deterministic in `(program, tape, maxOps, fuel, rounds)`: the same request twice gives byte-identical rows, events and outcome, in the same process and across the three hosts. The avatar's module-level state is reset at the head of every run (`e4d_reset.ml`). | by construction; tested (`determinism-in-one-session`, `hosts-agree` on 60 programs × 3 hosts, `batch-state-is-reset`) |
| **R2** | `step` snapshots are **prefix-closed in `rounds`**: the rows at `r` rounds are a prefix of the rows at `r+1`. They are **not** prefix-closed in `fuel`. | tested both ways (`R2-step-prefix-closed-in-rounds`, `R2-fuel-is-not-monotone-as-documented`) |
| **R3** | A `run` and a `step` at full bounds agree on the rows, up to the terminal row `run` appends. | by construction (one `execute`); tested |

R2's counterexample is worth stating in full, because it is a property of the avatar and not
of the daemon: `fiber.parentInterruptDuringChildWait` at tape `0:0,1:0` emits **4 rows at fuel
1 and 2, 14 at fuel 3, 11 at fuel 4, and 14 at fuel 5**. A nested `drive` inside `continue k`
spends the same budget as its caller (the avatar's DIVERGENCE 4), so a truncation at one point
sends the run down a different path. Read a `fuel`-bounded snapshot as *a* reachable state,
not as a prefix of the full run.

### Streaming

| | property | how |
| --- | --- | --- |
| **S1** | FIFO. A stream's chunks arrive in index order and in no other: `pull` accepts only the cursor the stream is at. | by construction (`E4d_stream.pull`); tested (`S1-fifo`, `S1-first-chunk-is-zero`) |
| **S2** | At most once per chunk. The delivery mark only increases, and a cursor below it is `chunk-already-delivered`. | by construction; tested (`S2-at-most-once-per-chunk`) |
| **S3** | Bounded buffer. A reply of more than **100 000** items is refused with `stream-too-large` rather than truncated, and a session holds at most **8** open streams. | by construction; tested (`S3-open-stream-bound-enforced`, `S3-open-never-exceeds-max`) |
| **S4** | Back-pressure. Nothing is produced until it is pulled: the chunks are cut once, when the stream is opened, and `pull` reads. A client that stops pulling costs one stream's storage and no further work. | by construction (`E4d_stream` is data; `pull` is total) |
| **S5** | Every stream ends explicitly: the item after the last chunk is a `Halt` carrying the reply's terminal value, or a `Fail` carrying the reason. A stream never simply ends. | by construction; tested (`S5-explicit-terminator`) |

---

## 1. The wire

One JSON object per line in, one JSON object per line out, in order.

```json
{"id": 7, "request": "run", "source": "fixture", "family": "ref", "program": "makeGet"}
```

```json
{"protocol":"effect4d/1","ok":true,"request":"run","id":7,"host":"native",
 "header":[...],"headerFields":{...},"rows":["op\tmake\t7", ...], ...}
```

Every response carries:

| field | meaning |
| --- | --- |
| `protocol` | `"effect4d/1"`. Bumped when a field changes meaning or is removed. |
| `ok` | `true`, or `false` with an `error`. |
| `request` | the request name, echoed. |
| `id` | the request's `id`, echoed, `null` if it carried none (W1). |
| `host` | `"native"`, `"bytecode"` or `"js_of_ocaml"` (`Sys.backend_type`). |
| `header` | the golden header block, as an array of TSV lines (§2). |
| `headerFields` | the same, as an object. |

An error response replaces the payload with
`{"error": {"kind": "...", "message": "..."}}`. The kinds are `no-request`,
`unknown-request`, `no-program`, `unknown-id`, `unknown-source`, `unknown-program`,
`unknown-mask`, `unknown-stream`, `out-of-order-pull`, `chunk-already-delivered`,
`stream-too-large`, `too-many-streams`, `no-text`, `no-reference`, `bad-diff`, `bad-expect`,
`bad-json`, `avatar-failure` (a `Failure` raised inside the avatar, such as a tape read past
its end), `stack-overflow` and `internal-error` (any other exception, reported by name). A
malformed request is never fatal: the session continues.

**`id` is the request id, not a program handle.** A program handle is `programId`, from a
`load`. The two used to share a key, which made every request naming a loaded program look
like a replay of the `load` that minted it.

### Transports

- **stdin/stdout** (the default on all three hosts). A live session: a request is answered
  before the next is read. Under node the line reader is `fs.readSync` on fd 0, which blocks
  on a pipe.
- **TCP**: `effect4d --tcp 47311` serves the same protocol on `127.0.0.1`, one connection at
  a time, **each connection its own session**. Not on the node host.
- **one-shot**: `effect4d --once '<json>'`; `--version`; `--schema`.
- **as a library**: §6.

---

## 2. The header block, and why it is there

Every response carries the header of a `generated/traces/*.tsv` golden, so a daemon answer
can be written to a file next to a golden and compared by the estate's own rule with no
translation:

```
format	effect4-trace-golden-v1
generator	ocaml/server/dune	sha256=…
regenerate	ocaml/server/tools/dune-build.sh
input	ocaml/avatar/deep_fibers.ml	sha256=…      (one row per input, per-file digest)
…
pin	effects	a4ee7a14248ee5976039b73039319efa87834986
format	effect4-trace-v1
face	ocaml
program	ref.makeGet
tape	
rules	
```

`face` is `ocaml` because the rows *are* the avatar's: the daemon links the avatar's own
library (`effect4-avatar`) and changes nothing about them. The `pin` is read at build
time out of `generated/traces/masks.tsv`. The `input` digests are per file, where
`avatar_main.ml` stamps one digest over all its sources at once — so a `pins` answer says
*which* file moved.

A `run` response also carries `tsv`: the header block and the rows, joined by newlines, ready
to write to a file.

---

## 3. The row vocabulary

The rows are the estate's, verbatim, one TSV line per row
(`git:c407ab7:Effect4/Target/TypeScript/Trace.lean`, `git:c407ab7:harness/trace/tracer.ts`):

```
op	<name>	<request>
answer	<name>	<value>
failed	<name>	<error>
decide	<site>	true|false
done	{"success":v} | {"failure":e} | {"interrupted":true} | {"defect":"…"}
frontier
```

`enter`, `leave` and `finalizer` are in the vocabulary the daemon parses (the Flow faces emit
them) but the avatar never produces them.

Values are the wire alphabet: `[]` is unit, a list is right-nested pairs closed by unit, a
handle is its index in first-seen order, `{"none":true}` / `{"some":v}` are the option.

**Masks.** `generated/traces/masks.tsv` is compiled in. Its three masks — `outcome`, `m1`,
`m2` — are what `run` projects under, what `diff` compares under and what `why` searches
under. A request may name a subset (`"masks": ["m1"]`) or carry a table of its own
(`"masksText": "<the file's text>"`).

---

## 4. Naming a program

Every request that runs something names its program in one of four ways.

| `source` | fields | meaning |
| --- | --- | --- |
| `"fixture"` | `family`, `program`, optional `tape` | one of the avatar's committed program tables |
| `"corpus"` | `program`, optional `text`, optional `tape` | a program of the adversarial corpus DSL; `text` supplies a corpus text of the caller's own |
| `"golden"` | `text`, optional `family` | a golden's own wire header block: the program, tape and rules are read out of it |
| `"loaded"` (or absent) | `programId` | a program a previous `load` resolved |

An absent `tape`, and an empty one, both mean *the program's own default*: nothing for a
fixture program, and for a corpus program its `tape` line or 32 all-`false` entries — the
same defaults `avatar_main.ml` synthesises.

Families: `fiber`, `ref`, `deferred`, `scope`, `layer`, plus `extra` (the avatar's programs
for the `WithFiberAction` arms no committed golden reaches). `programs` lists every name.

---

## 5. The requests

The full alphabet is answered by `schema`, in the estate's `OpSpec` shape
(`git:c407ab7:Effect4/Target/TypeScript/ScriptFlow.lean:39`: `name`, `kind`, `requestTy`, `answerTy`,
`errorTy`, `params`) — the daemon is a host boundary and describes itself the way the estate
describes one. What follows is prose for the same 19 rows.

### `ping`, `version`, `pins`, `schema`

`version` and `pins` are the same answer: the protocol, the host, the OCaml version, the
build note, the rc.112 `pin`, the per-file `inputs` with their SHA-256, the request list, and
the `src/Effect4/Machine/*.lean` modules the arm citations resolve against.

`schema` answers `requests` (the `OpSpec` rows), `properties` (§0, each with its `how` and a
`theoremShape`) and `bounds` (`maxInFlight`, `journal`, `maxOpenStreams`, `maxStreamItems`).

### `families`

The five service families, each with its `OpSpec` rows (`name`, `params`, `answer`), the
avatar module that implements it, its programs, and the `harness/trace/*-fixture*.ts` export
the rows were read from. `extra` and `corpus` are reported separately, under their own
headings, because neither is a family.

### `masks`, `programs`

The mask table with its per-row-kind `keeps`; and every program the daemon can run.

### `load`

Resolves a program and returns `{"programId": "p0", "program": "ref.makeGet", "family":
"ref", "tape": "", "rules": "", "defaultMaxOps": null}`. `reset` clears the table (and the
open streams) but keeps the reply journal, so a `reset` cannot be replayed into a second
reset.

### `inspect`

What a program declares, read off its source and not off a run:

- `operations` — the family's `OpSpec` rows;
- `alphabet` — the row kinds and the value alphabet with their wire forms;
- `roots` — for a fixture program the numeric body table a fork names (`0` succeeds with 11,
  … `4` never, `5` masks across a yield, `6` completes the Deferred at handle 0); for a corpus
  program the declared roots with their steps;
- for a corpus program also `notes`, `tape`, `maxops`, `main` and `usedOperations`.

### `run`

Inputs: a program, optional `tape`, `maxOps`, `fuel`, `rounds`, `masks`, an optional `expect`
(a golden's text, or an array of row lines), and an optional `chunk` (§ streaming).

Outputs: `rows` (the TSV row lines), `rowCount`, `projections` (per mask), `outcome`
(`finished` with the exit, `frontier`, or `stuck`), `yields`, `events` (the `RunEvent` trace),
`eventCount`, `tsv`, and — when `expect` was given — `verdicts` (per mask: `agree`, `rows`,
`firstDifference`, `expected`, `actual`) and `agree`.

With `"chunk": n` the rows are handed over as a stream instead of inline: `rows` is omitted
and the reply carries `stream` (the head) and `first` (the first item). Pull the rest with
`pull` (S1–S5).

### `step`

Runs the drive loop under a bound and returns a `RunMachine` snapshot. Two bounds:

- `fuel` — how many commands one `drive` may execute (`Fibers.lean`'s `drive` fuel);
- `rounds` — how many sweeps of the armed dispatchers `flushAll` is allowed. `rounds: 0` is
  `runFork` alone. This is the bound R2 is prefix-closed in.

The snapshot is every field of every carrier, under the Lean name: `fibers` (each with
`frame` — `control`, `interruptible`, `interruptedCause`, `deferredInterrupt` —, `status`,
`running`, `parked`, `pending`, `finalizing`, `exit`, `currentOpCount`, `maxOpsBeforeYield`,
`preventYield`, `yieldOverride`, `yielding`, `raceAnswerHeld`, `observers`, `children`,
`dispatcher` with its priority buckets and tasks), `races`, `nextId`, `nextToken`, `nextRace`,
`middlewareInstalled`, `stuck`, `finished`, and `state` (the fixture's `started`/`cleanups`,
`Deep_stores.store` — the Ref heap, the Deferred store and its due queue, the ScopeStore —
and `Deep_layer.layers`, the memo world).

`control` is the continuation status. It is the one field that is not a Lean field verbatim:
`FrameFiber.current`/`.stack` are the OCaml stack (the avatar's DIVERGENCE 1), so the snapshot
reports `program` (unstarted), `onstack`, `suspended` with the token its one-shot continuation
answers to, `failing` with the cause, or `ended`.

### `pull`, `streams`

`pull` takes `stream` and `cursor` and answers the item at that cursor, under S1–S5. A
finished stream is closed when its terminator is delivered, and its slot freed. `streams`
lists the open ones with their heads, the count and the bound.

### `diff`

`left` and `right` (each a golden's text or an array of rows), optional `masks`, optional
`program` and `knownText`. Returns a verdict per mask and, when the program is in the
classified table (`avatar/corpus/known-divergences.tsv`, compiled in), its class and reason.

The comparison is `avatar/compare.py`'s rule ported to OCaml, so the daemon is self-contained:
no python, and it works on the node host too.

### `explain`

For each row: its index, kind, name, the avatar **handler** that produced it, and the
`RunEvent`s in its bucket. Plus a `citations` count — `serviceRows`, `withArm`,
`withLeanSite` — so how far the chain reaches is a number and not a claim.

A handler carries its label (`arm_fork`, or `case Rref_make` for a dispatch case that pushes
its row itself), the effect `constructors` that reach it, its doc comment, `citationsFrom`
(itself, or the function whose match it is a case of), its `citations` — the `` `…:N` ``
tokens the avatar writes — each resolved against every `src/Effect4/Machine/*.lean` module as

- `exact` — the same citation token occurs in a Lean module: the file, line and enclosing
  declaration are given;
- `byLine` — the token names a line, explicitly (`Stores.lean:653`) or bare (`:550`, meaning
  a line of the home module of the avatar file the arm lives in); reported **unverified**;
- `unresolved` — an rc.112 or harness citation no Lean module carries;

and its `leanDeclarations` — the declarations the doc names by name (`interruptRecord`,
`WithFiberAction.fork`, …) with the file and line each is declared at. Prefer these to the
citation lines: a name survives an edit of the Lean file and a line number does not (§7.8).

**Row-to-event correlation.** The avatar records no link between a service row and the events
around it, and it is consumed read-only, so the daemon recovers the link by replay: it runs
the program again under a tightening bound and buckets the rows by the step at which each
first appears. `granularity` says which bound was used — `flush-round` (always sound; the run
at `r` rounds is a genuine prefix of the run at `r+1`), `drive-command` (finer, used only when
the scan is checked monotone), or `coarse`. `buckets` is how many distinct buckets the rows
fell into; `buckets: 1` means the answer has no per-row event attribution and says so.

### `why`

A program, and a `reference` row list (rc.112's, typically produced by
`avatar/corpus_rc112.mjs`). Returns the first row on which the two differ under a mask, the
mask it differs under, the rows on both sides, three rows of context on each side, the avatar
event trace up to the difference, the events in the difference's own bucket, the handlers of
the differing row, and the classified entry if the program has one.

### `reachable`

From a snapshot (same bounds as `step`): per fiber, whether it is `resumable` (it holds a
captured one-shot continuation whose token is the guard it is parked on) and with which
token, whether its dispatcher is `armed` and how many tasks it holds, what it is `parkedOn`
(a `fiber` with the countdown remaining, a `deferred`, a `race`, a `countdown` or a bare
`async`), whether it is interruptible and whether an interrupt is pending, its children, and
the observers others hold on it. Plus the machine-level `resumable`, `armed`,
`observersPending`, `dueResumes`, `finished` and `stuck`.

### `budget`

The op counter and the yield injection points along a run: `maxOpsBeforeYield`,
`preventYield`, `yields`, `injections` (each with the fiber and the `currentOpCount` at which
the yield was injected) and `perFiber` (`currentOpCount`, the fiber's own budget pair,
`yielding`, `yieldOverride`, and how many injections it took).

`currentOpCount` is reset at every `Cmd.evaluate` and `Cmd.resume`, so the per-fiber figure is
the count since that fiber was last given the processor. The answer says so in a `note`.

---

## 6. As a library

The handlers are a plain OCaml module. Nothing in `effect4d.ml` or `effect4d_js.ml` but
transport.

```ocaml
val Effect4_daemon.run_program :
  E4d_catalog.program -> string (* tape *) -> E4d_wire.mask list -> Effect4_daemon.result

val Effect4_daemon.step : session -> E4d_protocol.request -> session * E4d_protocol.response
val Effect4_daemon.answer : session -> string -> session * string   (* one line in, one out *)
val Effect4_daemon.handle : E4d_json.t -> E4d_json.t                (* the shell session *)
val Effect4_daemon.handle_line : string -> string
val Effect4_daemon.masks : unit -> E4d_wire.mask list
val Effect4_daemon.program_of_fixture : string -> string -> E4d_catalog.program
val Effect4_daemon.program_of_corpus : ?text:string -> string -> E4d_catalog.program
```

`result` carries `result_rows`, `result_header`, `result_projections`, `result_events`,
`result_outcome` and `result_machine` — the avatar's own `run_machine`, not a copy.
`tests/lib_test.ml` is the demonstration.

From JavaScript, the js_of_ocaml build exports the same functions, each `string -> string`
over JSON text:

```js
const effect4d = require("./effect4d.js")
JSON.parse(effect4d.runProgram(JSON.stringify({ family: "ref", program: "makeGet", tape: "" })))
JSON.parse(effect4d.request(JSON.stringify({ request: "explain", source: "corpus", program: "aIntDaemon" })))
```

`tests/node_module_demo.mjs` is the demonstration, and it is the interesting one: spike A0's
probe C found that a `perform` inside an OCaml callback invoked from JavaScript is `Unhandled`
under `--enable effects`, because `caml_callback` replaces `caml_fiber_stack` with a fresh
one-frame fiber. It works here because the avatar installs its own handler *inside* the
callback — `run_under_handler`'s `match_with` runs on the fresh fiber, and every `perform` the
fiber bodies make is under it. A JavaScript caller that tried to perform *across* the boundary
would still be `Unhandled`; a JavaScript caller that asks the daemon to run a program is not
crossing it.

---

## 7. Stated limits

Each of these is a property of this build, not a claim about what a daemon should be.

1. **No authentication, no authorisation, no transport security.** The TCP listener binds
   `127.0.0.1` and accepts anything that connects. Do not expose it.
2. **No persistence.** The session dies with the process (or with the TCP connection). Nothing
   is written to disk.
3. **Streaming is pull-only and reply-only.** A large reply can be chunked (S1–S5), but there
   is no server push, no cancellation of a request in flight, and no streaming *input*.
4. **One request at a time, one connection at a time** (W4). The avatar keeps module-level
   state — the tape, the row sink, the stores, the handle space — so two runs must not
   interleave. A daemon that served several clients at once would need the avatar's state to
   be a parameter rather than a module-level binding; that is a change to the avatar, which
   seat W1 owns.
5. **No multi-program sessions in the machine sense.** `load` remembers programs, but every
   `run` starts from a reset avatar, and `step` re-runs from the start under a larger bound
   rather than continuing a held machine. A machine could survive a request — its
   continuations are ordinary OCaml one-shot continuations — but the global state around them
   would have to be per-session first (see 4).
6. **Row-to-event correlation is by replay, not by observation.** `buckets: 1` means one
   bucket for the whole run: every row shares every event. A single-fiber synchronous program
   is always one bucket.
7. **Drive fuel is not a monotone step counter** (R2, with the counterexample).
8. **Citation resolution is partial, and shows drift.** Of the 118 citation tokens the
   avatar's handlers carry, **62 resolve `exact`, 48 `byLine`** (reported unverified) and
   **8 `unresolved`** — counted 2026-09-04 against all sixteen `src/Effect4/Machine/*.lean`
   modules (`grep -o 'resolution = "[a-z]*"' _build/default/server/e4d_armmap.ml | sort |
   uniq -c`). An earlier 16/12/4 counted the avatar of `b60fe28` against `Fibers.lean`
   alone; it is superseded by what `explain` and `version` report. The `byLine` ones have
   drifted: the avatar cites `interruptRecord` at `:550` where `Fibers.lean` declares it at
   558, `spawn` at `:622` where it is at 631, `exitFiber` at `:992` where it is at 1031 and
   `drive` at `:1025` where it is at 1064 — the avatar was written against the Deep files
   before their promotion. This is why `explain` reports `leanDeclarations` by name as well.
9. **Not every handler cites Lean.** Seat W1's checkpoint-1 store cases (`case Rref_make`, …)
   carry no citation of their own and inherit none from `store_arm`, so a `ref`, `scope` or
   `deferred` run resolves its rows to an avatar handler and no further. `explain`'s
   `citations` count says so per run: 12 of 12 for a `fiber` run, 2 of 4 for `layer.buildOnce`,
   0 of 4 for `ref.makeGet`.
10. **The `fiber` family has no committed golden in this checkout.** `generated/traces/`
    carries `ref`, `deferred`, `scope` and `layer` (25 goldens). The `fiber` and `extra`
    programs are checked against the avatar's own committed faces under
    `ocaml/avatar/out/*.ocaml.tsv` instead.
11. **The daemon adds no semantics.** Every row it emits comes from the avatar unchanged. It
    resets the avatar's global state between requests (`e4d_reset.ml`) and nothing else; if the
    avatar is wrong about something, so is the daemon.
12. **The package swap has not happened.** The `effect4` opam switch of
    `docs/research/2026-09-04-ocaml-packages-plan.md` did not exist while this was built, so
    the daemon is written against the 5.1.1 default switch's stdlib. The seams the swap goes
    through are `e4d_protocol.ml` (the codec), `e4d_server_loop.ml` (the loop) and
    `e4d_json.ml` (the JSON value); each names its replacement in its header.

---

## 8. Layout

```
dune                     the build: the four generated modules, effect4d_lib over the
                         avatar's library `effect4-avatar`, the three hosts (BUILD-DUNE.md)
tools/dune-build.sh      build all three hosts, into ocaml/_build
tools/dune-test.sh       build, then every test on every host this machine reaches
e4d_json.ml              a minimal JSON value, parser and printer  (-> Yojson)
e4d_wire.ml              the trace wire: headers, row kinds, masks, projection, comparison
e4d_protocol.ml          the request and response carriers, and their codec  (-> deriving)
e4d_stream.ml            streaming replies as a pull carrier (S1-S5)
e4d_alphabet.ml          the daemon's own OpSpec rows and the stated properties
e4d_server_loop.ml       the loop, with the transport as a parameter  (-> Eio)
e4d_reset.ml             resetting the avatar's module-level state between requests
e4d_catalog.ml           the programs, and `inspect`
e4d_snapshot.ml          `RunMachine` as JSON, field for field
effect4_daemon.ml        the session, the state machine, every request handler, the library
effect4d.ml              the POSIX transport (stdin/stdout, TCP)
effect4d_js.ml           the node transport, and the module exports
server_runtime.js        the four JavaScript externals of the jsoo build
tools/gen_armmap.py      the avatar's dispatch tables, row names and citations
tools/gen_families.py    the five families' OpSpec rows, from the harness fixtures
tools/gen_pins.py        the pin, the per-file digests, the build note
tests/test_client.py     the protocol, on every request, program, property and host
tests/lib_test.ml        the library surface, no wire (OCaml)
tests/node_module_demo.mjs   the jsoo build required as a node module (JavaScript)
```
