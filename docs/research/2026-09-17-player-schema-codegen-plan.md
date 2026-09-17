# The player, the schema layer and the one codegen API: a plan

2026-09-17, written against `f93b3040`. It follows the owner's direction of the same day:
an engine instance is a way to play Eff programs; the same API on WASM as on OCaml;
everything is a schema; OCaml needs a native schema AST; the store needs its own API, which
is not designed yet; no sync for now; plan it properly before building.

Companion: `2026-09-16-ocaml-engine-base-abstractions.md` (items A to H). This note replaces
its item A with something smaller and better, and gives items B, C and F a home.

## 1. What is settled

1. **An instance is a player.** It takes a program's canonical bytes and a tape and answers
   canonical bytes. Replay is deterministic, so tapes under concatenation act on machines and
   every instance is the same action (on the accepted prefix: a stuck machine absorbs, and
   fuel belongs to the job, never to the instance).
2. **The boundary is canonical bytes, described by schemas.** No typed value crosses between
   instances or between a host and an instance.
3. **No sync now.** Stores do not merge, roots do not move between instances. The laws that
   would let them (node union is commutative and idempotent; roots only fast-forward) are
   recorded in §6 and not built.
4. **Targets come off one pipeline.** A target is a printer plus a profile (§5).

## 2. The schema layer that already exists in Lean

The tree has the whole layer; only OCaml lacks it.

| piece | where | what it is |
| --- | --- | --- |
| `Val` | `Store/Val.lean` | the universal value tree (unit, bool, nat, str, bytes, list, pair, none, some, ctor, ref, handle) with `encode`/`decode`, exact |
| `Shape`, `ShapeDoc` | `Store/Shape.lean` | the schema AST: `unit bool nat string bytes digest list option pair struct sum ref anyRef named`, a root plus a definitions table |
| `ShapeDoc.accepts` | same | the checker: a value fits a shape; structural on the value |
| `ShapeDoc.document`, `print` | same | the spec document and the JSON printer, both derived from the shape |
| `Canonical α` | `Store/Canonical.lean` | `shape`, `toVal`, `ofVal`, with `ofVal_toVal`, `ofVal_exact`, `fits` proved |
| `Content α` | `Store/Node.lean` | `Canonical` plus the kind byte; a node is `version ∷ kind ∷ spec ∷ payload` and `spec` is the address of the schema node |
| generated instances | `Program/Derived.lean`, `Store/Derived/Schema.lean`, `Api/Derived.lean` | `Canonical` for the program alphabet and the API types |
| `Api.ofBytes`, `Api.bytesOf` | `Api.lean:167-171` | a program from its bytes, exactly, and back; `decode_exact` |

So "everything is a schema" is already true in Lean: every boundary value is a pair
(`ShapeDoc`, `Val`), and every node in the store names its schema by address.

On the OCaml side the same layer is hand code: `eff/eff_frame.ml` (the framing kernel, 314
lines), `engine/cas/e4_shape.ml` (601 lines: a per-kind table transcribed by hand, because a
`Cid` frame cannot be told from any other 32-byte frame without the shape), and the generated
per-type codecs `eff_wire.ml` and `eff_json.ml` which exist because there is no generic one.

## 3. OCaml's native schema AST: generated, not written

Do not port `Shape` by hand. Compile Lean's own modules through LCNF, as the machine already
is. New roots:

- `Store.Val.encode`, `Store.Val.decode` (the framing, replacing the hand kernel as the reference);
- `Store.ShapeDoc.accepts`, `Store.ShapeDoc.print`, and `Canonical Shape`'s `toVal`/`ofVal` (a schema is itself content);
- `Api.ofBytes`, `Api.bytesOf`.

**Probe, run today.** The engine's generator with `Api.ofBytes` and `Api.bytesOf` added to its
roots translates the whole closure with no missing declaration and nothing beyond the cap.
Three primitives have no row: `Char.ofNatAux`, `ByteArray.emptyWithCapacity`,
`ByteArray.push` (all from UTF-8 string decoding). Three builtin rows, no design question.

**What this deletes.** Once the engine loads a program with Lean's own verified decoder:

- `engine/e4_program.ml` (the hand translation between two OCaml copies of one type, 430
  lines), `e4_program_layout.ml`, `scripts/generate-engine-structure.py`, the ordinal pin and
  the manifest check. There is one copy of the program type, the engine's, and bytes are how
  a program reaches it. This is the drift source, removed rather than generated.
- `e4_shape.ml`'s hand table: `cids_of` becomes a walk of the value by its `ShapeDoc`, which
  the node already names.
- In time `eff_wire.ml` and `eff_json.ml`: a generic codec over (`ShapeDoc`, `Val`) replaces a
  codec per type. `Eff_types` stays only if OCaml authors programs as typed values; that is a
  separate, optional face (§7, question 4).

**Cost to watch.** `Bytes` is `List UInt8` in Lean, so the compiled decoder walks a list.
Programs are hundreds of bytes, so correctness first; a `Bytes` carrier (an OCaml `string`
behind the same operations) is one more row in the carrier table when a benchmark asks.

## 4. The player

The player is `Effect4.Api.HostSession` with a bytes boundary. Its whole surface:

| function | input | output |
| --- | --- | --- |
| `load` | program bytes, row table bytes, profile | a session, or a refusal |
| `submit` | a reply (bytes) | a session, or a verdict that leaves the state unchanged |
| `advance` | a budget | a session and an outcome |
| `inspect` | nothing | the run, as bytes under its schema |
| `schemaOf` | a boundary name | the `ShapeDoc` of that boundary, as bytes |

`schemaOf` is what makes it self-describing: a host or an agent asks the player what shape
`inspect` answers in and gets a schema, itself content. The MCP tools of R12 (start, step,
reply, inspect, trace, blame) are these functions with JSON printed by `ShapeDoc.print`.

Inside a player the carriers are private. The list carriers are Lean's own definitions, so a
player with **zero extern rows** is correct by construction on every target; fast carriers are
a per-target optimisation checked against it by byte equality of `inspect`.

The differential across targets is then one rule: same bytes in, same bytes out.

**Landed (2026-09-17): the typed session API and its algebra.** `src/Effect4/Api/Player.lean`
and `src/Effect4/Laws/Api/Player.lean`, over `HostSession`'s checked transitions and adding no
semantics. `Command` is a journal row (`bind`, `submit`, `apply`, `control`); `Player` packs
the program, the table, the session they index and the job's step fuel; `step : Player →
Command → Player × Phase` is total; `replay` folds it and keeps every phase; `inspect`,
`observe` and `outstanding` are the reads. Laws, all at `[propext, Quot.sound]`:
`step_refused` (a refused row leaves the player unchanged, from one lemma per transition),
`replay_append` (journals act), the monoid of plays with `replayPlay` a homomorphism into it,
`replay_unique` (journals are the free monoid, so `replay` is the only such map),
`behaviour_cons` (behaviour unfolds along `step`, the map into the final Mealy machine), and
`replay_skip_refused` with `behaviour_skip_refused`: a refused row is the unit, so a journal
has a normal form without refused rows, which is what a compaction may keep. Contract:
`Test/Api/PlayerContract.lean` plays the two-call scenario as one journal. At this level the
stuck caveat of §1 disappears: `step` is total and a refusal is a row like any other.

Still owed for the table above: the bytes boundary. `Command`, `Phase`, `Refusal`, `Header`,
`Call`, `Reply`, `NativeDecision`, `Completion` and `Api.Run` need `Canonical` instances from
the generator (the `Api` group derives four types today), then `stepBytes`, `inspectBytes` and
`schemaOf` are one line each, and the player joins the LCNF roots.

## 4b. The holder: what keeps a player running (owner, same day)

A player is pure, so something must hold it: keep its events, answer its parks, expose it.
The owner's direction: an event construct, Eio or similar on OCaml, an event source holding
the WASM player, built from Effect's own types (its event log for persistence), everything
under a schema, a state machine, MCP on top. That is event sourcing with the player as the
reducer, and the pieces exist on both sides.

**One shape on every host: journal, player, reactor.**

| part | what it does | OCaml | TypeScript or WASM host |
| --- | --- | --- | --- |
| journal | append-only rows per job: `(kind, index, canonical bytes)`; read from an index; subscribe | `cas/e4_wal` (rows are already opaque canonical bytes plus a kind byte) | rc.112 `EventJournal` (`unstable/eventlog`): `write { event, primaryKey, payload: Uint8Array, effect }`, `entries`, `changes`; layers for memory, IndexedDB and SQL |
| player | `state' = step state decision`, pure | generated | generated TypeScript, or the WASM module |
| reactor | turns the world into decisions: timers, I/O, external rows, an agent's reply | Eio fibers and streams (the Lean models are in `OCaml5/Lib/Eio`), inside one owner domain per machine as `e4_sched` requires | Effect fibers, `Schedule`, `PubSub`; the journal's `changes` is the subscription |

**The one rule: journal first.** A decision is appended before it is applied. State is the fold
of the player over the journal, recovery is replay, and the reactor can be anything because
replay never calls it. `EventJournal.write` has this shape already: it takes the payload and
the `effect` to run on the committed entry, so "commit, then step the player" is one call.

**Events are schemas.** An rc.112 `Event` is `{ tag, primaryKey, payload: Schema, success:
Schema, error: Schema }`. The decision alphabet maps onto it directly: one `Event` per
decision constructor, `primaryKey` the job, `payload` the decision's schema (printed from its
`ShapeDoc` by the schema printer, R7), `success` the observation's schema, `error` the
refusal's. An `EventGroup` of them is a typed client for a player, and it is also exactly the
MCP tool list (R12): one tool per event, arguments and results under the same schemas.

**The state machine** is the session's, already in Lean: `HostSession.Phase` with refusal as a
verdict that leaves the state unchanged. The holder adds no states of its own.

**Two mismatches to design around, both known now.**

1. `EventJournal`'s `EntryId` is a time-based identifier the host mints. LOG-REL forbids
   anything host-chosen in a position. So the entry id is transport only; the canonical
   position is the row's index within its job, carried in the payload or counted per
   `primaryKey`, and two hosts must agree on bytes and indices, never on ids.
2. `EventLog` above the journal brings remotes, conflict handling, compaction and encryption.
   That is sync, which is out of scope now. Use `EventJournal` and `Event`/`EventGroup`; leave
   `EventLog`'s remote half alone until the store API (§6) exists.

**Not first, but worth recording:** the holder could itself be an Eff program whose external
rows are the journal's operations. It would make the holder replayable and inspectable like
any other program. It needs the package rows of R8 first.

**Reading checked with the owner's words.** "They need an event construct" is read here as the
host-side holder. If it also means a construct inside `Eff` (a program that emits and awaits
named events), the existing pieces cover it without a new constructor: awaiting is an external
row answered by the tape, emitting is a trace event; a named-event pair of rows would be an
addition to the row table, not to the alphabet.

## 5. The codegen API

Today `src/OCaml5/Lcnf/Translate.lean` does four jobs at once: reads LCNF and closes over
callees, makes lowering decisions, builds OCaml syntax, and names things. The decisions are
target-independent and the last two are not.

**Lower once** into a neutral core. The tree already has the core language:
`tools/Conform/Lcnf/SemanticsTarget.lean` defines `Target.Expr` (let, letrec, application,
constructors, records, tuples, match, primitives) with a total evaluator and a `Word`
parameter for the integer width. Today emitted OCaml is read back into it for checking. Make
it the lowering's output instead, and add what it lacks: data declarations, join points,
saturated call against partial application, and abstract carrier types with typed operations.

Decisions made once, in the lowering: the closure and its emission order, the `_redArg` fold,
erasure, trivial structures, unique binders, carrier inference (landed 2026-09-17), and a
pass that turns self tail calls into loops (TypeScript needs it; every target gains).

**A target is a printer plus a profile.**

| profile field | OCaml | js_of_ocaml | wasm_of_ocaml | TypeScript | Wasm GC direct |
| --- | --- | --- | --- | --- | --- |
| integer bits | 63 | 32 | 31 | 53, or bigint | 64 |
| strings | bytes | bytes | bytes | UTF-16 units | bytes |
| tail calls | yes | self only | yes | none | `return_call` |
| partial application | automatic | automatic | automatic | explicit | explicit |
| carriers bind as | functor parameters | same | same | a factory over an interface | imports |

`js_of_ocaml`, `wasm_of_ocaml` and Melange are not languages to model. They are the OCaml
printer under a different profile. The archived work that modelled `js_of_ocaml`'s block IR
spent its effort on effect handlers, which generated code does not use. ReScript would be a
third syntax to print and a compiler in the trust chain we cannot check, for what a direct
TypeScript printer gives; not a target.

Extern rows stop naming OCaml spellings. A row names a carrier and an operation with a typed
signature, and each target has a binding table. (The law form of a row, Lean operation against
carrier operation with the theorem that relates them, is item F of the companion note.)

## 6. The store: deferred, with its questions written down

Not designed here. What is known:

- Lean has the reference: `Store.Store` (`putNode`, `get`, the three outcomes fresh,
  duplicate, conflict; `Closed` and `Sound` as theorems; a roots plane).
- OCaml has a fast implementation (`cas/e4_cas`, pack, index, WAL, checkpoint) written before
  the schema layer reached it, which is why it carries hand tables.
- Laws that would make instances' stores mergeable, recorded and not built: node sets merge by
  union (content addressing makes it commutative, idempotent and conflict-free); roots do not,
  they fast-forward along `prev` and refuse a fork.

Questions the store API must answer before it is built:

1. Is the API the Lean `Store.Store` compiled through the same pipeline, with the OCaml pack
   as its carrier? (Recommended: yes; it is the carrier pattern again.)
2. What does a player see of it: `get : address → bytes` and `put : bytes → address` only, or
   typed `Ref α` with the schema check at the boundary?
3. Who owns roots when there is one authority and several players?
4. Are checkpoints content (a generated codec for `RunMachine`, item C) or only tape positions?
5. What is the retention rule for the log against the trace?

## 7. Order, and what each step proves

1. **Bytes in.** Add `Api.ofBytes` to the engine roots with the three primitive rows; load
   programs from bytes in `e4_engine`; delete `e4_program.ml`, the layout script and the pin.
   Gate: `make check-ocaml`, 0 divergences on the same corpus. Small; this is the drift source.
2. **Schema AST out.** Add the `Val`, `Shape` and `ShapeDoc` roots; check the compiled
   `Val.encode`/`decode` against `eff_frame.ml` on every golden, then make the hand kernel the
   carrier behind it or delete it; replace `e4_shape.ml`'s table with the shape walk.
3. **The player.** `HostSession` roots with the bytes boundary and `schemaOf`; zero extern
   rows first, byte-equal to `Fast` and `Ref` on the differential corpus.
4. **The neutral core.** Split `Translate.lean` into lowering and OCaml printing over
   `Target.Expr` extended; output byte-identical to today's. No new target yet.
5. **TypeScript printer** over the same core (`lean4-typescript` has the syntax and the
   renderer); the player in TypeScript, byte-equal on the corpus.
6. **WASM** by `wasm_of_ocaml` on the OCaml player first (31-bit profile); a direct Wasm GC
   printer only if a reason appears.
7. **The holder** (§4b): journal, player, reactor, journal first; on OCaml over `e4_wal` with Eio, on the TypeScript host over rc.112 `EventJournal`, which also holds the WASM player.
8. **MCP driver**: the event group of the decision alphabet as the tool list (R12).

Steps 1 to 3 need no new API and remove hand code at each step. Step 4 is the API. Steps 5
and 6 are what the API is for.

## 8. Decisions open

1. **Integer overflow.** Recommended: a refusal on every target, never wraparound, so targets
   agree or refuse and width stops being a semantic difference. Cost: checked arithmetic on
   program-level `Nat` atoms.
2. **String order.** Recommended: byte order is canonical. UTF-16 order differs outside the
   basic plane, and tags are strings.
3. **What the TypeScript is for.** If agents and the Effect interop read it: print it
   directly, typed. If it is only a way to run in JavaScript, `js_of_ocaml` suffices.
4. **Does OCaml author programs as typed values?** If no, `Eff_types` and its codecs retire
   with step 2 and OCaml only plays. If yes, they stay as a generated authoring face.
5. **The store questions of §6.**
