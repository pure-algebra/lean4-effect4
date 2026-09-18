# The MCP surface over the new application API — scout C (2026-09-17)

Worktree `/Users/pooks/Dev/lean4-effect4-scout-c`, detached at `d798feb2`. Seven `lake env lean`
probes, no source edited, no gate run. **Evidence words**: **proved** — a theorem with a proof
term at the cited line (I wrote none; I cite the tree's); **tested** — a `#synth`, `#check` or
`#eval` of mine that ran in my build, which every number and JSON fragment below is; **assumed**
— my own reading, marked where it appears; **stamped** — I ran no axiom print; **reproduced** —
nothing is from another machine.

**Summary.** The MCP face is not a new API. It is `Author.build`, `Run.open`, `Rows.*`,
`Run.observe`, `Api.explain` and `Api.supervision`, which all landed today, plus one missing
codec. I propose **14 tools**: seven over a program, six over a run, one over a schema — and
`run.play` deliberately not among them, because a tool that takes journal rows makes the agent
invent a `Call` and `Call.at` exists so that it never does. Of R12's nine `InspectOp` commands
only `explain`, `blame`, `at` and `children` are buildable today: `resolve` needs the store
(deferred) and `render`/`window`/`spans`/`locate` need a `Doc`, which **does not exist** in the
tree — so R12's first slice should be re-cut as the *run* protocol. Eleven readings an agent
wants are fields or functions of one `Observation`, so they are one tool, not eleven. On schemas
the answer is better than the plan assumed: `Canonical.shape T → ShapeDoc.document →
Codegen.Schema.generate?` already turns **28 of the 43 types I probed** into a runtime Effect
Schema, and `ShapeDoc.print` already prints a response value as MCP-shaped JSON — both tested
end to end. **15 have no `Canonical` instance**: four must never cross (`Api.Inspection`,
`Api.Machine`, `Api.Built`, `Run` — a machine or a proof), ten are the gap (`Observation`
first), one (`Document`) has its own printer. The server should be a Lean `--run` driver in
`src/Tools` first, generated bun second, because only a Lean host can hold a `Built`'s
certificate, so only there is `open_total` a statement about the server. Two cited receipts are
stale: `Canonical RowTable` **does** exist, and `src/Effect4.lean` **does** import `Effect4.Run`.

## 1. The tool table

### 1.1 The fourteen

Input and output name the Lean type; `[S]` = a generated codec, so a schema and a JSON printer
today (§3); `[—]` = none.

| # | tool | input | output | the Lean function | refusal | the law that makes it safe |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `program.build` | `Eff NativeOp` `[S]` + `RowTable` `[S]` | `ty : EffTy` `[S]`, `requires`, `closed`, `rowNames`, `programDigest` | `Author.build` (`Api/Author.lean:55`); over the wire, `Api.check` + `admitProgram` | `BuildRefusal` `[—]` (`Api/Author.lean:30`) | `build_table_lawful`, `build_rows_resolve` (`Laws/Program/Author.lean:155,175`), `build_lawful`, `build_runnable` (`:201,205`) |
| 2 | `program.print` | program + table (+ `module : Bool`) | `TypeScript.Expr` rendered | `Built.print` (`Api/Author.lean:107`) / `Api.emitModule` (`Api.lean:200`) | `PrintRefusal` `[—]`, `EmissionRefusal` `[—]` | law 12 / `PrintReadable` (`Laws/Codegen/PrintReadable.lean`) |
| 3 | `program.read` | `TypeScript.Expr` + table | program `[S]` | `Api.readAt` (`Api.lean:156`) | `Program.ReadFailure` `[—]` (has `.render`) | law 11, `Laws/Codegen/Read.lean` |
| 4 | `program.explain` | program + table | `{path, reason}` | `Api.explain` / `Api.blame` (`Api.lean:112,120`) | total | `explain_none_iff` (`Api.lean:125`) — **proved**: `none` exactly when well-typed |
| 5 | `program.at` | program + `path : List Nat` | the node, its children's arity | `Node.at_` (`Program/Refs.lean:44`), `Node.child` (generated, `Program/NodeLenses.lean:19`) | `none` off-tree | the generated lens laws in `Program/NodeLenses.lean` |
| 6 | `program.schema` | program + table | `Document` `[—]`, but `Codegen.Schema.generate?` prints it | `Api.schemaOf` (`Api.lean:138`) | `none` when ill-typed | D12 |
| 7 | `program.supervision` | program | `List ForkSite` `[—]` | `Api.supervision` (`Api/Supervision.lean:146`) | total | `supervision_static` (`Laws/Api/Supervision.lean:288`), `supervision_isDaemon_flag` (`:130`) |
| 8 | `run.open` | build ref + `id` + `Budget` | `{runId, Observation}` | `Run.open` (`Run.lean:100`) | **cannot refuse** except `id = ""` | `open_total` (`Laws/Run.lean:210`) |
| 9 | `run.control` | runId + one of `start`/`flush`/`clock n`/`interrupt f` | `List Phase` `[S]` + `Observation` | `Rows.start`/`flush`/`clock` (`Run.lean:172,175,178`), `Run.control` | `Phase.refused why` `[S]` | `advance_not_envelope` (`Laws/Run.lean:279`), `runPure_eq_run` (`:801`) |
| 10 | `run.answer` | runId + `Key` `[S]` + `Answer` `[S]` | `List Phase` + `Observation` | `Run.answer` = `play (Rows.answer …)` (`Run.lean:205,195`) | `Phase.refused`; **no rows at all** for a key with no call | `answer_rows_three` (`Laws/Run.lean:368`), `answer_accepted` (`:452`), `answer_once` (`:689`) |
| 11 | `run.observe` | runId | `Observation` `[—]` | `Run.observe` (`Run.lean:243`) | total | first-order by construction; `daemonsQuiet_iff` (`Laws/Api/Supervision.lean:473`) |
| 12 | `run.journal` | runId | `List Command` `[S]` | `Run.journal` (field, `Run.lean:58`) | total | `journal_replays` (`Laws/Run.lean:164`) |
| 13 | `run.replay` | build ref + `id` + journal | `List Phase` + `Observation` | `Run.open` then `Run.play` | per-row `Phase.refused` | `journal_replays`, `replay_append` (`Laws/Api/Runner.lean:81`), `replayRows_eq_replay` (`Laws/Api/RunnerBytes.lean`) |
| 14 | `schema.of` | a boundary name | `ShapeDoc` `[S]` | `Api.Runner.schemaOf` (`Api/RunnerBytes.lean:89`) | `none` for an unknown name | the schema of schemas accepts itself (the group's guard) |

Eight of these fourteen are functions that landed today and were not callable before.

### 1.2 What is deliberately *not* a tool

- **`run.play` (a journal row from the agent).** `Command.bind` carries a `Call` restating the
  run's name, table, next call id and the machine's parked request, and `bindCall` refuses a
  claim that does not match (`Api/HostSession.lean:145-158`); `Call.at` builds it from the
  machine instead (`Run.lean:151`) and `bindCall_at` (`Laws/Run.lean:318`) proves such a claim
  is never stale. `run.play` hands that job back to the agent, so keep `play` inside the server
  (tools 9, 10, 13 call it). **Tested**: a bind row from `kv-1` played on `kv-2` is
  `refused session`; three rows recorded before an answer and replayed after it are
  `refused callOrder, refused noCall, refused noCall`; a stray `apply` is `refused noCall` and
  leaves the observation bit-identical.
- **`run.daemons`, `run.exit`, `run.fibers`, `run.pending`, …** — each a field of `Observation`
  or a function of one (`Observation.daemons`, `.daemonsQuiet`, `Run.lean:256,260`). Eleven
  readings, one tool: the "few deep tools" argument in one line.
- **a reactor over the wire** — `Reactor σ = Program.Row → Val → σ → Option (Answer × σ)`
  (`Run.lean:269`) is a Lean function. See §2.4.

### 1.3 R12's `InspectOp` commands, one by one

| command | verdict |
| --- | --- |
| `explain`, `blame` | **survive** as tool 4; `Api.explain`/`Api.blame` exist and `explain_none_iff` is proved |
| `at`, `children` | **survive** as tool 5; `Node.at_` and the generated `Node.child` exist for `Eff` today |
| `resolve digest` | **not buildable**: it is the store's, and the store API is deferred (runner plan §6); no `Store.get` face exists |
| `render`, `window`, `spans`, `locate` | **not buildable**: they fold a `Doc` with a measure, and there is no `Doc` type (`find src -name "Doc*.lean"` returns only `Schema/Document.lean`, the schema `Document`, a different thing) |
| `evaluate program` | **not buildable as written**: the machinery is there (`NativeOp.external` + a `RowTable` + `Run`), the `InspectOp` signature is not. `grep -rn InspectOp src/ tools/ ts/ harness/ ocaml/` returns nothing |
| events | **not buildable**: `Inspection.trace` exists (`Api.lean:337`) but `RunEvent` holds `Ctx` and `EffThunk` and has no codec |
| — | of the nine, four survive, five do not |

**Consequence (D11).** §4.14b says the inspection signature is the first slice and the drivers
second. The tree now allows the opposite: the *run* protocol is fourteen tools over code that
exists, and the inspection protocol needs two structures (`Doc`, the store) that do not.

## 2. The run lifecycle over MCP

### 2.1 What the server holds between calls

Not the `Run`. **Tested**: `#synth Canonical Run` fails, and it must — `Run.session` holds
`Api.Machine` (`Api/HostSession.lean:84-93`) and `Run.built` holds
`admitted : AdmittedProgram program table`, a record of `Prop`s. The server holds (1) the
program bytes and the table bytes (`Api.bytesOf`, `Canonical RowTable`), (2) the **journal**, a
`List Command`, each row canonical bytes (`commandBytes`, `Api/RunnerBytes.lean:37`, exact by
`commandOf_exact`), and (3) the `Run` value as a **cache only**.

State is the fold — the runner plan §4b's "journal first". **Tested** on the kv run:
`(Run.open r.built r.id r.budget r.profile).play r.journal` gives the same `Observation`, the
same `phases` and the same `journal`, three `==` checks all true. That is `journal_replays`
(**proved**, `Laws/Run.lean:164`) decided on a concrete run.

### 2.2 The identity of a run on the wire

`Built.bytes` is **not** it: it is `Api.bytesOf b.program` (`Api/Author.lean:110`,
`Api.lean:492`), the program only. The table is not in it, and a program's external positions
mean nothing without the table it was written against (DI-22). **Tested**: the kv program is
321 bytes and `Api.ofBytes ∘ Built.bytes = some program`. So the wire identity is
`(digest(programBytes ++ tableBytes), Run.id)`, where `Run.id` is `session.header.session`
(`Run.lean:67`) and no transition writes it (`step_id`, `Laws/Run.lean:127`, **proved**).
Neither `Built.digest` nor a table-covering `Built.bytes` exists; both are one line, because
`Canonical RowTable` exists (§3.3). Decision D3.

### 2.3 What `Run.open` buys the server

`open_total` (**proved**, `Laws/Run.lean:210`): with a `Built` in hand the checked
`HostSession.start` returns exactly the session `Run.open` builds — five identity refusals
impossible because the header is built from the `Built`, the admission refusal impossible
because the certificate is what admission produces. A host without a certificate calls
`Api.Runner.load` (`Api/Runner.lean:56`), whose refusal includes `.program why`. **This is the
whole argument of §4**: `run.open` cannot fail in a Lean server and can in any other.

### 2.4 Where the reactor lives when the agent is the host

Nowhere. The agent is not a `Reactor`; it is the *driver*, and the loop is pull: `run.observe`
→ read `awaiting` → `run.answer key completion`, with `Rows.answer` building the claim from the
machine so the agent supplies only the key and the completion. `Run.drive` still matters,
because it records the same rows. **Tested**: the hand-answered run and a `Run.drive` with a
two-case reactor reach an 8-row journal with the identical phase list and exit, and
`play (Rows.answerAll …)` equals the driven run's observation — `drive_eq_play` (**proved**,
`Laws/Run.lean:177`). So expose `run.drive` only with a **named server-side** reactor
(`"kv-memory"`, `"testclock"`, `"echo"`), never one from the wire. Decision D4.

### 2.5 The exact call sequence

For the E2 kv module (`Test/Program/AuthorContract.lean:116-121`); every value is **tested**.

```
1 program.build {program,table}   → ty=option string / prod string string, closed, 321 bytes,
                                    rowNames=[Kv.make 0, get 1, set 2, remove 3, has 4]
2 run.open      {build,"kv-1"}    → state=idle, journal=0                  [cannot refuse]
3 run.control   {"start"}         → [progressed]; awaitingAsync, outcome=frontier,
                                    awaiting=[{fiber 0, token 0, external 0, unit}],
                                    reasons=[awaitHost{0,0}], fibers=[{0, root}]
4 run.observe   {}                → the same Observation (inspect reads only)
5 run.answer    {{0,0}, nat 0}    → [bound, preflight, applied]; applied=1,
                                    awaiting=[{0, 1, external 1, list[handle(7,0),"greeting"]}]
6 run.answer    {{0,1}, some "hello"}
                                  → [bound, preflight, applied]; terminated, finished,
                                    exit=success(some "hello"), awaiting=0, applied=2
7 run.control   {"flush"}         → [progressed]; already terminated
8 run.journal   {}                → 8 rows
9 run.replay    {build,"kv-1",journal} → identical Observation and phases, no host called
```

Three facts from that sequence the plan did not have:

- **The flush at step 7 is a no-op here.** The second answer terminates the run; the ordinary
  `[evaluate, flush]` tape (`runPure`) is for a program that parks a dispatcher. A driver must
  decide flush by the observation, not by convention — `Run.drive` does (`Run.lean:300-308`).
- **Step 5's answer creates step 6's request, and it carries a live handle**:
  `Val.list [Val.handle 7 0, Val.str "greeting"]`. See §3.4.
- **An answer's three rows cost 2051, 187, 73 bytes** (2138, 213, 74 for the second call): the
  `bind` row is 89% of it, and it is the row table, carried by value in every `Call`
  (`Api/HostSession.lean:32-40`). Decision D7.

## 3. Every response is first-order data with an Effect Schema — checked

### 3.1 The census, by `#synth`

I probed 43 types (probe 1). **28 have a `Canonical` instance; 15 do not.** Present, each named
by the instance the build resolved: `Command`, `Option Phase`, `Header`, `Call`, `Reply`,
`HostSession.Refusal`, `HostProtocol.State`, `HostProtocol.Key`, `Api.Outcome`,
`FrontierReason`, `Machine.Stuck`, `Api.Program` (= `Eff NativeOp`), `EffTy`, `Row`, `NativeOp`,
`Store.Val`, `ShapeDoc`, `AdmitRefusal`, `TableRefusal`, `ExitV`, `Await`, `List Await`,
`RowTable`, `List Row`, `FiberId`, `Api.Decision` (= `RunDecision`), `Completion`,
`ForkOptions`. Absent, in three classes:

| type | verdict |
| --- | --- |
| `Run.Observation` (`Run.lean:220`) | **the gap.** Group `Runner`; the structure's own group was never emitted and **every field's instance exists** |
| `Api.FiberStatus` (`Api/Supervision.lean:197`) | **the gap.** Group `Runner`, *before* `Observation`, which holds it |
| `Api.ForkSite`, `Api.ForkKind` (`:52,76`) | **the gap.** Group `Runner`; needs `Term` and `ForkOptions`, both present |
| `Api.BuildRefusal` (`Api/Author.lean:30`) | **the gap.** Needs the two below |
| `Program.TypeRefusal`, `TypeReason` | **the gap.** `TypeReason`'s 24 cases hold `Term`, `CauseTerm`, `Ty`, `Decision`, `Lit`, `ServiceKey` — all present |
| `Authoring.Refusal`, `Authoring.Reason` | **the gap.** `Reason`'s fields are strings and paths |
| `Api.AuthorRefusal`, `PrintRefusal`, `Api.Budget` | the gap, trivially |
| `Api.Inspection` (`Api.lean:274-277`) | **must not cross**: it holds `Api.Machine`. `Observation` is the reading that does |
| `Api.Machine` | **must not cross** (the machine codec is item C of the engine note) |
| `Api.Built` | **must not cross**: `admitted` is a `Prop` record. Wire form = program bytes + table bytes |
| `Run` | **must not cross**: it holds a `Session`, which holds a machine. Wire form = the journal |
| `Effect4.Document` | not a gap: `Codegen.Schema.generate?` prints it |

Of the eight types the brief names: `Command`, `Await` (published as `"Outstanding"` for the
list) and `Phase` (published as `"Verdict"`) have one — **three of eight**. `Observation`,
`Inspection`, `ForkSite`, `FiberStatus` and `BuildRefusal` do not — **five of eight** — and
exactly one of those five (`Inspection`) is not a codec gap but a boundary violation.

### 3.2 The payload chain already exists — and this is the finding

For every one of the 28, three things are already callable. **The JSON an MCP response carries**:
`ShapeDoc.print (Canonical.shape T) (Canonical.toVal x)` (`Store/Shape.lean:539`) names fields,
writes `_tag` for a sum and renders an all-nullary sum as a bare string. **The Effect Schema the
tool advertises**: `(Canonical.shape T).document` (`Store/Shape.lean:468`) then
`Codegen.Schema.generate?` (`Codegen/Schema.lean:468`), which emits a module exporting
`<Name>Json : Schema.Json` and
`<Name> : SchemaRepresentation.Document = SchemaRepresentation.fromJson(<Name>Json)`. And **the
bytes**: `Canonical.encode` / `Canonical.decode`. **Tested** on real values from the kv run —
one journal row, then the two most-read readings:

```json
{"_tag":"submit","reply":{"version":2,"session":"kv-1","callId":0,
  "key":{"fiber":{"value":0},"token":0},
  "completion":{"_tag":"ofExit","exit":{"_tag":"success","value":{"_tag":"nat","n":0}}}}}
"awaitingAsync"                                          // HostProtocol.State
{"_tag":"refused","reason":{"_tag":"noCall"}}            // Option Phase, i.e. "Verdict"
```

So "every response carries an Effect Schema" is **already true at runtime** for 28 types, and no
new emitter is needed for them — only the calls. What is missing is narrower and different:

- **a static TypeScript type.** `ts/eff/eff.gen.ts` gives `Schema.TaggedUnion` plus
  `typeof X.Type` for **23 families, all of them the program IR** (`Ty` … `EffTy`, ending at
  `Row` and `EffTy`) and **zero** session, runner or observation types. The missing work is the
  `TsGen` family list (`tools/Tools/TsGen.lean`), not a schema printer.
- **`Repr`.** **Tested**: none on `Observation`, `FiberStatus`, `EffTy`, `NativeOp`, `ExitV` or
  `TypeReason`. `Val.render` (`Store/Val.lean:192`) and `TypeReason.head`
  (`Program/Typing/Blame.lean:72`) are the only two human renderings in the reading surface.
  Not on the MCP critical path (§2.5's table uses renderers I wrote); fatal for a CLI.

### 3.3 The generator groups the ten missing ones go in

`tools/Effect4Gen/manifest.json` has 19 groups; the codec ones are `Json`(2), `Schema`(13),
`Program`(20), `Pin`(3), `Api`(4), `Value`(4), `Runner`(19).

- **Group `Runner`** (`src/Effect4/Api/RunnerDerived.lean`): append `FiberStatus`, then
  `Observation`, then `ForkKind`, `ForkSite`. Order matters — the group requires every applied
  carrier before the type holding it, and `Observation.fibers : List (FiberId × FiberStatus)`
  needs `FiberStatus` first. `RunnerBytes.schemas` (`Api/RunnerBytes.lean:78`, eight entries)
  then gains `"Observation"` and `"Supervision"`, and `Run.observeBytes` becomes writable.
  This is the run receipt's O-8, whose §6 field table I verified instance by instance (`State`
  `RunnerDerived.lean:1462`, `Outcome` `:1589`, `Exit` `:473`, `Key` `Api/Derived.lean:133`,
  `FrontierReason` `:278`, `List Await` by `instCanonicalList`).
- **A new group `Refusals`** (`src/Effect4/Api/RefusalsDerived.lean`): `Authoring.Reason`,
  `Authoring.Refusal`, `TypeReason`, `TypeRefusal`, `AuthorRefusal`, `BuildRefusal`,
  `PrintRefusal`, `ReadRefusal` — eight types, one group, every refusal an agent can be shown.
  Nothing in it is new: `TypeReason`'s heaviest field is `Term`, which `Program`'s group emits.
- Both groups touch the compatibility policy, which names the derived types as consumer
  additions (`Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`) and calls a change to
  it a review event.

### 3.4 Two shape defects the MCP face will meet on day one

- **`Await` is an `abbrev` for a nested product** (`Program/Admit.lean:37`:
  `FiberId × Nat × NativeOp × Val`), so its JSON is `[[{"value":0},[0,[…]]]]` — nested arrays,
  no field names, on the most-read response field. A structure `{fiber, token, op, request}`
  fixes every reader at once. Decision D6. (Same for `Observation.fibers`, `Built.rowNames`.)
- **A live handle crosses, and the schema accepts it.** The `get` call's request is
  `Val.list [Val.handle 7 0, Val.str "greeting"]`. **Tested**: `commandOf ∘ commandBytes = id`
  on that row, so a decoder gets `Val.handle 7 0` back, and under the generated `Val` sum it
  prints as a *legal* case, `{"_tag":"handle","kind":7,"key":0}` — not the unfitting-value
  fallback `{"handle":7,"key":0}` (`Store/Shape.lean:525`). A receiver therefore cannot refuse
  it on schema grounds. In one process that is right; across two, machine A's handle is not
  machine B's. `Api/RunnerBytes.lean` calls this "a policy above this module"; the MCP face
  **is** that module. Decision D8.

## 4. What is generated, what is hand-written

**Recommendation: a Lean `--run` driver first (`src/Tools/McpRun.lean`), generated Effect
TypeScript on bun second, with one `ToolSpec` table read by both.** The reason is not
preference. It is `Built`.

1. **A `Module` cannot cross any boundary.** `Module.main : Src NativeOp = Env → List Nat →
   Except Refusal (Eff Op)` (`Program/Authoring.lean:110,318`) is a Lean function. A bun server
   can only receive an *elaborated* `Eff` plus a `RowTable`, so `Author.build` — the point of
   today's author face, and the only call that resolves `Row.call "get"` to a position — is
   reachable from a Lean host and nowhere else.
2. **A certificate cannot cross either.** `Built.admitted` is a record of `Prop`s. A bun server
   re-derives admission inside `HostSession.start` and can answer `Refusal.program why`; a Lean
   server calls `Run.open`, and `open_total` says it cannot. The two servers have *different*
   tool 8, and only the Lean one is the one the laws describe.
3. **The memory rule already places it.** Native IO tooling here is a Lean `--run` driver under
   `src/Tools`, because the axiom gate walks every `.lean` under `src/Effect4` and `Test/`.
   `src/Tools/McpRun.lean` with a `main`, run by `lake env lean -M4096 --run …`, is that shape.

The bun server is for a host with no Lean (browser, worker, the OCaml engine's sibling): tools
8–14 over the bytes boundary (`RunnerBytes`), plus a `program.load` taking program bytes + table
bytes and answering `HostSession.Refusal` — **not** `program.build`.

**What the generator must emit**, three artefacts from one table:

| artefact | from | exists? |
| --- | --- | --- |
| the `ToolSpec` table — 14 rows: name, description, input/output/refusal schema names, read-only flag | one Lean value at `src/Effect4/Tooling/ToolSpec.lean` | **does not exist** (layout note §2 lists it "new (R12)"; scout B §2.4 has the columns) |
| the Effect Schema per boundary name | `Canonical.shape T → ShapeDoc.document → Codegen.Schema.generate?` | **exists** (§3.2, tested) |
| the static TS types and the typed client | `tools/Tools/TsGen.lean`, in `eff.gen.ts`'s conventions, drift-checked by `make check-gen` | **family list covers the program IR only** (§3.2) |

The table belongs **inside** the gate (`src/Effect4/Tooling/`) as audited data; the driver
**outside** (`src/Tools/`) so it can do IO. Decision D10.

One cost to state plainly. **Tested**: the Effect Schema text for `Command` is **231 660
characters** with 7 references and its `ShapeDoc` is 20 006 bytes, because `Header` and `Call`
inline the whole `Row`/`Ty` closure — a tool advertising `Command` as its input schema ships a
quarter of a megabyte (`Outstanding` has 2 references). Same fact as §2.5's 2051-byte bind row;
answer D7 before either emitter runs.

## 5. The dogfood transcript

One agent session over the E2 kv package. Every JSON value is `ShapeDoc.print` of a real value
from probes 2, 5, 6 and 7, field names and `_tag`s included, except where marked `⟨GAP⟩` — those
types have no `Canonical` instance and so no printer, and their spelling is mine (**assumed**).
Every other named type has a runtime schema and **no** static TypeScript type (§3.2).

```jsonc
→ program.build {"program":"<321 bytes>", "table":"<bytes>"}            // Eff, List Row
← {"buildRef":"b1", "closed":true,
   "ty":{"answer":{"_tag":"option","inner":{"_tag":"string"}},          // EffTy
         "error":{"_tag":"prod","left":{"_tag":"string"},"right":{"_tag":"string"}},
         "requires":[]},
   "rowNames":[["Kv.make",0],["get",1],["set",2],["remove",3],["has",4]],
   "printed":"Effect.flatMap(Kv.make(), (a0) => a0.get(\"greeting\"))"}
// refused: {"_tag":"scope","refusal":{"path":[],
//            "reason":{"_tag":"unboundRow","spelling":"Kv.missing"}}}   ⟨GAP BuildRefusal⟩
//     or:  {"_tag":"typing","refusal":{"path":[],"reason":{"_tag":"requestNotSubtype",…}}}

→ run.open {"buildRef":"b1","id":"kv-1","budget":{"fuel":1000,"compileFuel":1000}}  ⟨GAP Budget⟩
← {"runId":"kv-1","observation":{"state":"idle", …}}                     ⟨GAP Observation⟩

→ run.control {"runId":"kv-1","decision":"start"}
← {"phases":[{"_tag":"progressed"}],                                     // Phase
   "observation":{"state":"awaitingAsync",                               // State (bare string)
     "outcome":{"_tag":"frontier"}, "exit":null,                         // Outcome, ExitV
     "awaiting":[[{"value":0},[0,[{"_tag":"external","index":0},{"_tag":"unit"}]]]],
     "pending":[],"retired":[],"applied":0,                              // Await: §3.4
     "reasons":[{"_tag":"awaitHost","key":{"fiber":{"value":0},"token":0}}],
     "fibers":[[{"value":0},{"_tag":"root"}]]}}                          ⟨GAP FiberStatus⟩

→ run.answer {"runId":"kv-1","key":{"fiber":{"value":0},"token":0},      // Key
   "completion":{"_tag":"ofExit","exit":{"_tag":"success","value":{"_tag":"nat","n":0}}}}
← {"phases":[{"_tag":"bound"},{"_tag":"preflight"},{"_tag":"applied"}],
   "observation":{"state":"awaitingAsync","applied":1,
     "awaiting":[[{"value":0},[1,[{"_tag":"external","index":1},
       {"_tag":"list","xs":[{"_tag":"handle","kind":7,"key":0},
                            {"_tag":"str","s":"greeting"}]}]]]]}}        // handle crossed: §3.4

→ run.answer {"runId":"kv-1","key":{"fiber":{"value":0},"token":1},
   "completion":{"_tag":"ofExit","exit":{"_tag":"success",
     "value":{"_tag":"some","a":{"_tag":"str","s":"hello"}}}}}
← {"phases":[{"_tag":"bound"},{"_tag":"preflight"},{"_tag":"applied"}],
   "observation":{"state":"terminated","outcome":{"_tag":"finished"},"applied":2,"awaiting":[],
     "exit":{"_tag":"success","value":{"_tag":"some","a":{"_tag":"str","s":"hello"}}},
     "fibers":[[{"value":0},{"_tag":"exited", …}]]}}

→ run.answer {"runId":"kv-1","key":{"fiber":{"value":0},"token":1}, …}   // the same key again
← {"phases":[],"observation":{…unchanged…}}
// answer_once: the rows are built from the machine and it holds no call there. Tested:
// Rows.answer = 0 rows — not a refusal, no rows at all.
→ run.journal {"runId":"kv-1"}
← {"rows":[2051,187,73, 2138,213,74, 65,38]}   // sizes; the two binds are 87% of the traffic,
                                               // because each Call carries the table. D7.
→ run.replay {"buildRef":"b1","id":"kv-1","journal":[…8 rows…]}
← identical phases, identical observation, no host called.   // journal_replays, tested
```

## 6. Decisions for the owner

**D1 — fourteen tools, `run.play` withheld.** *Recommend yes.* A tool taking journal rows makes
the agent invent a `Call`; `Call.at` + `bindCall_at` exist so it never does, and eleven readings
collapse into `run.observe`. The thin `play`/`step` pair STATE.md describes under "the generated
session as the engine's host API" is the bun server's surface, not the agent's.

**D2 — the server holds the journal, not the `Run`.** *Recommend yes, journal-first.* `Run` has
no codec and must not get one; `journal_replays` makes the fold the definition and the cached
`Run` an optimisation. Runner plan §4b's rule, now decided by a theorem.

**D3 — `Built.digest` and the run's wire identity.** *Recommend:* add `Built.digest` over
`programBytes ++ tableBytes`; the wire identity is `(digest, Run.id)`. Today two builds against
different tables have the same `Built.bytes`. `Canonical RowTable` exists, so this is one line.

**D4 — no reactor over the wire.** *Recommend:* the agent is the driver (`observe` + `answer`);
`run.drive` is exposed only with a server-side reactor named from a registry. A `Reactor` is a
Lean function and cannot be sent; `drive_eq_play` means both routes write the same journal.

**D5 — the two generator groups.** *Recommend both, `Runner` first.* Group `Runner` gains
`FiberStatus`, `Observation`, `ForkKind`, `ForkSite` in that order (O-8, unblocking
`run.observe` and `Run.observeBytes`); a new group `Refusals` gains the eight refusal types of
§3.3, closing every refusal an agent can see. Both touch the compatibility policy.

**D6 — `Await` becomes a structure.** *Recommend yes.* `FiberId × Nat × NativeOp × Val` prints
as nested arrays with no field names on the most-read response field; `{fiber, token, op,
request}` fixes every host at once. It is a widely used `abbrev` (`Program/Admit.lean:37`), so
a real change — but the alternative, a projection in the MCP layer, duplicates a representation.

**D7 — the row table must not travel by value.** *Recommend a digest now, the store later.* The
runner plan's settle-item 1 defers this to the store (§6); the digest half needs only
`Canonical RowTable` (exists) and a hash. The MCP face pays the cost per call: 89% of an
answer's bytes and a 231 KB advertised input schema for `Command`.

**D8 — a described handle.** *Recommend:* refuse a row whose request or completion describes a
handle **when it arrives from another process**, admit it in-process. The schema accepts it
either way (§3.4), so it cannot be a schema check; `RunnerBytes` calls it "a policy above this
module", and the MCP face is the only module that knows who the sender is.

**D9 — Lean driver first, bun server second.** *Recommend yes,* for §4's three reasons. A
bun-first order ships a server whose `run.open` can refuse and whose `program.build` cannot exist.

**D10 — where the `ToolSpec` table lives.** *Recommend:* the table inside the gate
(`src/Effect4/Tooling/ToolSpec.lean`, audited data), the driver outside (`src/Tools/`, IO). Both
emitters read the table, so drift is a `make check-gen` failure.

**D11 — re-cut R12's first slice.** *Recommend:* the run protocol (these fourteen tools) first,
the inspection protocol second. Four of R12's nine `InspectOp` commands are buildable today and
five need `Doc` or the store, neither of which exists; §4.14b's ordering predates `Run`.

**D12 — skip `Repr`, generate a `head` instead.** *Recommend:* no `Repr` on the reading types;
emit one `head : T → String` per sum from the generator (the pattern `TypeReason.head` sets), so
a CLI has a word and the MCP payload keeps using `ShapeDoc.print`. The run receipt lists
`Repr Observation` as owed; close it this way rather than with a derived instance, which on a
nested inductive becomes `partial` and the trust gate refuses it (`Store/Val.lean:172-176`).

## 7. Where the tree contradicted the brief

1. **`Canonical RowTable` exists.** The run seat receipt's owed item 3 says `Run.openBytes`
   "needs a `Canonical RowTable`, which does not exist". `RowTable` is `List Row`
   (`Program/Native.lean:134`), `Row` is in the `Program` group, and the generated `Header`
   codec already uses `Canonical (List Row)` (`Api/RunnerDerived.lean:856-861`). **Tested**:
   the `#synth` succeeds. So `openBytes` needs only a `Built` wire form (D3), not a new codec.
2. **`src/Effect4.lean` imports `Effect4.Run`.** The same receipt's owed item 6 says it does
   not. At `d798feb2` `:139-145` import `Api.Runner`, `Api.RunnerBytes`, `Api.Built`,
   `Api.Author`, `Api.Supervision` and `Effect4.Run`. Closed by the coordinator's merge.
3. **`ShapeDoc` already has both a document and a printer.** The brief's §3 asks which types
   "need only the structure's own group", implying the schema half is the work. It is not:
   `ShapeDoc.document` (`Store/Shape.lean:468`) and `ShapeDoc.print` (`:539`) make the codec
   *be* the schema and the JSON printer. The missing emitter is the static TypeScript type.
4. **No `Doc` and no `InspectOp` anywhere.** The brief lists `render`, `window`, `spans`,
   `locate` among commands that might survive as tools. They cannot: there is no `Doc` type,
   and `grep -rn InspectOp src/ tools/ ts/ harness/ ocaml/` is empty. The one mention of MCP in
   the tree is a comment at `src/Effect4/Codegen/Target.lean:44`.

## 8. What I did not do

No gate (`make check`, `check-host`, `check-full`, `check-gen`) and no axiom print, so nothing
here is **stamped**; all seven probes are `lake env lean` on scratch files under my scratchpad,
no worktree file was edited and no `.olean` written outside the warm cache. I did not read
`Api/RunnerDerived.lean` in full (1759 lines) — §3 is its instance headers plus `#synth`. I did
not touch the OCaml side and ran nothing on bun. Two things are **assumed**: that a `Module`
cannot cross a boundary (from `Src Op`'s type, `Program/Authoring.lean:110`, not from a failed
codec attempt), and §4's account of what the generator must emit (from the manifest and
`TsGen`'s header; I ran neither generator).
