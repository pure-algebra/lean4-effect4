# The cut survey at 774ddc3d7

Status: survey (history, not authority). A read-only agent collected every cut that the reviews name and checked each against `774ddc3d7`. The coordinator's rulings on its unsure rows are in `cuts.md`.

## Cut survey at `774ddc3d7` (read-only, every name checked with grep)

**Source gaps.** There is no round-1 Codex review file under `reviews/`, and `landing-1-codex.md` has not been written. For round 1 I used the ledger's Round 1 section and the refactor assessment.

**Already gone, nothing to do:**
- `kit_gen.ml`
- the rerooting `parray`
- the G2 tolerances `k1_pending` and `m2_pending`
- the `test_bytes.ml` pin "tag 13 refused"
- the duplicate engine signatures (slices 0.3 and 0.5 landed)
- Rocq's hand-transcribed tree (`rocq/Skeleton.v` is now generated)
- landing-1 Q7's `rocq/tools/split_types.ml` item: the tool already reads the module layout
- the tool's `run` arm losing services (slice A fixed it)

**Source abbreviations:** EP = estate `plan.md`; L1 = `landing-1-brief.md`; R2 = Codex round 2; CAS = `cas/README.md`; AUD = `cas/audit.md`; RA = the refactor assessment; AS = `authoring-and-store/README.md`; SC = `session-composition/plan.md`; CR = its `codex-review.md`; TD = `tooling-design` §5; RR = the Rocq CAS receipt; BR = your list.

### Lean core

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| `Store.putOr` (`src/Effect4/Store/Domain/Store.lean`) | BR | yes | none anywhere; its docstring says "three families build stores by folding this", which is false | **CUT NOW** | delete it; keep `putRootOr` (CasGoldens uses it) |
| `CascadingStore` (`src/Effect4/Store/Domain/Cascade.lean`) and its `export` in `src/Effect4/Api.lean` | AS §5 "two tiers"; AUD gap 6 | yes | one test (`Test/Codegen/SchemaGenerationContract.lean`) | **CUT NOW** (unsure, see below) | delete the module, the export and the test section. `Word.Layered`/`LocalFirst` (proved) stays the one two-tier owner. Cascade's `putLocal` checks edges against the local tier only |
| `Api.Author.buildIn` cited in the `Module.types` docstring (`src/Effect4/Program/Authoring.lean`) | BR | yes | none: no such declaration exists | **CUT NOW** | say `Api.Author.build`. This is the only dead `Api.Author.*` citation |
| Turning a document into a `Built`, done by hand twice (`start` and `run` arms of `tools/Tools/Session.lean`; only `start` sets `rowNames`) | AS §3; SC §5 | yes | the tool | CUT WITH SLICE **S4** | one declaration beside `Built` |
| Admission reruns: `Run.Kit.admit` (partial), `Run.Preview.admit`, `HostSession.start`, `LiveRecord.restore` | AS §3 | yes | lowered kit (`roots.json`), the tool | CUT WITH SLICE **S4** | named restrictions of `admitProgram`; `Kit.admit` stays as a root |
| Run entry points `Run.runPure`, `Api.Runner.load`, `HostSession.start`, `Typed.replay`, `Live.start` | AS §3 | yes | `Api/Author.lean`, `Run/Live.lean`, tests | CUT WITH SLICE **S4** | `Live.open` from a `Built`; raw `Api.run`/`replay`/`runSync` stay as test uses |
| `Doc.undo` (`src/Effect4/Program/Typing/SourceDocument.lean`) | SC §3 (H2) | yes | the tool's `undo` | CUT WITH SLICE **S1** | an append-only revert of a named entry |
| Tool `State.source/journal/docId/revision`, and the second `feedStep` in the commit and publish arms | AS §3 | yes | `tools/Tools/Session.lean` | CUT WITH SLICE **S1**, then **S3a** | `Doc` owns the history; `Doc.step` returns the step |
| `Tools.Session.Snapshot` (`Cache`, `resolve_agrees`) | CR, AS §3 | yes | only `Test/Program/SketchAdmissionControls.lean`. Its named consumer, an "experimental MCP preview driver", does not exist; `Tools.Session` does not import it | CUT WITH SLICE **S1** | `Doc`'s replay-proved cache replaces it |
| `Tools.Session` dispatcher (26 ops, 41 optional fields, including the `run` op that duplicates start + play, and `fills.materialize`) and `Tools.Query` as protocol source | TD §5; SC S3b; CR | yes | `tools/Drivers/*`, `Tools.View.*` | CUT WITH SLICE **S3a** (core), **S3b** (old dispatch deleted) | flat `Request`/`Answer` plus `serve`; the drivers stay thin |
| `JsonBridge.valueFrom?`: hex wins when hex and JSON both arrive | AS §3; SC §7 | yes | the tool | CUT WITH SLICE **S3b** | one generated encoding per field |
| Checking written several times (`Sketch.check`, `Run.Kit.check`, `Tools.Query` `check`) | AS §3 | yes | tool, kit | CUT WITH SLICE **S3a** | each calls `Sketch.sourceCheck` or `Api.check` |

### Lean laws

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| `address_inj` (`src/Effect4/Store/Domain/Node.lean`): its premise is `Function.Injective sha256`, so it says nothing | CAS; AS §8; RR | yes | `Test/Store/NodeContract.lean` (`example`), a docstring in `Test/Store/ProgramContent.lean` | **CUT NOW** | replace with `address_inj_resident` (RR proposal 1); drop the `example`; edit the Node.lean module doc and `Test/Counterexamples/REGISTER.md` row `E4-CAS-CE-006`, which mentions "level 1" |
| `Pin.holds_of_injective` (`src/Effect4/Store/Domain/Pin.lean`) | AS §8; RR | yes | none | **CUT NOW** | delete it; keep `holds_or_collision`; fix Pin's module doc |
| `putNode_fresh_closed` (Store.lean): "the brief's name" for `putNode_closed` | BR | yes | none | **CUT NOW** | delete |
| `verify_sound'` (Word.lean): projection of `verify_sound` | BR | yes | none | **CUT NOW** | delete |
| `wf_closed` (Word.lean): "the brief's form", a weaker `wf_apply` | sweep | yes | `ocaml/engine/cas/e4_cas.mli` (G6), a Test `example` | KEEP (unsure) | could go if `e4_cas.mli` cites `wf_apply` instead |

### Tools

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| `tools/Conform/Effect4/mirrors.json` rows for `eff_types.ml` (`ty`, `registration` type blocks), `ctor_index_ty`, `ctor_name_ty`, `json_ty`, `emit_ty` (all `stripPrefix "Ty_"`), and the `prop_wire.ml` row's reason (`prop_wire.ml:171`, `Ty_causeOf`) | L1 Q7 | yes; the file now has `Ty.t` and `Ty.Never` arms | `tools/Conform/Cli/Audit.lean`, which no Makefile target runs, so the rows rot silently | **CUT NOW** | re-key to `… : Ty.t -> int =` and the like with `stripPrefix "Ty."`. Either drop the two type-block rows or teach the reader `module Ty = struct type t`. Update the reason text |

### OCaml engine

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| `E4_nat` (`ocaml/engine/bytes/e4_nat.ml(i)`) | EP §5; RA; R2-C-8 | yes | no code caller: only `bytes/test/test_math.ml` and comments citing `E4_nat.max_nat`. Its division rows went with decisions row 404; `Lcnf_nat` and the exact runtime replace it | **CUT NOW** | delete it and test_math's N* cases; comments say `max_int` |
| `E4_log.Vec`, an alias of `Lcnf_array` | L1 Q2 | yes | `e4_logindex.ml`, `e4_trace.ml`, `bench_array.ml`, tests | **CUT NOW** | callers name `Lcnf_array` |
| `E4_trace.to_list` (hand array fill) beside `Lcnf_array.to_list` (fold, then reverse) | L1 Q2 | yes | engine trace | **CUT NOW** | move the faster body into `Lcnf_array.to_list`; `E4_trace.to_list = Lcnf_array.to_list` |
| `ocaml/engine/bench/bench_array.ml` | EP D-3, §6a | yes | none (an executable) | **CUT NOW** | D-3 was settled at `7eaaf9257` and the list shim it measures is gone since 3.2; remove it from `bench/dune` |
| Lean `File.lean:N` citations in hand engine headers, about 360 sites (for example `Fibers.lean:585-587` is now elsewhere, and so is `Stores.lean:1120 refPoke`) | L1 Q7 | yes | docs | **CUT NOW** | cite declarations, not lines. Start with `e4_table.mli`, `e4_engine.mli`, `e4_log.mli`, `e4_trace.ml(i)`, `e4_memo*.ml(i)`, `e4_buckets*`, `e4_fibers_view*`, `api_engine_prelude.ml` |
| `test/api_gen_inst.ml` (third adapter), `Gen_engine` in `test_diff.ml` and `e4_engine_bench.ml` | L1 Q2; R2-C-12 | yes | tests only | CUT WITH SLICE **3.6** | the lowered list reference replaces it; `api_gen.ml` stays (it holds other roots) |
| The seven list twins (`E4_{table,trace,memo,buckets,ppath,env,fibers_view}_list`), `Api_engine_ref`, `E4_engine.Ref` | EP §5 | yes | tests, `test_scenarios` | CUT WITH SLICE **3.3–3.6**, one family at a time | delete as each family's successor serves `test_diff` |
| `ocaml/engine/tools/api_engine_prelude.ml` (`sh_api_load`, `sh_spawn`, `sh_ref_step`, …) and `externs.txt` rows | EP §5; R2 | yes | generated `api_engine.ml` | CUT WITH SLICE **3.3–3.6** | lower the machine operations |
| `Kit_author` hand wrappers | EP §5 | yes | `test_kit`, `test_rocq` | CUT WITH SLICE **1.4** | generated adapters |
| Hand `REPO` (`test/todo/native_todo.ml`) | EP §5 | yes | the to-do lane | CUT WITH SLICE **1.5** | generated host module type |
| `Kit_serve` request execution (`answer`, `request_of_json`) | EP §5; R2-C-10; R3-C-7 | yes | `kit/bin/eff.ml`, transcripts | CUT WITH SLICE **1.7**, after S3a and S6 | keep parsing, framing and input/output only |
| `OCaml5.Lcnf.ClockFlow`, `Lcnf_nat`'s saturating helpers, and `fidelity`/`domain` beside `receipt` in `Builtins.lean` and `TypeRows.lean` | EP §5; RA; L1 Q2 | yes | `Translate.lean`, generated code | CUT WITH SLICE **2.2b part 2** (ClockFlow under 2.4's conditions) | `receipt` becomes the contract |
| `E4_clock.Profile_refusal` exception; the crossing and refusal types | EP §6a; L1 Q2 | yes | `e4_host`, `e4_engine`, `e4_diff` | CUT WITH SLICE **2.3** | one refusal value in `ocaml/lcnf` |
| Per-file test `check` and counters (about 45 files) | L1 Q2 | yes | tests | CUT WITH SLICE **6.5** (D-6) | one test library |
| `E4_host.serve`, a hand copy of `driveFrom` | SC §8 | yes | the host drive | KEEP until **LC-8 / S6** | none |

### OCaml CAS

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| The decode-refusal mapping written three times: `check_pure`, `put_bytes`, `readmit_tail` in `e4_cas.ml`; recovery reports `Unknown_tag` as `Oversize` | CAS §3a; AS §5 | yes | the store | **CUT NOW** | one mapping function, used three times |
| `E4_pack.Bad_pack` raised by recovery inside a sealed segment, re-raised as `Store_error` | CAS; AS §8 (decided) | yes | `e4_cas.ml` | **CUT NOW** | a value of the recovery result |
| `e4_wal.mli` header cites `ocaml/engine/query/e4_log.mli` (gone) and says `replay` feeds `E4_log` (nothing does) | AUD; CAS §4 | yes | docs | **CUT NOW** | fix the text; the module stays (run-node target) |
| Pre-move paths (`src/Effect4/Store/{Val,Node,Store,Digest,Canonical,Word,Kind}.lean`, `Program/Wire.lean`, `Lib/Deque.lean`) in about 40 files | AUD gap 4 | yes | docs | **CUT NOW** | rewrite to `Store/Carrier/*` and `Store/Domain/*`. Files: CAS `.mli` (`e4_shape`, `e4_node`, `e4_addr`, `e4_control`, `e4_cas`, `e4_checkpoint`), `bytes/*.mli`, `eff_frame`, `e4_buckets*`, `CasGoldens.lean`, `Effect4Gen/{Main.lean,manifest.json}`, `TestSupport/CasEntry.lean`, the Store tests |
| `g2-handle-in-content` named exception (`goldens/manifest.txt`, `test_cas.ml`) | CAS; AS §8 | yes | G2 | CUT WITH SLICE **M2** | Lean `putNode` refuses `handleInContent`; re-cut G2 |
| `E4_checkpoint.schema_node`, a stand-in "pending" schema beside Lean's `genesisNode` | AS §5 | yes | `E4_checkpoint` | CUT WITH SLICE **run nodes** (after S4) | Lean-owned job and tape shapes |
| `test_shapes.ml` OCaml text digest | CAS C4 | yes | kit lane | CUT WITH SLICE **C4** | pin `specOf` once `render` writes wire tags |
| `E4_cas`, `E4_wal`, `E4_checkpoint`, `E4_chunk`; OCaml root kinds `Registry` and `Pin` | AUD; AS §5–6 | yes | tests only | KEEP: action cache (C6), document history, run nodes | one root-kind table after S3b |

### Generators and docs

| Item | Source | Present? | Users | Verdict | Smallest change |
|---|---|---|---|---|---|
| `ocaml/gen/NOTES.md` gaps row "`Array` as `list` … list shim" | §6a 3.2 | yes; it contradicts the text above it | docs | **CUT NOW** | delete the row |
| `rocq/tools/split_types.ml` | L1 Q7 | yes, already on the new layout | `make gen-rocq` | KEEP | none |
| `harness/truth/session/keyed-*.ts` (hand keyed session) | TD §5 | yes | harness | KEEP until probe 5, by the owner's word | none |
| `plan-v1.md`, `plan-v2.md`, session-composition `README.md` (v1) | — | yes | history | KEEP (history convention) | none |

### Totals

**CUT NOW: 18 rows.**
- Lean core 3: `putOr`, `CascadingStore`, `buildIn`.
- Lean laws 4: `address_inj`, `holds_of_injective`, `putNode_fresh_closed`, `verify_sound'`.
- Tools 1: `mirrors.json`.
- OCaml engine 5: `E4_nat`, `E4_log.Vec`, `E4_trace.to_list`, `bench_array`, the line citations.
- OCaml CAS 4: the decode mapping, `Bad_pack`, `e4_wal.mli`, the Store paths.
- Docs 1: the `NOTES.md` row.

### Unsure

1. **`CascadingStore`:** `Effect4.Api` exports it, and I did not check whether the export feeds anything generated. My grep of `ts/` and `ocaml/` found nothing.
2. **`address_inj`'s replacement form:** AS §8 says "declared from Rocq". Decisions row 411(1) says a statement Lean proves in a few lines must be a theorem, and RR proves it in Lean directly.
3. **`wf_closed`:** I kept it because `e4_cas.mli` cites it.
4. **`bench_frame.ml`:** part 1 (copy, reserve and sizes strategies) is settled by 5.1; part 2 still measures the real writer.
5. **`Tools.Session.Snapshot`:** CUT NOW is defensible, since its named consumer does not exist; I put it with S1.
6. **`E4_trace.to_list`:** its 2x speed claim was not re-measured.
