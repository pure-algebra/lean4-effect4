# 2026-10-18 seat 1 receipt (wave 2): one owner of carrier JSON

**The one thing to know before merging:** the branch edits seat 2's `corpora.ml` and
`stm_tool.ml`, since it deletes `Kit_json`, `Eff_json_text` and `Eff_json`. Keep those edits
through seat 2's moves, then run `make gen-lcnf` once all three seats merge: `ocaml/gen/roots.json`
gains six public roots.

The two files are `ocaml/engine/corpora.ml` and `ocaml/engine/test/stm/stm_tool.ml`, each edited
at its JSON calls only.

Two rulings wait, and neither blocks the merge. The frozen faces contract names
`ocaml/eff/eff_json.ml`, which the brief deleted, as face 7's OCaml implementation (O1). The two
session drivers read JSON text by two parsers, and they differ where no theorem reaches (O2).

Seat 1 of wave 2 (`docs/research/2026-10-18-slices/wave2.md`, "Seat 1"). The four slices C1, A2,
C6 and H7 landed, each as its own commit after its narrow build. Two later commits add the law
helpers' docstrings and pin the kit's JSON text boundary.

## Base and head

- Branch `seat/w2-json`, worktree `/Users/pooks/Dev/wt-w2-json`.
- Base: `b83188cb2`. The branch was not rebased or merged.
- C1, one session fixture: `f17805f63`.
- A2, the located reader in Lean: `5109504c0`.
- C6, the OCaml estate on Lean's JSON: `ca252e848`.
- H7, the kit's warnings: `803109767`.
- A2's helper docstrings: `303522c40`.
- C6's text boundary, described and pinned: `8c0a71dd8`.
- Head: the commit that adds this receipt.

A2's commit regenerates the Lean codecs only. The OCaml closure and `tool-numbers-replies.jsonl`
follow in C6, so `make check-ocaml` holds from C6 on.

## Changed files

### C1 (`f17805f63`, 4 files)

- `Test/fixtures/session/requests.jsonl`: deleted, a byte copy of
  `ocaml/engine/test/kit/tool-requests.jsonl`. No Lean file read it (reading).
- `ocaml/engine/test/kit/bench_tool.ml`: it reads the kit's file, run from the repository's root.
- `ocaml/engine/test/kit/test_tool.ml`: its header names the kit's file as the one copy, with its
  two other readers.
- `scripts/check-mcp-protocol.py`: it reads the kit's file.

### A2 (`5109504c0`, 10 files)

Sources:
- `src/Effect4/Data/NatJson.lean` (new): `NatJson`, the profile's JSON tree, whose numbers are
  naturals. A number the tree does not hold as a natural is a `numeral` with its text. The module
  also holds `JsonStep`, `JsonSite`, `JsonSite.relative`, `NatJson.at?`, `NatJson.limit`
  (2^53 − 1) and `NatJson.render`, the compact text as bytes.
- `src/Effect4/Store/Domain/ShapeJson.lean` (new): `JsonReason`, `JsonRefusal`
  (`Located JsonSite JsonReason`) and the located reader (`readAt` with its mutual steps,
  `ShapeDoc.readLocated`, `Canonical.readLocated`). It also holds Lean's printer to the tree,
  `ShapeDoc.printTree`, which writes each list family as an array. The old `Option` readers are
  the located reader's projections: `ShapeDoc.readAny` and `Canonical.ofJsonAnyOrder`.
  `Canonical.printArrays` is `printTree`'s binary64 image.
- `src/Effect4/Store/Domain/ShapeRead.lean`: `ShapeDoc.order` normalises a list family's array
  through each cell's tail shape (`orderSpine`). The arrays pass (`ShapeDoc.arrays` and its steps)
  and the old two-pass readers are deleted.
- `src/Effect4/Tool/CodecProfile.lean`: `Refusal.unreadable` carries a `JsonRefusal`.
  `readLocated` is the profile's reader, and `read` is its projection on the binary64 tree.
  `natLimit` is `NatJson.limit`.
- `src/Effect4/Tool/Native.lean`: `serveTree`, `refusalTree` and `relativeRefusal`, for the native
  shell and the MCP server. `answer` refuses at the root, with a reason.
- `src/Effect4/Tool/ToolDerived.lean`: regenerated (`make gen-derived`), with the instances of the
  four new wire types.
- `tools/Effect4Gen/manifest.json`: the Tool group gains `JsonStep`, `JsonSite`, `JsonReason` and
  their `Located`, before `CodecProfile.Refusal`.

Laws and battery:
- `src/Effect4/Laws/Store/ShapeRead.lean`: the located reader's laws, listed under "Landed theorems
  and their placement".
- `src/Effect4/Laws/Tool/CodecProfile.lean`: the profile's laws, and `write_read` proved again at
  the new `read`.
- `Test/Program/WireControls.lean`: the red controls, probe 1's four places, and the guards at the
  new refusals.

### C6 (`ca252e848`, 39 files)

Lean:
- `src/Effect4/Store/Domain/ShapeJson.lean`: Lean's printer writes `negInt n` as
  `"-" ++ toString (n + 1)`, because the OCaml route has no `Int.add`.
- `src/OCaml5/Eff/Emit.lean`: the JSON output arm (`jsonOf`, `jsonBind`, `jsonModule`) is
  deleted, and `jsonStr` stays.
- `src/OCaml5/Tools/EffGen.lean`: it writes no `eff_json.ml`. Its docstring says the goldens' JSON
  is `V`'s spelling, which `ts/eff` reads.
- `Test/Codegen/MirrorReaders.lean`, `tools/Conform/Effect4/mirrors.json`: the deleted printer's
  mirror entry is removed.
- `Test/Program/WireControls.lean`: guards at the printer's `negInt` text.

OCaml, the kit (`ocaml/engine/kit/`):
- `kit.ml`, `kit.mli`: `Kit.Json.t` is the generated `nat_json`. `parse` reads text through
  yojson (`Yojson.Raw`) into the tree. `render`, `read` and `print` are Lean's, lowered to OCaml.
- `kit_tool.ml`, `kit_tool.mli`: `serve_tree` and `wire_refused` over the generated `serveTree`.
- `kit_mcp.ml`: the request envelope is a tree, and a codec refusal's path is made relative to
  the tool's arguments (`relativeRefusal`).
- `kit_serve.ml`, `bin/eff.ml`, `dune`: the commands use `Kit.Json`, and the library drops
  `kit_json`.
- `kit_json.ml`: deleted.

OCaml, `ocaml/eff/`:
- `eff_json_text.ml` and the generated `eff_json.ml`: deleted. `dune` and `README.md` follow.
- `test/test_eff.ml`, `test/prop_wire.ml`, `test/test_lean_wire.ml`: each program's print by
  Lean's printer reads back under Lean's reader, both lowered to OCaml. A program with a natural
  above 2^53 − 1 is refused instead.
- `test/test_metadata.ml`: the check of `V`'s JSON spelling is gone. `test/dune`: the three tests
  link `effect4_gen`.

OCaml, the kit's tests (`ocaml/engine/test/kit/`):
- `test_kit.ml`, `test_tool.ml`, `test_transcript.ml`, `test_mcp.ml`, `dune`: they use `Kit.Json`,
  and `test_mcp` reads the transport with yojson.
- `serve.transcript`: four answers rewritten through `E4_KIT_TRANSCRIPT_REWRITE`.
- `tool-numbers-replies.jsonl`: regenerated by `tools/Drivers/Session.lean`. Its third and fifth
  replies carry located refusals.

Outside the brief's list:
- `ocaml/engine/corpora.ml` (seat 2): a local six-constructor JSON tree replaces `Eff_json_text`'s.
- `ocaml/engine/test/stm/stm_tool.ml` (seat 2): its two JSON calls use `Kit.Json`.
- `ocaml/gen/roots.json`: six public roots appended to the `api_gen` recipe, and nothing else.
- Generated by `make gen-lcnf`: `ocaml/gen/api_gen.ml`, `api_gen.mli`, `closure-api_gen.tsv`,
  `facade/effect4.ml`, `facade/effect4.mli` and `public-names.tsv`. The name list gains six values,
  and no path moves or drops.

### H7 (`803109767`, 2 files)

- `ocaml/engine/kit/dune`: the flags `-w -4-9-26-27-32-33-35-37-39-40-41-42-44-45-69-70` become the
  engine's `-w +a-4-9-40-41-42-44-45-70`. Unused values, variables, opens, loop indices,
  constructors, `rec` flags and fields are reported again.
- `ocaml/engine/kit/kit_mcp.ml`: the one finding, warning 48 in `Kit_mcp.line`, is an explicit
  function now. No dead code remained after C6.

### The follow-ups (`303522c40`, 1 file; `8c0a71dd8`, 3 files)

- `src/Effect4/Laws/Store/ShapeRead.lean`: docstrings for sixteen helpers, each naming its claim
  and its consumer. `natOfBinary64_binary64OfNat` gains its placement attribute.
- `ocaml/engine/kit/kit.mli`: `parse` says where yojson's text is wider than RFC 8259.
- `ocaml/engine/test/kit/test_kit.ml`: T2 pins the text boundary, with three controls and nine
  refusals.
- `ocaml/engine/test/kit/test_tool.ml`: N4's note on a number past the int range is corrected.

## Commands and results

Every Lean command ran from the worktree as `python3 /private/tmp/seams-lean-one.py lake …` or
`python3 /private/tmp/seams-lean-one.py make …`. Every `dune` command ran from `ocaml/` as
`opam exec --switch=effect4 -- dune …`.

### C1

| Command | Result |
| --- | --- |
| `dune build ./engine/kit/bin/eff.exe ./engine/test/kit` | built |
| `dune test --force engine/test/kit` | `test_kit: 48 checks, 0 failures`; `test_transcript: 81 checks, 0 failures`; `== ALL PASS: 0 failure(s) ==` |
| `./ocaml/_build/default/engine/test/kit/bench_tool.exe 50`, from the repository's root | `edits 50: first 50 mean 0.327 ms, last 50 mean 0.327 ms` |
| `uv run --with jsonschema==4.25.1 python scripts/check-mcp-protocol.py --binary ocaml/_build/default/engine/kit/bin/eff.exe --schema /Users/pooks/Dev/refs/ocaml-tooling/mcp-spec/schema/2025-06-18/schema.json` | `"status": "PASS"`, `"schema_checks": 87`, `"tools": 20` |
| `dune build @fmt` | exit 0 |

### A2

| Command | Result |
| --- | --- |
| `lake build Effect4.Data.NatJson`, then `lake build Effect4.Store.Domain.ShapeJson` | built |
| `make gen-derived` | `PASS generate: requested producers ran in dependency order` |
| `lake build Effect4.Tool.Native Effect4.Tool.Wire Effect4.Run.Kit Effect4.Tool.Methods` | `Build completed successfully (227 jobs).` |
| `lake build Effect4.Laws.Tool.CodecProfile` | `Build completed successfully (41 jobs).` |
| `make batteries-touched BASE=b83188cb2` | `batteries-touched: 3 batteries`; `Build completed successfully (948 jobs).` |
| `lake build Test.Program.JsonFormControls Test.Program.SessionToolControls Test.Program.QueryControls Test.Program.ToolMethodsControls Test.Store.ResultControls Test.Program.LiveRecordControls Test.Audit.LandingPlanControls` | `Build completed successfully (1179 jobs).` |
| `lake build Effect4.Laws.Tool.Wire Effect4.Laws.Tool.Serve Effect4.Laws.Tool.Exchange Effect4.Laws.Author Tools.WireText Tools.Catalogue Drivers.Session` | `Build completed successfully (752 jobs).` |
| `lake build Effect4.Laws` | `Build completed successfully (1405 jobs).` |
| `lake env lean --run tools/Drivers/Session.lean < ocaml/engine/test/kit/tool-numbers.jsonl` | the 2^53 line and the unknown-case line refuse with a reason at a path |
| `lake env lean <scratch>/AuditA2.lean` | see the axiom output |

### C6

| Command | Result |
| --- | --- |
| `make gen-lcnf`, first run | `FAIL generate`: `todos remaining in closure (fatal): #[Int.add: extern]` |
| `make gen-lcnf`, after the `negInt` change | `PASS generate: requested producers ran in dependency order` (7:01) |
| `make gen-eff` | `EffGen: 31 families, 89 corpus programs`; `PASS generate: requested producers ran in dependency order` |
| `lake env lean --run tools/Drivers/Session.lean < ocaml/engine/test/kit/tool-requests.jsonl`, then `cmp` | equal to `tool-replies.jsonl` |
| the same with `tool-numbers.jsonl` | the third and fifth replies moved; the file is regenerated |
| `lake env lean --run ocaml/engine/test/kit/write.lean <scratch>`, then `cmp` | `verdicts.txt` unchanged |
| `dune test --force engine/test/kit eff`, before the fixes | `FAIL: pIllTupleAtIndex: Lean's JSON print reads back`; `FAIL serve.transcript:81: the answer moved`, and three parse messages |
| `E4_KIT_TRANSCRIPT_REWRITE=… dune test --force engine/test/kit` | `rewrote …/serve.transcript: 40 entries, 4 answers changed` |
| `dune test --force engine/test/kit eff`, after | `test_eff: 739 checks, 0 failures`; `prop_wire: 6345 checks, 0 failures (seed 42)`; `test_lean_wire: 125 checks, 0 failures`; `test_kit: 49 checks, 0 failures`; `== ALL PASS: 0 failure(s) ==` |
| `python3 <scratch>/probe_sites.py ocaml/_build/default/engine/kit/bin/eff.exe /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-authoring-probe/session` | the four places of "What moved on the wire" |
| `scripts/check-mcp-protocol.py`, as in C1 | `"status": "PASS"`, `"schema_checks": 87`, `"tools": 20` |
| `lake build Test.Codegen.MirrorReaders OCaml5.Tools.EffGen OCaml5.Eff.Emit` | `PASS ocaml/eff/eff_ctors.ml: 29 qualified constructors`; `PASS ocaml/eff/eff_wire.ml: 29 qualified constructors`; `Build completed successfully (120 jobs).` |
| `dune fmt`, then `dune build @fmt` | exit 0 |
| `make check-ocaml` | `PASS native: shared result 0f1c25c410ce`; `PASS compiler: shared result 83c962ef8af6`; `PASS ocaml: recorded 085b57ccafdc (114.602s)`; 2,518 `PASS` lines and no `FAIL` |
| `lake build Test.Program.WireControls Test.Codegen.MirrorReaders Effect4.Laws` | `Build completed successfully (1825 jobs).` |
| `make batteries-touched BASE=b83188cb2` | `batteries-touched: 5 batteries`; `Build completed successfully (951 jobs).` |
| `lake env lean <scratch>/AuditC6.lean` | see the axiom output |

### H7

| Command | Result |
| --- | --- |
| `dune build ./engine/kit` at the new flags | `Warning 48 [eliminated-optional-arguments]` in `kit_mcp.ml`, and no other |
| `dune build ./engine/kit ./engine/test/kit`, after the fix | no warning |
| `dune fmt`, `dune build @fmt`, `dune test --force engine/test/kit` | 0 promoted; exit 0; `test_kit: 49 checks, 0 failures`, `== ALL PASS: 0 failure(s) ==` |
| `make check-ocaml` | `PASS ocaml: recorded 11dd279da9b7 (38.784s)`; no `FAIL` |

### The follow-ups and the head

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Store.ShapeRead Effect4.Laws.Tool.CodecProfile Effect4.Laws.Author Tools.JsonBridge Test.Program.JsonFormControls Test.Audit.LandingPlanControls` | `Build completed successfully (1234 jobs).` |
| `dune test --force engine/test/kit` | `test_kit: 61 checks, 0 failures`; `== ALL PASS: 0 failure(s) ==` |
| `make check-ocaml` | `PASS ocaml: recorded ee481e87242e (15.940s)`; no `FAIL` |
| `make batteries-touched BASE=b83188cb2` | `batteries-touched: 5 batteries`; `Build completed successfully (951 jobs).` The five: `Test.Codegen.MirrorReaders`, `Test.Program.JsonFormControls`, `Test.Program.QueryControls`, `Test.Program.ToolMethodsControls`, `Test.Program.WireControls` |
| `lake build Effect4 Effect4.Laws Tools.JsonBridge Tools.WireText Drivers.Session OCaml5.Tools.EffGen OCaml5.Eff.Emit` | `Build completed successfully (1454 jobs).` |
| the session driver on both fixtures, then `cmp` | `tool-replies.jsonl` and `tool-numbers-replies.jsonl` equal |
| `probe_sites.py` and `check-mcp-protocol.py`, as in C6 | the same four places; `"status": "PASS"` |
| `lake env lean <scratch>/AuditC6.lean` | see the axiom output |
| `python3 /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-slices/measure.py`, at the base and at the head | the measures under "Lines removed" |

## Axiom output

Each audit file imports the touched `src` and `Test` modules and runs `#axiom_audit` over them
(`tools/ProofGraph/AxiomAudit.lean`).

- A2, 9 modules: `#axiom_audit: 3522 declarations within [propext, Quot.sound], 0 of them modulo
  planned goals; 0 planned goals`.
- C6 and the follow-ups, 13 modules: `#axiom_audit: 3674 declarations within [propext,
  Quot.sound], 0 of them modulo planned goals; 0 planned goals`. The last run is at the head's
  code.

The thirteen modules:

```text
Effect4.Data.NatJson Effect4.Store.Domain.ShapeRead Effect4.Store.Domain.ShapeJson
Effect4.Tool.CodecProfile Effect4.Tool.Native Effect4.Tool.ToolDerived
Effect4.Laws.Store.ShapeRead Effect4.Laws.Tool.CodecProfile Test.Program.WireControls
Test.Program.QueryControls Test.Program.ToolMethodsControls Test.Program.JsonFormControls
Test.Codegen.MirrorReaders
```

A2's nine are the first nine.

The axiom gate holds `Effect4.*` and `Test.*`, and the OCaml5 library is outside it. C6 deleted
three declarations of `OCaml5.Eff.Emit` (`jsonOf`, a `partial def`, `jsonBind`, `jsonModule`) and
edited docstrings there and in `OCaml5.Tools.EffGen`. For the record, `#axiom_audit
OCaml5.Eff.Emit OCaml5.Tools.EffGen` reports 44 of 122 declarations reaching `Classical.choice`.

## What moved on the wire

The owner ruled the wire greenfield until release. Each move below is regenerated in this branch.

The session wire (`Tool.Wire`, on both drivers):
- A request that does not read refuses with its place and reason:
  `{"_tag":"codec","why":{"_tag":"unreadable","why":{"site":…,"reason":…}}}`. At the base it
  answered `{"_tag":"codec","why":"unreadable"}`.
- `CodecProfile.Refusal`'s other two cases print as objects, `{"_tag":"unprintable"}` and
  `{"_tag":"unsupportedProfile"}`, since the type is no longer all nullary.
- Four types join the wire. `JsonStep` is `key{name}` or `index{n}`. `JsonSite` is `value{path}`,
  `missing{parent,field}` or `schema{path}`. `Located` is `{site, reason}`.
- `JsonReason` is `expected{shape}`, `unknownField{name}`, `duplicateField{name}`,
  `unknownCase{name}`, `naturalOutsideProfile{limit}`, `carrierValue`, `unsupportedProfile` or
  `budget`.

The native shell (`eff tool`):
- A line that parses but does not read answers Lean's located refusal, as Lean's driver does.
- A natural above 2^53 − 1 refuses at its path (`naturalOutsideProfile`). At the base it refused
  as a bare `codec unreadable`, or at the text parser past the int range.
- A line that does not parse answers yojson's message, where the deleted parser wrote
  `JSON at byte N: …`.

The MCP server (`eff mcp`):
- A codec refusal answers JSON-RPC -32602, and its `data` holds the wire refusal with the located
  refusal. Its path is relative to the tool's arguments, with `payload.<field>` removed.
- Other wire refusals still answer -32603.
- Arguments the tree refuses (NaN, a tuple, a variant, text that is not UTF-8) still answer -32602
  with `{"refused": <why>}`. The reason is now in yojson's words or the tree's.
- Probe 1's four refusals name `a.items[0][1]` (missing field `q`), `sketch.program`
  (`unknownCase succed`), `q.tape[0].value` (missing field `n`) and `at_[0]`
  (`naturalOutsideProfile`).

The kit's commands (`eff check`, `run`, `explore`, `serve`):
- Program, row and tape JSON read through Lean's located reader, lowered to OCaml.
- A natural above 2^53 − 1 refuses where the JSON reads. `serve.transcript`'s literal request now
  answers `the program's JSON does not read as a program`.
- At the base that request answered a run stopped by the machine's literal profile (DI-56).
- Three parse messages are yojson's, rewritten in `serve.transcript`.

The JSON text, on the native side (tested, `test_kit.ml` T2):
- yojson takes comments, an unquoted key and a control byte inside a string, which the deleted
  parser refused.
- `-0` and `1e0` are numerals, which Lean's reader refuses; the deleted parser read `-0` as 0 and
  refused `1e0` at the text.
- A leading zero (`007`) refuses at the text, where the deleted parser read 7.
- A key written twice reaches the reader, which refuses it at its object (`duplicateField`).

The OCaml `eff` library prints no JSON in `V`'s spelling now. `OCaml5.Eff.Goldens` and
`ts/eff/json.gen.ts` keep that spelling.

## Lines removed

`wc -l` at the head, and `git show b83188cb2:<path> | wc -l` at the base:

| File | Base | Head |
| --- | --- | --- |
| `ocaml/engine/kit/kit_json.ml` | 539 | deleted |
| `ocaml/eff/eff_json_text.ml` | 75 | deleted |
| `ocaml/eff/eff_json.ml` (generated) | 373 | deleted |
| `Test/fixtures/session/requests.jsonl` | 10 | deleted |
| `src/OCaml5/Eff/Emit.lean` | 615 | 574 |
| `src/Effect4/Store/Domain/ShapeRead.lean` | 312 | 276 |
| `src/Effect4/Data/NatJson.lean` | 0 | 219 |
| `src/Effect4/Store/Domain/ShapeJson.lean` | 0 | 402 |
| `src/Effect4/Tool/CodecProfile.lean` | 95 | 112 |
| `src/Effect4/Tool/Native.lean` | 86 | 110 |
| `src/Effect4/Laws/Store/ShapeRead.lean` | 281 | 1,372 |
| `src/Effect4/Laws/Tool/CodecProfile.lean` | 39 | 121 |
| `Test/Program/WireControls.lean` | 86 | 228 |
| `ocaml/engine/kit/kit.ml` | 390 | 462 |
| `ocaml/engine/kit/kit.mli` | 245 | 282 |
| `ocaml/engine/kit/kit_mcp.ml` | 385 | 402 |
| `ocaml/engine/kit/kit_tool.ml` | 53 | 55 |
| `ocaml/gen/api_gen.ml` (generated) | 67,102 | 69,244 |

`git diff --numstat b83188cb2..8c0a71dd8`, by kind:

| Kind | Added | Removed |
| --- | --- | --- |
| hand OCaml (`.ml`, `.mli`) | 612 | 984 |
| hand Lean | 2,085 | 185 |
| generated (`ocaml/gen/`, `ToolDerived.lean`, `eff_json.ml`) | 2,799 | 533 |
| other | 39 | 48 |

`measure.py`, at the base and at the head:

| Measure | Base | Head |
| --- | --- | --- |
| hand OCaml lines | 57,146 | 56,709 |
| generated OCaml lines | 127,520 | 129,432 |
| hand lines that twin Lean | 1,629 | 1,017 |
| hand library modules with no `.mli` | 20 | 18 |

Two notes on `measure.py`. Its marker test counts `test_kit.ml` as generated, since the file's
header names `GENERATED`. Its section 6 stops at the head, because it reads the deleted copy.

## New public roots

Six roots join the `public` class of the `api_gen` recipe (`ocaml/gen/roots.json`):

| Lean root | OCaml value |
| --- | --- |
| `Effect4.Tool.Native.serveTree` | `Api_gen.tool_native_serve_tree` |
| `Effect4.Tool.Native.refusalTree` | `Api_gen.tool_native_refusal_tree` |
| `Effect4.Tool.Native.relativeRefusal` | `Api_gen.tool_native_relative_refusal` |
| `Effect4.Store.ShapeDoc.readLocated` | `Api_gen.store_shape_doc_read_located` |
| `Effect4.Store.ShapeDoc.printTree` | `Api_gen.store_shape_doc_print_tree` |
| `Effect4.NatJson.render` | `Api_gen.nat_json_render` |

The facade gains `Effect4.NatJson` and `Effect4.Store.ShapeDoc`, and three values in
`Effect4.Tool.Native`. The types `nat_json`, `json_step`, `json_site`, `json_reason` and `located`
reach the closure through them. `make gen-lcnf` refuses a moved or dropped public path, and it
passed.

## Evidence

- **proved**: the theorems of the next section. The kernel accepted each, and the audits hold each
  within `[propext, Quot.sound]`.
- **tested**: `Test/Program/WireControls.lean`. A duplicate key, an extra field, a misspelt case and
  a natural above `natLimit` refuse, each at its place. `Option Unit` refuses as unsupported.
- **tested**: the same battery's green controls. Objects in any order and both list spellings
  read, and an array's refusal keeps the element's index.
- **tested**: probe 1's four places, by `argumentsRefusal` guards in the battery and through
  `eff mcp` (`probe_sites.py`).
- **tested**, host-only: `make check-ocaml` at C6, H7 and the head, and the kit's tests (T2 to T11,
  N1 to N5, the transcript, `test_mcp`).
- **tested**, host-only: `prop_wire`, `test_eff` and `test_lean_wire` on the eff corpus and its
  generated programs.
- **tested**, host-only: `scripts/check-mcp-protocol.py` against the upstream 2025-06-18 schemas.
- **tested**, finite: a one-off harness, not committed, compared the deleted twins with Lean's
  code, lowered to OCaml. The 408 corpus programs print byte for byte alike and read Lean's JSON
  alike.
- **tested**, finite: in the same harness, 587 of 597 request trees read alike (128 of them read).
  These trees are the fixtures and their one-edit variants. The other 10 each hold a natural above
  2^53 − 1.
- **tested**, finite: the two drivers on seven request lines, in the table below.
- **tested**: how the codec refusals print (`<scratch>/WireForms.lean`, four `#eval`s).
- **reproduced**: Lean's session driver rewrites both reply fixtures byte for byte at the head.
  `write.lean` rewrites `verdicts.txt` unchanged.
- **reading**: the deleted parser's behaviours (`kit_json.ml`'s K4), and the base's printing of an
  all-nullary sum as a string (`printIn`).
- **assumed**: yojson 2.2.2's lexer, the text boundary of the native side. The OCaml route's
  trust is decisions row 391's.

The two drivers on one request, its number or text varied (tested, finite):

| The request holds | Lean's driver | `eff tool` |
| --- | --- | --- |
| `1.0` | refused by the binary64 bridge, with a string | refused at `payload.q.id.n`, `expected nat` |
| `-0` | reads, as 0 | refused at `payload.q.id.n`, `expected nat` |
| `1e0` | reads, as 1 | refused at `payload.q.id.n`, `expected nat` |
| a comment | refused by the text parser | reads |
| an unquoted key | refused by the text parser | reads |
| the key `form` twice | reads: Lean's parser keeps one entry | refused at `payload.q`, `duplicateField form` |
| neither | reads | reads |

## Landed theorems and their placement

`CodecProfile.profileLocated_exact` (`src/Effect4/Laws/Tool/CodecProfile.lean`), with its steps
`readAt_exact` and its mutual steps, `ShapeDoc.readLocated_exact_of`, `ShapeDoc.readLocated_exact`
and `Canonical.readLocated_exact` (`src/Effect4/Laws/Store/ShapeRead.lean`):
- Concept: `exact-codecs`; property: whatever the reader reads is the value whose canonical print
  is its input, modulo the named normaliser `ShapeDoc.order`.
- Question: the proposed registry claim `json-read-located` (P1, role compatibility), pointer
  `profileLocated_exact`. Consumers: `Tool.Wire`, `Tool.Native.serveTree` and the MCP server.
- Reach: every `Canonical` carrier, shape document, profile tree and budget. The binary64 side is
  covered for every tree that agrees with the profile tree (`Agrees`).
- Does not establish: the round trip of a value that fits a shape, which needs the write guard.
  Nothing of JSON text or of either text parser.
- Unlocks: R8, a face's observation inside its profile; the files tag R12 and R14 (O4).

`CodecProfile.profileLocated_site`, with `readAt_site` and its mutual steps,
`ShapeDoc.readLocated_site`, `Canonical.readLocated_site` and the relation `JsonSite.Valid`:
- Concept: `exact-codecs`; property: every refusal names a place of its input. This is Codex's
  `readLocated_site`, amended so that a missing field names its present parent.
- Question: the proposed registry claim `json-refusal-placed` (P2), or a step of `json-read-located`.
  Consumer: the MCP server's -32602 `data`, which an agent repairs by.
- Reach: every profile tree, shape document and budget. The place is a value of the input, an
  object of the input that lacks the field, the input's root, or the shape's root.
- Does not establish: that the reason is the input's only fault, or that the place is the deepest.
- Unlocks: R14, "a total checker marks every refusal", for JSON input.

`CodecProfile.profileLocated_erases` and `ShapeDoc.readLocated_erases`:
- Concept: `exact-codecs`; property: the old `Option` readers are the located reader's
  projections.
- Question: steps of `json-read-located`. Consumers: `write_readLocated`, and the callers of
  `ShapeDoc.readAny`, `Canonical.ofJsonAnyOrder` and `CodecProfile.read` until they move.
- Reach: every tree. The proofs hold by definition.
- Does not establish: anything beyond the definitions.
- Unlocks: the deletion of the `Option` readers once their callers move.

`CodecProfile.write_readLocated`, and `CodecProfile.write_read` proved again:
- Concept: `exact-codecs`; property: a guarded write reads back as its carrier.
- Question: `write_read` is the pointer of the registry claim `codec-profile-retains-value` (role
  compatibility). `write_readLocated` is a step of `json-read-located`, transported through
  `read`.
- Reach: every `Canonical` carrier and each successful guarded write. Consumers: the Tool driver's
  write and the native shell's reply.
- Does not establish: total writing, or textual identity.
- Unlocks: R8.

`CodecProfile.read_toBinary64`, with `ofBinary64_toBinary64` and its list and entry steps,
`natOfBinary64_binary64OfNat`, `highestBit_go`, `highestBit_eq` and the predicate `NatJson.within`:
- Concept: `exact-codecs`; property: within the profile, the profile tree and its binary64 image
  read alike. This is the deleted `kit_json.ml`'s comment K1, now a theorem.
- Question: the proposed registry claim `json-trees-agree` (P3), or a step of `json-read-located`.
  Consumers: the two drivers' agreement (N1, N4), and `Data/JsonNumber.lean`'s owed retraction.
- Reach: every tree whose naturals are at most `NatJson.limit` and that holds no numeral.
- Does not establish: anything of text (O2). The naturals from 2^53 up with at most 53 significant
  bits stay owed.
- Unlocks: R8, two drivers of one profile.

`Canonical.ofJsonAnyOrder_exact` (`src/Effect4/Laws/Store/ShapeRead.lean`), proved again through
the located reader:
- Concept: `exact-codecs`; property: exactness modulo `ShapeDoc.order`.
- Question: a step of the registry claim `json-read-exact` (pointer `Canonical.ofJson_exact`).
  Consumer: the session tool's JSON profile.
- Reach: every binary64 tree and every budget.
- Does not establish: the round trip.
- Unlocks: R14, the file's tag.

The helpers are steps of the claims above, and each docstring names its claim and its consumer:
- the relation `Agrees`, its two constructions and `Agrees.nodes_eq`;
- the `Except` steps (`except_bind_ok`, `except_map_ok`, `except_bind_error`, `except_map_error`);
- `NatJson.at?_append`, `NatJson.at?_index` and `NatJson.at?_key`;
- `closeObject_site`, `listParts?_eq`, `printIn_nil` and `printIn_cons`.

## Open obligations

- **O1, the faces contract.** `Test/contracts/faces.contract.md` names `ocaml/eff/eff_json.ml` as
  one of face 7's three implementations. Its §5 bullet "JSON" requires that file's bytes.
  - C6 deleted the file, as the brief asked, and `test_metadata.ml` dropped the matching check.
  - Face 9 also lists "JSON implementations" under `ocaml/eff`.
  - The packet is frozen, so its amendment is the owner's (P4).
- **O2, the JSON text.** The two session drivers read text by two parsers, and the table above
  shows where they differ.
  - The theorem `read_toBinary64` covers trees only.
  - Lean's `Json.parse` keeps one entry of a key written twice, so the Lean driver never sees the
    duplicate that the reader refuses.
  - Option (a): both parsers stay, each documented.
  - Option (b): one Lean parser from bytes to `NatJson`, lowered to OCaml, serves both drivers.
  - Option (c): a strict OCaml validator, which is a hand twin that the rule refuses.
  - Recommendation: (b) in a later wave, and (a) until then.
- **O3, the reason `budget`.** The dictionary says a spent budget is a frontier, never a refusal
  (§3.6 "budget", §3.2 "refusal"). The located reader names it as a refusal reason.
  - The base's `Option` reader answered `none` at the same bound, with no reason.
  - The bound is `8 × nodes + 64`. A document whose names loop through `option` without a node can
    reach it, and `supports` refuses such a loop (reading, no theorem).
  - Option (a): the reason stays.
  - Option (b): a theorem shows the budget enough for every supported document, and the reason
    goes.
  - Option (c): the reader answers three ways, with the budget as a frontier.
  - Recommendation: (b).
- **O4, the requirement tags.** `src/Effect4/Laws/Tool/CodecProfile.lean` tags R12, after the
  registry claim `codec-profile-retains-value` ("seams S3b, R12"). The system map's R12 is about
  frontiers. The JSON profile serves R8, and the located refusal R14 (P5).
- **O5, references this seat could not edit.** Each names a deleted file:
  - `src/Effect4/Run/Kit.lean`'s docstring (`Kit_json`);
  - `ocaml/README.md`'s rows for `engine/kit/` and `eff/`;
  - `ocaml/.ocamlformat-ignore` (`eff/eff_json.ml`);
  - `tools/Drivers/TsGen.lean`, `ts/eff/json.gen.ts` and `ts/eff/README.md`, which name
    `ocaml/eff/eff_json.ml` as a peer writer;
  - `src/Effect4/Data/JsonNumber.lean`, which calls the retraction owed; it is now proved below
    2^53.
- **O6, `measure.py`.** Section 6 reads the deleted copy and stops. The script is the coordinator's,
  untracked in this worktree.
- **O7, the kit's command errors.** `eff check`, `run` and `explore` answer "the program's JSON does
  not read as a program", with no place. `Kit.Json.read` has the located refusal, and a follow-up
  can answer it.
- **O8, F5b's place.** The brief expected `q`. The reader names `q.tape[0].value` (missing field
  `n`), a place inside `q`.
- **O9, two dictionary words.** "fixture" means test data under `Test/fixtures/`, and the session
  fixture now lives beside its tests. "site" means a place of a program, and `JsonSite` names a
  place of a JSON input (P6).
- **O10, the warning policy.** The kit repeats the engine's flags, without the engine's `-w @55`.
  One `env` stanza in `ocaml/dune`, not this seat's file, could hold the policy once.
- **O11, the two drivers.** Their answers agree on the fixtures (N1, N4, tested). No theorem
  relates `serveTree`'s answer to Lean's JSON driver beyond `read_toBinary64` on trees.
- **O12, the old reader.** The deleted two-pass reader and the located reader accept the same trees
  only on the harness's 597 trees. The old reader is gone, so no theorem will compare them.

Bounded or host-only evidence: the harness, the driver table, the four probe calls, the MCP check
(a finite stdio trace) and every `dune` test.

## Proposed decisions rows (proposals only)

- **P1.** Register the claim `json-read-located`: concept `exact-codecs`, role compatibility, R8.
  Its pointer is `CodecProfile.profileLocated_exact`, with the steps of the first placement above.
- **P2.** Register the claim `json-refusal-placed`: concept `exact-codecs`, role compatibility, R14.
  Its pointer is `CodecProfile.profileLocated_site`.
- **P3.** Register the claim `json-trees-agree`: concept `exact-codecs`, role compatibility, R8.
  Its pointer is `CodecProfile.read_toBinary64`.
- **P4.** Amend `Test/contracts/faces.contract.md` (O1): face 7 keeps two implementations. The OCaml
  estate's JSON is `ShapeDoc.printTree` and `ShapeDoc.readLocated`, lowered to OCaml.
- **P5.** Retag `codec-profile-retains-value` and the profile's laws from R12 to R8 (O4).
- **P6.** Rule O2's text boundary and O3's `budget` reason. Amend "fixture" and "site" in the
  dictionary (O9).
