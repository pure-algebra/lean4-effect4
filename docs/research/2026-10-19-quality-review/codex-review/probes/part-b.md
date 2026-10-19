## Part B: the remaining second owners

These six findings are ranked by the work they remove or unblock within each severity.
Counts describe current source or a checked scratch result. They are not estimates of net patch size.

### B5.1 — Stop exporting unreachable lane types

| Field | Finding |
| --- | --- |
| Severity | medium |
| Kind | consolidation |
| Where | `ocaml/gen/interface/main.ml`, its reachable selector; the lanes recipe and `ocaml/engine/test/lanes/lanes_gen.mli`. |
| Evidence | `python3 probes/b5_interfaces.py` changes the inferred interface from 2,618 lines to 164. All eleven inference and compilation steps pass. |
| Why | The public signature repeats implementation types that no exported lane entry needs. Those names make the next generated change harder to inspect. |
| Fix | Select reachable types when inferring the lanes interface. Keep the implementation and the private closure owner. Apply the same reachability test to other signatures individually. |
| Deletes | 2,454 generated signature lines. The scratch implementation is byte-for-byte the pinned implementation. |
| Test | Compile the smaller signature, unchanged implementation, and all four current facades: todo, ctors, modeled and rocq. `probes/b5/compile.json` retains commands and results. |
| Plan | C5 follow-up; before F1. |
| Size | S |

This is an OCaml compilation check, not a fresh run of every behavior gate.
The 69,991-line closure has 3,267 top-level definitions.
The lanes implementation has 213 definitions; none repeats a closure definition.
The five-line facades already avoid repeating implementation bodies.
Those measurements do not justify deleting another compiled closure or exposing private packages through a blanket include.

### B1.1 — Generate the authoring and host faces from their owners

| Field | Finding |
| --- | --- |
| Severity | medium |
| Kind | consolidation |
| Where | `ocaml/engine/kit/kit_author.ml`, its interface, and `ocaml/engine/test/todo/native_todo.ml`, `REPO` and `host`. |
| Evidence | The pinned `measure.py` reports 113 authoring implementation lines, 162 interface lines, and 13 host-signature/adapter lines. `probes/measure.log` retains the run. |
| Why | A change to Lean authoring or the typed host asks for another hand declaration. Lean owns these carriers and operations. |
| Fix | F1 generates wrappers and their signatures from `Effect4.Program.Authoring` and the lowered `Typed.Host`. Preserve native implementations and exception policy. |
| Deletes | 288 hand lines become generated lines. This does not promise a smaller generated artifact. |
| Test | Compile an outside consumer against the generated face. Retain the missing-host-method rejection and existing native-to-Lean comparisons. |
| Plan | F1, after the numeric and JSON choices. |
| Size | M |

Every group in the brief's 567-line measurement has a disposition:

| Group | Lines | Lean owner | Disposition |
| --- | ---: | --- | --- |
| `kit_json.ml` | 0 | `Store.ShapeDoc` and `Tool.CodecProfile` | Already deleted. Do not recreate it. |
| `eff_json_text.ml` | 0 | `NatJson.render` | Already deleted. |
| `kit_author.ml` and `.mli` | 275 | `Program.Authoring` | Generate through F1. |
| `native_todo.ml`, measured block | 13 | `Test/Dogfood/Scenario/Todo/Typed.lean`, `Typed.Host` | Generate `REPO` and the record adapter. Keep the hand host implementations. |
| `kit_serve.ml` | 204 | `Tool.Queries`, with `Run.Kit` supplying run observations | A6 moves semantic dispatch into queries. Keep parsing, framing and input/output. Not all 204 lines are deletable. |
| `test/reference/e4_memo_list.ml` | 75 | `MemoWorld` operations in `Machine/Stores.lean` | Keep as the remaining independent list reference until a replacement detects the same memo defects. |
| Total | 567 | — | No second runtime or new program representation is required. |

The measurement script detects `GENERATED` within the first 2,000 bytes.
Its hand total is 56,112 lines, unlike the brief's anywhere-in-file classification.
Those totals use different methods; their difference is not growth measured by this review.

### B4.1 — Settle the public JSON spelling before generating more faces

| Field | Finding |
| --- | --- |
| Severity | medium |
| Kind | consolidation |
| Where | `src/OCaml5/Eff/Goldens.lean`, `effV` and `V.json`; `ts/eff/json.gen.ts`; `Store.Canonical.print`. |
| Evidence | `probes/B4Json.lean` prints the same program both ways. `probes/b4-json.log` retains the two different strings. |
| Why | Face 7's arrays and the tool's tagged objects have no connecting theorem. A generated public API must name which contract it accepts. |
| Fix | Make the canonical tagged spelling the public interchange contract. Migrate the TypeScript face in its own slice. Keep V as an internal fixture format during migration. |
| Deletes | Zero justified immediately. The shared corpus and existing TypeScript consumer prevent deleting V now. |
| Test | Feed the same corpus through both readers during migration. Compare the recovered canonical program bytes, including refused cases and numeral boundaries. |
| Plan | Owner choice before F1; decisions row 416 does not make the two spellings identical. |
| Size | M |

The checked example is `succeed (lit (nat 1))`:

```json
["succeed",["lit",["nat",1]]]
```

```json
{"_tag":"succeed","value":{"_tag":"lit","value":{"_tag":"nat","value":1}}}
```

If both public spellings must remain, give each a version and a named consumer.
Then place their equal-program observation before proving a connector.
No lowering proof is requested; decision 391 remains in force.

### B3.1 — Share the two `Except` facts

| Field | Finding |
| --- | --- |
| Severity | low |
| Kind | consolidation |
| Where | `except_bind_ok` in `Store/Domain/Word.lean`, `Store/Domain/JsonText.lean`, and `Laws/Store/ShapeRead.lean`; the latter two also define `except_map_ok`. |
| Evidence | `probes/consolidation_counts.py` counts three five-line bind declarations and two seven-line map declarations. Their statements express the same two facts. |
| Why | Five owners repeat two elementary steps used by codec readers and termination arguments. |
| Fix | Put the two facts in a core data module. Migrate the five uses of the declarations without changing the codec claims. |
| Deletes | Seventeen duplicate declaration lines, before import and alias changes. Keep one five-line bind fact and one seven-line map fact. |
| Test | Narrow-build the three consumers and audit their changed modules. Their existing reader controls remain the behavioral tests. |
| Plan | J3. |
| Size | S |

### B3.2 — Share the finite table measure

| Field | Finding |
| --- | --- |
| Severity | low |
| Kind | consolidation |
| Where | `Store/Domain/ShapeRead.lean`, `unseenDefs`; `Program/TyExpand.lean`, `TyDecls.unseen`. |
| Evidence | Both definitions filter a named table by unseen keys and take its length. Each main decrease proof occupies 23 lines. |
| Why | Shape unfolding and type unfolding prove the same finite-key decrease separately. |
| Fix | Generalize the keyed-list measure over its payload. Retain each domain's alias and lookup-specific corollary. |
| Deletes | One two-line definition and one 23-line duplicated proof are replacement targets. Alias changes determine the final net count. |
| Test | Build both consumers and the located JSON reader. Keep repeated-name and recursive-name refusal controls. |
| Plan | J4, beside J3. |
| Size | S |

### B2.1 — Use the framing module's tag constants

| Field | Finding |
| --- | --- |
| Severity | low |
| Kind | consolidation |
| Where | `ocaml/engine/cas/e4_shape.ml`, its six `tag_*` bindings; `ocaml/eff/eff_frame.ml`. |
| Evidence | `E4_shape` repeats byte values for bytes, list, pair, some, constructor and reference. `Eff_frame` already exports all six. |
| Why | A frame tag has two OCaml owners despite one wire grammar. |
| Fix | Use the exported constants. Keep shape-specific tags and format versions with their own formats. |
| Deletes | Six literal definitions become references or disappear. No byte-layout change is needed. |
| Test | Existing frame and store-byte controls keep their bytes. The full decoder corpus remains unchanged. |
| Plan | B2 and A6 constant ownership. |
| Size | XS |

The other B2 leads do not justify indiscriminate consolidation:

| Lead | Checked disposition |
| --- | --- |
| UTF-8 | `Eff_frame.utf8_valid` already delegates to `String.is_valid_utf_8`. The finite check covers 1,277,857 strings with zero mismatches. |
| Hex and big-endian bytes | `E4_hex` owns hex conversion. `E4_be` already uses the framing kernel. Keep those host-byte adapters. |
| MCP JSON helpers | `Kit_mcp.raw` preserves number text for JSON-RPC IDs. Its inverse serves tool arguments. They are transport conversions, not another carrier reader. |
| Schema JSON parsing | Yojson reads internally generated schema text. Deleting it is not the same change as J5's external request reader. |
| Test helpers | C4/H5 already introduce `E4_check`. Retain process and native-resource fixture helpers where the shared checker does not replace them. |
| Warning strings | Generated join points need their warning contract. The kit's old broad suppression is gone. Share defaults while retaining documented generated-code exceptions. |

The H11–H14 counts are cleanup leads, not runtime failures.
`probes/lean-hygiene.json` records the census and every contributing file.
It finds 168 `]!` tokens, eleven `head!` tokens, and five `get!` tokens.
Outside `Laws`, these are in compiler, generator or elaborator modules.
They do not establish a reachable machine panic.
The same census finds 43 files above 1,500 lines, 45 without a module docstring, and thirteen named linter suppressions.
Split a file at a real ownership boundary when its consumer changes.
A size threshold alone does not establish a defect.
