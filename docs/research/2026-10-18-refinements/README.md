# Overnight refinements, 2026-10-18: the morning report

The one thing to know first: the review's top findings are fixed and landed. The native tool is
sealed, both drivers share one wire core and one number domain, the OCaml gate is about three
times faster, and `eff mcp` now serves the authoring tool from a table generated in Lean.

Base `1b9c351b7^` (the review, `1b7869eea`), head `338fab800`, branch `refactor/phase1-phase3`.
Nothing is pushed. The review this answers is
[review-2026-10-18.md](../2026-10-17-seams/review-2026-10-18.md).

## The request path now

```mermaid
flowchart LR
  A["agent (MCP)"] --> M["Kit_mcp: tools/list from Tool.Methods"]
  J["JSON lines"] --> K["Kit_tool"]
  M --> K
  L["Lean driver"] --> SJ["Wire.serveJson"]
  K --> N["Tool.Native.serve (sealed Session)"]
  N --> C["Wire.serveEnvelope: check, serve once, frame"]
  SJ --> C
  C --> S["Tool.serve"]
  P["CodecProfile.carries: naturals up to 2^53 - 1"] -.- N
  P -.- SJ
```

Everything left of `Kit_tool` and `Wire.serveJson` is text and IO. Everything from
`Wire.serveEnvelope` on is Lean, generated into OCaml for the native side.

## What landed

| Commit | What changed, in plain words | Evidence |
| --- | --- | --- |
| `1b9c351b7` | The OCaml gate's cache key reads its Lean modules from `roots.json`. The hand list had missed all 30 tool and store files, so the gate could pass on stale OCaml. | Red/green: an edit to `Tool/Actions.lean` was outside the old key and is inside the new one; gate-cache tests 17/17 |
| `5a3875b16` | Dropped 9.5 MB of tracked research cruft: 822 evidence logs, the ended pause archive, compiled OCaml objects. | No tracked file outside `docs/research` cited them; they remain at `1b9c351b7` |
| `f7677fb54` | The native store reads only its current control-file version; the version-1 decoder for stores that never existed is gone. Two stale notes corrected. | Native store tests pass |
| `fc4ed752d` | One wire core (`Wire.serveEnvelope`) for both drivers. The native tool's state and memo are one abstract `Session`: native code can no longer forge either. 7 native entry points instead of 12. One owner for suggestions (`Suggest.page`); the duplicate `Candidate` type, the unused `CheckCache.suggest` and the dead `response` refusal are gone. A zero page limit no longer loops a client. | 1,869-job build green; audit 4,211 declarations within `[propext, Quot.sound]`; ten hostile sealing clients refused; native replies equal Lean's (10/10) |
| `81f342733` | Stale docs and law docstrings corrected: the missing `src/Effect4/Tool` architecture row, the generated-file tables, three laws that named consumers that do not exist. | Docstring edits; laws built |
| `f5883b8ae` | A store commit now costs its own transaction, not the whole store. A read costs its own node. | `bench_commit`: before 0.95 → 3.96 ms per commit over 400 commits (growing); after 0.27 → 0.25 ms over 1,500 (flat) |
| `43e7cb7d5` | Both drivers carry naturals up to 2^53 − 1 and refuse the same values, keeping the same state (decision A). Replies stop leaking machine internals: previews drop the machine's store set, and waits drop the compiler's continuation names. The run record's second, hand-written codec is gone. | Audit 3,235 within ceiling; Tool codec file 10,908 → 8,335 lines; a new cross-driver fixture N4 (6/6); `write_read` re-proved |
| `26fa723e4` | The OCaml generator runs compiled (`lake exe lcnfgen`) instead of interpreted. This was the 412 s. | `api_gen` step 231 s → 10.6 s, output byte-identical; a cold `check-ocaml` reached its last step in 3 min 3 s (was 8 min 20 s) |
| `338fab800` | `eff mcp` serves the authoring tool to agents. Its 19 tools and their JSON Schemas are generated from Lean's request shape (`Tool.Methods`); the only hand input is each method's description, checked against the method list. The kit's hand-written MCP server is gone (decision B, its MCP half). | Every fixture request validates against its schema (JSON Schema 2020-12), except the two ids both drivers refuse; MCP tests C1–C3 pass; transcript 40/40 |
| `277c9c95d` | A refused session load names its fault: the chain reaching its origin early, or an action out of order, with both indices. It no longer shares one `parent` refusal. | Exchange laws audited; a new red control |
| `06d9ecf89` | Shape names that enter stored digests are data names (`Effect4.Program.Focus(Effect4.Program.NativeOp)`), not the generator's Lean source spelling (`_root_.`, `@`). | Audit 2,300 within ceiling; no golden changed; `check-ocaml` 2 min 17 s cold |
| `96d53d693` | The fifteen `Seams*` batteries and three `test_seams_*` native tests are named after their subjects. | Renamed batteries built; native tests pass |

## Measured, before and after

| What | Before | After | Command |
| --- | --- | --- | --- |
| `api_gen` closure | 231.3 s | 10.6 s alone, 5.5 s in the gate | `lake exe lcnfgen --stage DIR --recipe ocaml/gen/roots.json --one 1` |
| Cold `make check-ocaml` | 8 min 20 s (412 s at S6) | 3 min 3 s to the last step | `make check-ocaml` |
| Store commit, late in a session | 3.96 ms, growing | 0.25 ms, flat | `dune exec engine/cas/test/bench_commit.exe -- 1500` |
| Tool codec file | 10,908 lines | 8,335 lines | `wc -l src/Effect4/Tool/ToolDerived.lean` |
| Native tool entry points | 12, state forgeable | 7, sealed | `ocaml/gen/api_gen.mli` |
| Native edit, as the memo grows | — | 0.29 ms first 100, 0.46 ms last 100 of 1,000 | `ocaml/_build/default/engine/test/kit/bench_tool.exe 1000` |

## The review's plan, slice by slice

| Review slice | Status |
| --- | --- |
| 1. Gate key from the recipe | Done (`1b9c351b7`) |
| 2. Seal the tool natively | Done (`fc4ed752d`) |
| 3. One wire adapter | Done (`fc4ed752d`) |
| 4. Narrow leaked carriers | Done for previews and waits (`43e7cb7d5`). It did not speed the generator: compiling the generator did. |
| 5. One JSON number domain | Done (`43e7cb7d5`). One owner of the JSON *text* (Lean versus `kit_json.ml`) stays open: lowering it waits on exact 64-bit numbers. |
| 6. Precise, located refusals | Partly: the native unreadable line now prints Lean's refusal. Path-located decode refusals are not done. |
| 7. Memo as a keyed map | Measured and not needed now: a native session's edit costs 0.29 ms at first and 0.46 ms after 1,000 accepted edits (`bench_tool.exe 1000`), growth that the transcript's and history's list appends share with the memo's scan. |
| 8. `combine_deps` | Done: proved in place (merge `48a0f8bbc`), so `Checked.ask_value` rests on no goal. Merged head: `lake build` of the four law modules, `Effect4.Laws` and four batteries, 1,819 jobs green; `#axiom_audit` over the four modules, 726 declarations within `[propext, Quot.sound]`, 15 of them modulo planned goals, 4 planned goals |
| 9. Restore S1's proofs | Partly done. Proved: `feed_keeps`, `feed_root`, `feed_draft`, `kept_eq_certified`, `FillSet.add_wf` and `publish_eq_materialize`. `feed_draft` is restated with two premises: no ill-formed reference in the sketch or the candidate. `feed_coherent` and `feed_keepExact` are **false at head**, refuted by kernel-checked counterexamples. Fifteen document laws rest on those two goals |
| 10. Exchange residency, then S6b | Not done. A session cache has no consumer until the native exchange exists. The native store's commit cost, its prerequisite, is fixed. |
| 11. Suggestion owner and method table | Done (`fc4ed752d`); `method_supported` guards the method list |
| 12. Cruft sweep | Mostly done: evidence logs, the legacy decoder, dead refusals, the tuple codec, stale docs |

The decisions:
- **A (numbers):** taken, binary64-safe naturals in both drivers.
- **B (the kit's face):** taken for MCP. The kit's `check`/`run`/`explore` remain CLI and JSON-lines commands.
- **C (the result envelope):** taken; it is prepared, not extended, and its laws say so.
- **D (store laws):** not taken. It runs against the 2026-10-16 steer that hard proofs live in Rocq, so it is yours.

## Codex's core abstractions, folded in (`76a71a03e`)

Codex answered the six questions of the [brief](../2026-10-18-codex-abstractions/brief.md) in its
[report](../2026-10-18-codex-abstractions/README.md), and four of its slices are merged:

| Commit | What changed, in plain words |
| --- | --- |
| `bb95dbacb` | `eff mcp` follows its declared MCP protocol (stdio, 2025-06-18): 52 native controls, and 61 checks against the official schema (`scripts/check-mcp-protocol.py`) |
| `f4a01c5c4` | The exchange is generic over `Port`, its four store operations (entry, root, membership, commit), the S6b design's first slice. Its laws stay at the `Cas` instance |
| `4b2193074` | The S1 feed splices only where `SourceSession.canSplice` holds: no ill-formed reference on either side. This repairs bug 1. The native engine builds and seals its interpreter once (`Program.Prepared`) |
| `6c09715f0` | The report and receipts. The raw gate logs stay at that commit (`4f3d4f2f9`) |

The merge reconciles Codex's feed with the proof seat's laws:
- Five laws are stated over `canSplice`.
- `feed_keepExact` takes Codex's exact splice delta.
- Every bug-1 counterexample now evaluates false and is gone: eight refutations (`git:d048b9a1b`).

Evidence:
- **Build:** `Effect4`, `Effect4.Laws` and seven batteries, 1,873 jobs green.
- **Audit:** `#axiom_audit` over the nine touched modules gives 2,109 declarations within
  `[propext, Quot.sound]`: 15 rest on planned goals, and there are 4 planned goals.
- **Gate:** `make check-ocaml` passes in 3 min 8 s.

## Two side sessions, merged (`e2e8571b2`, `816d24bc6`)

| Merge | What changed, in plain words | Evidence |
| --- | --- | --- |
| `e2e8571b2` | The MCP tool list says each thing once. The schemas name the program grammar by `$ref`, and a generated `describe` tool answers each definition's schema from Lean's table. `tools/list` drops from 353,485 to 40,069 bytes of schema | `api_gen.ml` regenerated from the merged Lean equals the textual merge byte for byte; `scripts/check-mcp-protocol.py` gives PASS with 69 schema checks over 20 tools |
| `816d24bc6` | STANDARDS rule 7 is checked by the compiler's own types. `ocaml/tools/typed_lint` reads each hand library's `.cmt` files under `dune test` and refuses a polymorphic comparison at a type other than `int`, `char`, `bool` or `string`. Its 85 sites are fixed, the plan's manual phase 6 is gone, and `--raises` reports rule 6 | `dune test tools` (red control and fixtures) passes |

Evidence for both merges together:
- **Build:** `Effect4`, `Effect4.Laws` and the reached batteries, 1,878 jobs green.
- **Audit:** `#axiom_audit` over `Tool.Methods`, `Tool.Native` and their battery gives 234
  declarations within `[propext, Quot.sound]`.
- **Gate:** `make check-ocaml` passes (recorded `2babea115c92`, `gen-check` PASS).

## For you

- **The S1 feed is repaired and its laws are proved** (`4111bf9d6`). A kept-exact feed now splices
  only at a typed root (option A2): it keeps a typed document's exact observations, and at a
  refused root it refuses, since there is no root type to keep. A refused document is edited under
  `draft`. This closed the second bug.
  - **Proved:** `feed_coherent` and `feed_keepExact`, and with them the fifteen document laws that
    rested on them.
  - **Evidence:** `#axiom_audit` gives 872 declarations within `[propext, Quot.sound]`, none
    modulo a planned goal; `make check-ocaml` passes.
  - **The cost, taken on purpose:** a kept fill beside an unrelated error refuses, and its draft is
    accepted. `kept_eq_certified` now takes a typed root.
- **Decision D:** Codex recommends that Rocq own the hard store proofs, after aligning Rocq's
  missing result-uniqueness condition (report, question 6).
- **`AGENTS.md`:** a one-page draft that leads with the core abstractions is at
  [2026-10-18-agents-md-draft.md](../2026-10-18-agents-md-draft.md). The live file is unchanged.
- **Decision D:** who owns the store's node laws, Lean or Rocq.
- **The kit's commands:** whether `check`/`run`/`explore` fold into tool queries. That would drop
  the tree-versus-machine cross-check they run, or move it into the tool.
- **S6b, the native exchange over the disk store:** the next large slice, designed in
  [2026-10-18-native-exchange](../2026-10-18-native-exchange/README.md). The exchange is written once
  over a three-operation store port, proved at the Lean model, and generated over `E4_disk`.

## Not verified

- No full battery run (`lake build Test`) and no whole-tree axiom gate. Each landing built the
  touched modules and batteries and audited its modules.
- The generator's speed-up is measured on this machine, with other sessions idle.
- `check-ts` was not run: nothing tonight reaches the TypeScript face. The Tool carriers are not in
  `ts/eff`.
