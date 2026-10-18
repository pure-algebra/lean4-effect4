# S3b follow-on receipt: the query tool cut (plan §2.2)

The one thing to know first: `Tools.Query` and its driver are gone, and nothing it answered is
lost. Its three reads that the session tool lacked are now the tool's queries `table`,
`addresses` and `slots`; its check, focus and refusals were already the tool's `doc`; its fill and
omit answers are `dry` edits. `fillPremises`, `omitPremises` and their two soundness theorems went
with the file: the draft and `keepExact` feed policies decide the same premises inside the tool.

## Commits and source ownership

- Base: `025df9b34` on `refactor/phase1-phase3` (the generator's arm-lemma template, after the
  proof of `serve_answers`). The work started at `c95288fe3` and was rebased; every check below
  ran on the rebased tree.
- Branch: `claude/gracious-shamir-5b34bd`.

| Owner | What changed |
| --- | --- |
| `src/Effect4/Tool/Protocol.lean` | `Query.table`, `Query.addresses`, `Query.slots (at_) (slot)` and the matching `Answer` constructors, appended; `SlotView`; the three method names, at version 1 |
| `src/Effect4/Tool/Queries.lean` | `Internal.slots` (Tools.Query's `slotsAt`, read in the expansion's part as the table reads the node), `allSlots` with its completeness proof `mem_allSlots`, and the three query arms |
| `src/Effect4/Tool/Wire.lean` | `queryPairs` pairs each new read; a slots answer pairs with its own address |
| `src/Effect4/Laws/Tool/Wire.lean` | `query_pairs` gains the three new arms, so `serve_answers` stays proved |
| `tools/Effect4Gen/manifest.json`, `tools/Effect4Gen/wire-tags.json` | `ExtSlot` and `SlotView` join the Tool group; the new tags are `Query` 8, 9, 10 and `Answer` 9, 10, 11; no tag moved |
| `src/Effect4/Tool/ToolDerived.lean` (generated) | regenerated; no other group changed |
| `Test/Program/QueryControls.lean` | every control now drives `Tool.serve` |
| `tools/Tools/Query.lean`, `tools/Drivers/Query.lean` | deleted, with `fillPremises`, `omitPremises`, `fillPremises_sound`, `omitPremises_sound` |
| `tools/Tools/JsonBridge.lean` | `ofHex?` and `toHex` deleted: the query tool was their only caller |
| docstrings and docs | every consumer that named the query tool now names its successor, or says it has none (below) |

## How each control kept its meaning

| Old control | New form |
| --- | --- |
| `check` answers the checker; a refused program answers its first refusal | the `doc` view's type equals `Sketch.check`; a refused program's first refusal is `explain`'s |
| `addresses` | `Query.addresses`: the same seven addresses, in order |
| `focus` at an address; none at no address | the `doc` inspection's focus equals `Sketch.focusAt`; at no address the read refuses `noProgram` |
| `table`, entry by entry; an unreached entry | `Query.table` equals the program's table; the unreached entry has no environment and no result |
| `refusals`, and the whole refusal on the wire | the view's refusals by path and reason; the reply's refusals read back whole through the JSON profile |
| `slots`: one slot, every slot, no such slot, an open program, a block | `Query.slots`, with the same terms, environments and types; the typed flag is the premise the old answer's law name stood for |
| a block's root focus is the module check's | the root inspection's type is `checkModule`'s; a part's focus is present |
| `omit` names its law where its premises hold; the omission and its hole table are the sketch | a `dry` draft commit splices (the premises hold) and keeps the type; the omitted program opened with its hole rows checks at the original type, and without them is refused |
| `fill` names its law at the focus type; another type is a new check | a `dry` `keepExact` commit is accepted and keeps the type; another type refuses `notKept`, and under the draft policy the checker refuses the filled program |
| no omission or filling at no address | the commit's place refuses `moved` |
| bytes that do not decode; an unknown operation; the reader's field errors and unknown slot | request lines with a malformed program, hole table, operation or slot do not read; positive controls show the well-formed lines read |
| the reader reads what the writer writes; each slot name reads back | each new read crosses `Wire.decode` and prints back the same; each slot reads back from its JSON |

The controls are finite Lean evaluations.

## Departures and proposed decisions

| Correction | Evidence | Proposed decision |
| --- | --- | --- |
| Plan §2.2 named only `Query.doc` and `Query.dry` as the replacement. | The old battery's `table`, `addresses` and `slots` controls had no tool counterpart. | Three appended reads; the plan row now names them. |
| `Query.table` answers the session's source table, not `Sketch.table`. | Off layer references the two are equal; the battery compares with the program's table. | The tool's one table; at a reference it shows admission's reading, as the `doc` view does. |
| `Query.slots` refuses an address with no program. | The old tool answered an empty list there. | Refuse, as the `doc` inspection does; an address with no slot still answers an empty list. |
| `Program.SketchWire` lost its only consumer. | No source calls `Sketch.encode`, `Sketch.decode` or `Wire.encodeHoles` now; the tool carries a sketch through its generated codec. | Its docstrings and the registry's `sketch-wire` title say so; cutting the claim is a follow-up. |

## Current commands and trust evidence

The rows below are the last run of each check on the final tree, in this order. Before them, on
the same tree: the codecs were regenerated with
`python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only derived` (exit 0), which
changed only `src/Effect4/Tool/ToolDerived.lean`; and the narrow build ran once from the stale
`.lake` (exit 0, 761 s), rebuilding most of the tree for the rebased codecs and the Laws
docstrings, so the recorded narrow row is the incremental rerun.

- `batteries-touched` reaches 51 batteries against the base. The `tool-batteries` row rebuilds
  the thirteen that drive the tool or its JSON, whether or not they were reached.
- The OCaml and TypeScript groups read the wire tags and `tools/Tools/`; both regenerate
  byte-identically, and so does `generated/semantics.md` after the rebase.
- The first audit on the rebased tree refused `query_pairs` and `serve_answers`: the slots pairing
  compared paths with `==`, and `beq_self_eq_true` at `List Nat` reaches `Classical.choice`
  through an order instance. The pairing now decides `path = path'`, and the arm closes by
  `decide_eq_true rfl`.
- The first `batteries-touched` run failed at a positive control: a constructor with no fields
  prints as a bare string, so the unknown-slot line had been refused for the wrong reason. Both
  lines now spell the slot as a string.

```text
#axiom_audit: 4134 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [narrow](evidence/S3b-query/narrow.json) | 0 | 14.434 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Tool.Protocol Effect4.Tool.Queries Effect4.Tool.Wire Effect4.Tool.ToolDerived Effect4.Program.SketchWire Effect4.Laws.Program.Sketch Effect4.Laws.Program.SketchWire Effect4.Laws.Program.Typing.Splice Effect4.Laws.Program.Typing.Table Effect4.Laws.Store.ShapeRead Effect4.Laws.Tool.Serve Effect4.Laws.Tool.Wire Tools.JsonBridge Tools.WireText Tools.Catalogue Tools.LoadPaths Tools.RunChecks Tools.Semantics Tools.SemanticsDocument Tools.View.Build Tools.View.Cell Tools.View.CellSheet Tools.View.Glyph Tools.View.GlyphSheet Tools.View.Live Tools.View.LiveChecks Drivers.GlyphSheet Drivers.Live Drivers.Semantics Drivers.SemanticsControls Drivers.Session Drivers.View ProofGraph.Registry ProofGraph.AxiomAudit ProofGraph.Why Effect4 Effect4.Laws` |
| [batteries](evidence/S3b-query/batteries.json) | 0 | 192.175 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=025df9b346e901e0165a0d9b8e6c251de1030e5d` |
| [tool-batteries](evidence/S3b-query/tool-batteries.json) | 0 | 16.043 | `python3 /private/tmp/seams-lean-one.py lake build Test.Program.SessionToolControls Test.Program.SeamsS3a Test.Program.SeamsS3aInspection Test.Program.SeamsS3bWire Test.Program.SketchAdmissionControls Test.Program.LiveRecordControls Test.Program.PreviewControls Test.Program.CheckCacheControls Test.Program.FillSetControls Test.Program.SourceDocumentControls Test.Program.SourceFeedControls Test.Program.JsonFormControls Test.Schema.DocumentJson` |
| [audit](evidence/S3b-query/audit.json) | 0 | 4.805 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true docs/research/2026-10-17-seams/receipts/evidence/S3b-query/audit.lean` |
| [generate-semantics](evidence/S3b-query/generate-semantics.json) | 0 | 38.917 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
| [generate-eff](evidence/S3b-query/generate-eff.json) | 0 | 7.955 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only eff` |
| [generate-ts](evidence/S3b-query/generate-ts.json) | 0 | 13.489 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only ts` |
