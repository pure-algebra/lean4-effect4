# Seat APPCHECK receipt: the edit session at an application, through layer references

Status: receipt (history, not authority). 2026-10-13. Seat APPCHECK, from the brief
`docs/research/2026-10-13-seat-appcheck-brief.md`. Decisions rows 373 (7) and (10), 376 (1) and
(3). Obligation O2 of `docs/research/2026-10-13-authoring-obligations/README.md`.

## The one thing to know before merging

- **The session tool now holds an edit session of the sketch as written, checked through its
  layer references** (`SourceSession`, `src/Effect4/Program/Typing/SourceSession.lean`).
  - The table is the expansion's table at the source's addresses.
  - The root holds admission's check: `Sketch.sourceCheck_toOption` equates it with
    `typeOfProgram`.
  - `open` takes the application's row table and service declarations as canonical bytes.
- **The view tools still compile unchanged.** `Tools.Session.State.session` is now a definition:
  the session through references, shown as an edit session (`SourceSession.shown`). So
  `Tools.View.Build` and `Tools.View.Live` draw the program as written, with its table at the
  source's addresses.
- **The battery of step 4 is not written.** The coordinator ended the seat first. The plan is
  under "Open obligations", item 1.
- **No root was built** (`Effect4`, `Effect4.Laws`, `Test.All`), on the coordinator's word. The two
  root import lines were added at the roots' ends; the modules they name were built.

## Base, head and commits

- Base named in the brief: `cdcedb4b4`. Fast-forwarded on the coordinator's word to `0d918c680`,
  then to `d439b7767` (seat ADDRESS's merge) before the commit.
- `b4c0898ef` program: a sketch checked through its layer references; the session tool opens at
  an application.
- This receipt's commit follows it.

## Files

| File | What it holds |
| --- | --- |
| `src/Effect4/Program/Typing/Source.lean` (new) | `Sketch.expand`, `Sketch.sites`, `Sketch.sourceCheck`, `Sketch.sourceEntry`, `Sketch.sourceTable`, `Table.belowSite`, `Table.atSource`, `Sketch.sourceAnnotate`, `Sketch.sourceRefusals` |
| `src/Effect4/Program/Typing/SourceSession.lean` (new) | `Sketch.edit`, `Edit.expanded`, `Edit.Delta.atSource`, `SourceSession` with `open`, `feed`, `feedStep`, `run`, `table`, `shown`, `view`, `focusAt` |
| `src/Effect4/Laws/Program/ExpansionAddresses.lean` (new) | the expansion's address map, `Eff.addresses_expandRefs`, and its steps |
| `src/Effect4/Laws/Program/SourceTable.lean` (new) | the table law, the check at the root, the refusals, and the session's laws |
| `tools/Tools/Session.lean` | `open` takes `rows` and `services`; the state holds a `SourceSession`; answers name the new laws; `replays` and `answerLines` go; the JSON read names `Canonical.ofJsonAnyOrder_exact` |
| `src/Effect4.lean`, `src/Effect4/Laws.lean` | the four modules imported at the roots' ends |

## The laws (each proved, each placed in concept `initial-algebras-folds`, requirement R14)

| Statement | What it says |
| --- | --- |
| `Eff.addresses_expandRefs` | the expansion's addresses not strictly below a reference site are the program's addresses, in their order |
| `Eff.mem_addresses_expandRefs` | every address of a program is an address of its expansion |
| `Sketch.sourceAnnotate_eq_sourceTable` | **pointer of `source-annotation-agrees`**: one traversal of the expansion at the source's addresses is the table, whose root holds the check through the references and whose other entries are the expansion's |
| `Sketch.sourceTable_find`, `Sketch.sourceTable_typedAt` | below the root, the entry and the type at a source address are the expansion's there |
| `Sketch.sourceTable_focus` | where the table holds a type below the root, it is the expansion's focus there |
| `Sketch.sourceCheck_toOption` | the check through the references succeeds exactly as `typeOfProgram` at the application extended by the hole table |
| `Sketch.sourceRefusals_head`, `Sketch.sourceRefusals_nil_iff` | the refusals start with the check's refusal, and are empty exactly when it succeeds |
| `SourceSession.reached_view` | **pointer of `source-session-coherent`**: after an open and any edits, the view is the table at the source's addresses, its refusals and the type through the references |
| `SourceSession.feed_undo` | **pointer of `source-session-undo`**: an edit, then the edit that puts back the old sub-program as written, restores the session |
| `SourceSession.focusAt_typed` | below the root, the focus's environment and type are the expansion's focus |
| `SourceSession.open_shown_of_refSites_nil` | the connector: on a sketch with no reference, an open shows the edit session's own open |
| `EditSession.feed_omit_sketch`, `EditSession.feed_edit` | an edit session's edit holds the edited sketch (an omission had no such lemma) |

The placements of the two claims are written below, before the work, as `AGENTS.md` asks.

## Commands and results (each tested, the slot script around each)

- `lake build Effect4.Program.Typing.Source Effect4.Program.Typing.SourceSession
  Effect4.Laws.Program.ExpansionAddresses Effect4.Laws.Program.SourceTable Tools.Session
  Tools.View.Build Tools.View.Live Drivers.Session Drivers.Live Drivers.View
  Test.Program.SessionToolControls`, after the merge of `d439b7767`: "Build completed
  successfully (951 jobs)". These are the new modules and every reader of `Tools.Session`
  (`git grep`): the view tools, the three drivers and the tool's battery.
- `#axiom_audit Effect4.Program.Typing.Source Effect4.Program.Typing.SourceSession
  Effect4.Laws.Program.ExpansionAddresses Effect4.Laws.Program.SourceTable` (scratch file under the
  session scratchpad): "163 declarations within [propext, Quot.sound], 0 of them modulo planned
  goals; 0 planned goals".
- The first audit refused: `List.filter_eq_nil_iff` reaches `Classical.choice` through
  `Classical.propDecidable`. `List.filter_eq_self` was used too. Both are replaced by two facts
  proved by induction (`List.filter_eq_nil_of_all_false`, `List.filter_eq_self_of_all`).
- A probe (`lake env lean`, scratch): the scenario programs of `Test/Dogfood` hold no layer
  reference after elaboration. The edit session dogfood's `client`, P1's `program1` (six rows)
  and `fetchModule` each answer `refs 0`; `Test.Program.DefinitionsControls.moduleLayerProg`
  answers `refs 2`. So `Test/Dogfood/EditSession.lean`'s `expandRefs` is the identity on its
  program.
- Not run: the roots, `Test.All`, `make check-*`. The seat's change reaches no behaviour gate: the
  session tool is in none.

## Reused declarations (reuse first, row 376 (3))

- The edit session and its laws: `EditSession`, `EditSession.open`, `EditSession.feed`,
  `EditSession.view`, `Edit.Step`, `Table.typedAt` (`src/Effect4/Program/Edit.lean`);
  `EditSession.open_coherent`, `EditSession.feed_coherent`, `EditSession.feed_keeps`,
  `EditSession.Coherent.ext`, `Table.typedAt_table`, `Sketch.tableEntry_path`
  (`src/Effect4/Laws/Program/Edit.lean`).
- The sketch and its laws: `Sketch`, `Sketch.check`, `Sketch.fillAt`, `Sketch.omitAt`,
  `Sketch.tableEntry`, `Sketch.table` (`src/Effect4/Program/Sketch.lean`);
  `Sketch.table_result_refusal_none`, `Sketch.fillAt_of_replaceAt`
  (`src/Effect4/Laws/Program/Sketch.lean`); `Sketch.annotate`
  (`src/Effect4/Program/Typing/PartsTable.lean`); `Sketch.annotate_eq_table`,
  `Sketch.fillAt_some` (`src/Effect4/Laws/Program/Typing/PartsTable.lean`).
- The expansion: `Eff.expandRefs`, `Eff.expandRound` and siblings, `Eff.refSites`,
  `Eff.firstRefFault`, `Eff.firstRefFault_eq_none`, `Path.properPrefix`
  (`src/Effect4/Program/Refs.lean`); `expandRefs_eq_self_of_refSites_nil`
  (`src/Effect4/Laws/Program/ReferenceTyping.lean`); `typeOfProgram`
  (`src/Effect4/Program/Typing.lean`).
- The addresses: `Node.addresses`, `Table.Entry` (`src/Effect4/Program/Typing/Table.lean`);
  `Node.addresses_eq_cons`, `Node.childAddresses` (`src/Effect4/Laws/Program/Typing/Annotate.lean`);
  `mem_addresses_iff`, `addresses_eff_head` (`src/Effect4/Laws/Program/Typing/Table.lean`);
  `Node.at_append` (`src/Effect4/Laws/Program/Address.lean`); `Node.sizeOf_child_lt`, `refYield`,
  `mem_refSites_of_at` (`src/Effect4/Laws/Program/PathFold.lean`); `Node.replaceAt_spec`
  (`src/Effect4/Laws/Program/References.lean`).
- Seat ADDRESS's `at_of_mem_refSites` (`src/Effect4/Laws/Program/AddressMove.lean`). This seat
  had proved the same statement under the same name; it was deleted at the merge and ADDRESS's
  is used.
- The codecs: `Canonical.decode` and `Canonical.encode` at `RowTable` and at
  `List (ServiceKey × Ty)` (the derived store instances), `Wire.decodeHoles`, `Sketch.decode_exact`,
  `sha256` and `Digest.hex` (`src/Effect4/Store/Carrier/Digest.lean`).

## Gather candidates (one law, two homes)

- `List.filter_eq_self_of_all` (here) and `filter_all_true` (`src/Effect4/Laws/Run/Journal.lean`)
  are one fact. A common list bank should hold one. Importing `Laws/Run/Journal.lean` into the
  program laws was too heavy.
- `Node.child_expandRound` (here) and ADDRESS's `Node.child_mapRefs`
  (`src/Effect4/Laws/Program/AddressMove.lean`) are one law: a fold by `EffAlgebra.onRef` commutes
  with `Node.child` off the references. One lemma over `EffAlgebra.onRef g` would give both.
- `Node.child_ref` (here) and ADDRESS's `Node.at_ref_cons`: a reference has no child.

## Placement of the obligations (written before the work)

`AGENTS.md` asks for five fields before an obligation is worked.

### `source-annotation-agrees` (proposed claim, role compatibility)

1. **Concept**: `initial-algebras-folds`. The address table is a fold (`annotate-table`). The
   expansion (`reference-expansion-complete`) is a fold that keeps every address of the program,
   in its order. It adds addresses only strictly below a reference's site. So the expansion's
   table, at the source's addresses, is a table of the source.
2. **Question**: the proposed registry claim `source-annotation-agrees`, from Codex's live-graph
   theory (`docs/research/2026-10-10-live-graph-support/THEORY.md` §8). Its pointer is
   `Sketch.sourceAnnotate_eq_sourceTable`. One traversal of the expansion, at the source's
   addresses, equals the specification: one entry for each address of the sketch as written.
   The root holds the check through the references, and every other address the expansion's
   entry there. No planned goal is needed: the slice that states it proves it.
3. **Reach**: every sketch and application, refused programs included. A program whose
   references are ill formed has the reference's located refusal at its root, as `Api.explain`.
   The check at the root is program admission's typing (`typeOfProgram`) at the application's
   signature extended by the hole table. The address map is the identity on the source's
   addresses, for every operation alphabet.
4. **Does not establish**:
   - an address strictly below a reference's site maps to no source address: a copy is dropped;
   - a refusal located inside a copy keeps the expansion's address, as program admission's does;
   - an edit inside a referenced layer splices: it checks again;
   - a run: the compile redirects a reference, it does not expand it;
   - the cost, which no theorem counts.
5. **Unlocks**: R14 on programs with layer references, row 341 step 2's module layers included.
   The edit session tool at a real application (row 373 (10)). Obligation O2.

### `source-session-coherent` (proposed claim, role preservation)

1. **Concept**: `initial-algebras-folds`; the edit session's property (`edit-session-coherent`)
   carried to the sketch as written.
2. **Question**: the proposed claim `source-session-coherent`, pointer
   `SourceSession.reached_view`. After an open and any edits, the session shows the table at the
   source's addresses, its refusals and its type through the references.
   Its helpers are steps of it.
3. **Reach**: one application; every sketch; every list of edits. An edit splices where the
   expansion of the edited sketch is the expansion's own edit at the same address; any other edit
   checks again.
4. **Does not establish**: that an edit inside a referenced layer splices; a run; the cost.
5. **Unlocks**: the session tool at an application, with layer references (row 373 (7), (10)).

A third claim, `source-session-undo` (role compatibility, pointer `SourceSession.feed_undo`),
carries `edit-session-undo` to the sketch as written, with the same reach.

## Open obligations

1. **The battery of step 4** (not written). The plan, from the probe above:
   - The scenario: `Test.Program.LayerSharingContract.twice`, the counted-layer diamond of DI-71.
     The truth lane runs it on rc.112 as `pDiamond` (`harness/truth/Truth.lean`), and
     `Test.Program.AuthorContract.twice` authors it through the surface. Its target is
     `.effect kA body`, a layer that holds a program, so an edit can reach it through the tool.
   - Through `Tools.Session.answer`: an open types, where `EditSession.open` refuses
     `layerReference`. That is the red control of the old route. A fill at `[1, 1, 1]` splices.
   - The red control where a reference's target misfits: a fill of the target's body at
     `[1, 0, 0, 0, 0]` with a string. The delta is `rechecked`, since every copy moves. The view
     refuses `valueNotSubtype` at the target `[1, 0, 0, 0]`, and `Api.explain` gives the same
     refusal.
   - A red control of an ill-formed reference: a filling whose reference names a program. The
     root refuses `referenceIllFormed` at the site.
   - The application: P1's `program1` (`Test/Dogfood/P1HttpCache.lean`, six rows) opens at its
     `rows` and types, and refuses at the empty application.
   - Readers: `SourceSession.reached_view`, `Sketch.sourceAnnotate_eq_sourceTable` and
     `Sketch.sourceCheck_toOption` at the scenario. Per row 375 and the coordinator: no byte pins.
2. **Registry and semantics** (the coordinator's): the three proposed claims above; a property
   line under concept 7 of `docs/core/semantics.md`; R14's row in `docs/core/system-map.md` §8.
3. **Readers outside this seat's boundary**:
   - `Tools.View.Run.prepare` (`tools/Tools/View/Run.lean`) still opens
     `EditSession.open ⟨built.table, []⟩` on the program as written. A switch to
     `SourceSession.open` closes the display gap of Codex's `ReferenceViewControl.lean`.
   - `Effect4.Author` (`src/Effect4/Author.lean`) does not re-export the two new core modules.
   - `Tools.Query.Answer.app`'s docstring still says the application is the empty one.
4. **`Tools.Session.Snapshot`** still opens at the empty application on the program as written.
   Its consumer is the research MCP adapter. Keyed on the application's bytes too, it would open a
   `SourceSession`, and its three laws carry over by the same proofs.
5. **A refusal inside a copy** keeps the expansion's address, as `Api.explain`'s does. A body's
   reference to an ill-typed module layer is checked before the layer. So the root's refusal
   names an address of the copy. Moving it to the target would use `Checker.check_rebase`
   (`checker-base-natural`).
6. **Two laws not stated**:
   - the repaint set at the source's addresses: the tool names `Sketch.table_fill` at the
     expansion;
   - the connector for `feed` on a sketch with no reference: only the open's is proved.
7. **`sketch-admission`** stays open: `open` decodes the application and does not run `admitSig`.

## What this receipt does not establish

- The theorems are proved, and `#axiom_audit` is tested over the four modules. The tool's answers on a program with
  references were not run through a battery (item 1).
- No root, no `Test.All` and no behaviour gate ran.
- The probe's counts are a finite reading of four programs at `0d918c680`.
