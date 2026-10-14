# Consolidation and Review Receipt (2026-10-13)

## Coordinator Summary

All seven duplicate families from `docs/research/2026-10-13-seat-address-receipt.md` are consolidated in the working tree.
The file `docs/research/2026-10-13-gemini-consolidation/commits.txt` lists the seven ordered `git add` and `git commit` commands.
Today's landings leave `RowServices.rowServiceFault` and `ns ++ "Key"` unwired in `Print.printEntry` and `Checked.emitModule`.
Those files sit inside the `seat SVC` fence, so §3 ranks the defects and gives their exact repairs.

- **Base commit**: `3e86319b2`
- **Branch**: `gemini/consolidation`
- **Fenced files touched**: none

## Part 1 — Consolidation of the Seven Duplicate Families

```mermaid
flowchart LR
  FO["Effect4.Data.FieldOrder"] --> Refs["Effect4.Program.Refs"]
  Refs --> PAddr["Effect4.Program.Address"]
  PAddr --> LAddr["Effect4.Laws.Program.Address"]
  PAddr --> LMove["Effect4.Laws.Program.AddressMove"]
  Refs --> LRefs["Effect4.Laws.Program.References"]
  Refs --> LOrder["Effect4.Laws.Program.PathOrder"]
  LAddr --> LReplace["Effect4.Laws.Program.Typing.Replace"]
  LAddr --> LSplice["Effect4.Laws.Program.Typing.Splice"]
  LAddr --> LParts["Effect4.Laws.Program.Typing.PartsTable"]
  LAddr --> LAgree["Effect4.Laws.Program.Agreement"]
  LAddr --> LTerms["Effect4.Laws.Program.Typed.Denotation.Terms"]
  LAddr --> LGen["Effect4.Laws.Program.Typed.Commands.Clauses.Gen"]
  LMove --> LScope["Effect4.Laws.Program.Typed.Scope"]
  LRefs --> LScope
  LAgree --> LIntro["Effect4.Laws.Program.Intro.*"]
```

### Summary by Family (Commit Order)

| Order | Family | Surviving Home | Deleted Declarations | Rewritten Callers |
| --- | --- | --- | --- | --- |
| 1 | 7 — Dead access lemmas | `Node.replaceAt` (`src/Effect4/Program/Refs.lean`), `Node.replaceLayerAt_spec` (`src/Effect4/Laws/Program/References.lean`) | `Node.replaceLayerAt_eq_replaceAt`, `Node.layerAt_replaceLayerAt` (`src/Effect4/Laws/Program/References.lean`) | 0 (receipt: 0) |
| 2 | 5 — The bodies' spine | `Path.spineIndex_append` (`src/Effect4/Laws/Program/AddressMove.lean`), `spineParams_index` (`src/Effect4/Laws/Program/Typed/Scope.lean`) | `spineParams_append` (`src/Effect4/Laws/Program/Typed/Scope.lean`) | 3 in `src/Effect4/Laws/Program/Typed/Scope.lean` (receipt: 3) |
| 3 | 3 — A layer's node | `Node.layerAt_eq_some_iff` (`src/Effect4/Laws/Program/References.lean`) | `Node.at_of_layerAt` (`src/Effect4/Laws/Program/Typed/Scope.lean`) | 5 across `Typed/Denotation.lean` and `Typed/LayerArm.lean` (receipt: 5) |
| 4 | 2 — A machine point's child | `at_child`, `at_childWith` (`src/Effect4/Laws/Program/Agreement.lean`) | `at_child_of`, `at_childWith_of` (`src/Effect4/Laws/Program/Intro/Weight.lean`) | 41 across `Intro/*.lean` and `Typed/Mask.lean` (receipt: 37 external + 4 internal) |
| 5 | 1 — One more child index | `Node.at_child`, `Node.at_append`, `Node.at_snoc` (`src/Effect4/Laws/Program/Address.lean`) | `Agreement.Node.at_append` (`Laws/Program/Agreement.lean`), `node_at_child` (`Typed/Denotation/Terms.lean`), `at_snoc2`, `at_snoc1`, `at_frame` (`Typed/Commands/Clauses/Gen.lean`) | 46 across 10 modules (receipt: 45 external + 1 internal) |
| 6 | 6 — Stranded basis | `Table.under` (`src/Effect4/Program/Address.lean`), 4 `Table.under_*` and 9 `Node.*` lemmas (`src/Effect4/Laws/Program/Address.lean`) | Original definitions in `Program/Typing/Splice.lean` and `Laws/Program/Typing/{Replace,Splice,PartsTable}.lean` | 0 (namespaces stay unchanged) |
| 7 | 4 — Order on keys and paths | `Field.ltKey` and `Field.ltKey_*` (`src/Effect4/Data/FieldOrder.lean`), `abbrev Path.lt := Field.ltKey` (`src/Effect4/Program/Refs.lean`) | `def Path.lt` (`Program/Refs.lean`), `lt_cons_iff`, `lt_irrefl`, `lt_trans`, `lt_asymm`, `lt_trichotomy`, `lt_total` (`Laws/Program/PathOrder.lean`) | 10 across `References.lean`, `PathOrder.lean`, `Hoisting.lean`, `HoistingTotal.lean`, `Laws/Codegen/Module.lean` |

### Placement of New and Generalized Lemmas

- `Node.at_snoc` (`src/Effect4/Laws/Program/Address.lean`):
  - **Concept**: `initial-algebras-folds` (`docs/core/semantics.md` §2.7), requirement R14.
  - **Question**: serves `address-composes` (`Node.at_child`) and `compile_sound` as the one-step path-extension law.
  - **Reach**: every operation alphabet `Op`, any root node `root : Node Op`, path `path`, and child index `i`.
  - **Does not establish**: typing, scope safety, or machine progress.
  - **Consumers**: `Node.at_child` (`src/Effect4/Laws/Program/Address.lean`), `compileStmts_Step_at` (`src/Effect4/Laws/Program/Agreement.lean`), `actionTerm_scopedAt_of_at` (`src/Effect4/Laws/Program/NativeActionScope.lean`), `compile_Step_hook` (`src/Effect4/Laws/Program/Simulation/Hooks.lean`), and `action_opportunities_of_at` (`src/Effect4/Laws/Program/SourceOpportunityActions.lean`).
- `at_child` and `at_childWith` (`src/Effect4/Laws/Program/Agreement.lean`):
  - **Concept**: `frame-machine` (`docs/core/semantics.md` §2.3), requirement R4.
  - **Question**: serves `run_eq_meaning` (`src/Effect4/Laws/Program/Intro.lean`) and `typed-adequacy`.
  - **Reach**: `NativeOp` programs, any addressed node `n : Node NativeOp` at `q.path` and child index `i`.
  - **Does not establish**: evaluation of terms or machine progress.
  - **Consumers**: `src/Effect4/Laws/Program/Intro/{Weight,Sequential,Errors,Fibers,Layer,Scope}.lean` and `src/Effect4/Laws/Program/Typed/Mask.lean`.

### Detail by Family

1. **Family 7 (`dead access lemmas`)**:
   - Removed `Node.replaceLayerAt_eq_replaceAt` and `Node.layerAt_replaceLayerAt` from `src/Effect4/Laws/Program/References.lean`.
   - Both lemmas had zero callers in `src/` and `Test/`.
2. **Family 5 (`the bodies' spine`)**:
   - Imported `Effect4.Laws.Program.AddressMove` into `src/Effect4/Laws/Program/Typed/Scope.lean`.
   - Moved `spineParams_index` above `scopeParams_child` and deleted `spineParams_append` in `src/Effect4/Laws/Program/Typed/Scope.lean`.
   - Rewrote `scopeParams_child`, `scopeParams_below`, and `scopeParams_layer_below` to rewrite by `spineParams_index` and `Path.spineIndex_append`.
3. **Family 3 (`a layer's node`)**:
   - Deleted `Node.at_of_layerAt` from `src/Effect4/Laws/Program/Typed/Scope.lean`.
   - Rewrote the 1 caller in `src/Effect4/Laws/Program/Typed/Denotation.lean` and the 4 callers in `src/Effect4/Laws/Program/Typed/LayerArm.lean` to `(Node.layerAt_eq_some_iff _ _ _).mp`.
4. **Family 2 (`a machine point's child`)**:
   - Generalized `at_child` and `at_childWith` in `src/Effect4/Laws/Program/Agreement.lean` from `{e : NativeEff}` to `{n : Node NativeOp}`.
   - Deleted `at_child_of` and `at_childWith_of` from `src/Effect4/Laws/Program/Intro/Weight.lean`.
   - Rewrote all 33 uses of `at_child_of` and 8 uses of `at_childWith_of` across `Intro/{Weight,Sequential,Errors,Fibers,Layer,Scope}.lean` and `Typed/Mask.lean`.
5. **Family 1 (`one more child index`)**:
   - Added `Node.at_snoc` in `src/Effect4/Laws/Program/Address.lean`.
   - Deleted `Agreement.Node.at_append` from `src/Effect4/Laws/Program/Agreement.lean` and rewrote its 5 callers to `Node.at_snoc`.
   - Deleted `node_at_child` from `src/Effect4/Laws/Program/Typed/Denotation/Terms.lean` and rewrote all 35 callers across `Terms.lean`, `Arguments.lean`, `LayerArm.lean`, and `Denotation.lean` to `Node.at_child`.
   - Deleted `at_snoc2`, `at_snoc1`, and `at_frame` from `src/Effect4/Laws/Program/Typed/Commands/Clauses/Gen.lean` and rewrote their 6 callers to `Node.at_child` and `Node.at_append`.
6. **Family 6 (`stranded basis in Laws/Program/Typing/`)**:
   - Moved `Table.under` from `src/Effect4/Program/Typing/Splice.lean` to `src/Effect4/Program/Address.lean`.
   - Moved `Table.under_append`, `Table.under_self`, `Table.under_prefix_false`, `Table.under_sibling_false`, `Node.child_add_three`, `Node.at_stmts_nil`, `Node.at_layers_nil`, `Node.replaceAt_eff`, `Node.replaceAt_defs_main`, `Node.replaceAt_defs_body`, `Node.replaceAt_effs_head`, `Node.replaceAt_effs_tail`, and `Node.replaceAt_layers_cons` from `src/Effect4/Laws/Program/Typing/{Replace,Splice,PartsTable}.lean` to `src/Effect4/Laws/Program/Address.lean`.
7. **Family 4 (`the order on keys and paths`)**:
   - Imported `Effect4.Data.FieldOrder` in `src/Effect4/Program/Refs.lean` and replaced `def Path.lt` with `abbrev Path.lt : List Nat → List Nat → Bool := Field.ltKey`.
   - Replaced the two `#guard` lines in `src/Effect4/Program/Refs.lean` with `example : … := rfl`. The kernel checks both equations without precompiled VM code from `FieldOrder`.
   - Deleted `lt_cons_iff`, `lt_irrefl`, `lt_trans`, `lt_asymm`, `lt_trichotomy`, and `lt_total` from `src/Effect4/Laws/Program/PathOrder.lean`.
   - Aligned `sortBy_pairwise` and `sortBy_eq_self` in `src/Effect4/Laws/Program/PathOrder.lean` with the Boolean equations `Field.ltKey_total` and `Field.ltKey_asymm`, and updated `PathOrder.lean`, `References.lean`, `Hoisting.lean`, `HoistingTotal.lean`, and `Laws/Codegen/Module.lean`.

## Part 2 — Review of Today's Nine Landings

Reviewed commits: `6f32c88cd`, `9cff5c7cf`, `0c1760dd9`, `45761a86a`, `c4f56a879`, `23f95aac2`, `d2d10b383`, `f463ee53b`, and `60f10bc4c`.
Reviewed receipts: `docs/research/2026-10-13-seat-svc-receipt.md`, `docs/research/2026-10-13-seat-rows-receipt.md`, and `docs/research/2026-10-13-seat-bank-receipt.md`.

### Ranked Findings (Fenced or Cross-Seat)

#### 1. High — `RowServices.rowServiceFault` and `ns ++ "Key"` are unwired in `Print.printEntry` and `Checked.emitModule`

- **Commits**: `9cff5c7cf` (`seat ROWS`) and `d2d10b383` (integration into `Checked.lean` and `Print.lean`).
- **Declarations**: `rowServiceFault` and `rowNameUses` in `src/Effect4/Codegen/RowServices.lean`; `rowNameUses` and `printEntry` in `src/Effect4/Codegen/Print.lean`; `ModuleEmission.file` in `src/Effect4/Codegen/Checked.lean`.
- **Defect**:
  1. `ModuleEmission.file` (`src/Effect4/Codegen/Checked.lean`) emits `(rowServices table).map printRowService`, which declares `class <Ns>Key` and `const <Ns>` for every dotted row.
  2. Neither `Print.printEntry` nor `Checked.emitModule` calls `RowServices.rowServiceFault table`. Conflicting `serviceKey` strings or unsafe method names after the dot pass `emitModule` without refusal and emit invalid TypeScript.
  3. `Effect4.Program.rowNameUses` (`src/Effect4/Codegen/Print.lean`) includes `qualifiedRoot row.spelling` (`ns`) and `RowArg.names row.trailing`, but omits `ns ++ "Key"`. Meanwhile `Effect4.Codegen.rowNameUses` (`src/Effect4/Codegen/RowServices.lean`) includes `ns ++ "Key"`, omits `RowArg.names row.trailing`, and has zero callers outside `RowServices.lean`. Consequently, a definition, parameter, or export named `<Ns>Key` passes `printEntry` and collides with the emitted `class <Ns>Key`.
  4. In `rowBreaksServices` (`src/Effect4/Codegen/RowServices.lean`), the `splitDot? row.spelling = none` arm returns `false`. A row with `"Clock."` or `"a.b.c"` has `splitDot? = none`, while `SourceBindings.qualifiedRoot` returns `some "Clock"` or `some "a"`. The expression printer then emits a member call while `rowServices` emits no service declaration.
- **Proposed Fix (for `seat SVC` / coordinator)**:
  1. Return `row.spelling.contains '.'` in the `splitDot? = none` arm of `rowBreaksServices` (`src/Effect4/Codegen/RowServices.lean`). Make the `NsKey` check symmetric (`s.ns == ns ++ "Key" || ns == s.ns ++ "Key"`).
  2. Unify the two `rowNameUses` definitions by adding `ns ++ "Key"` to `Effect4.Program.rowNameUses` in `src/Effect4/Codegen/Print.lean` and deleting the duplicate `Effect4.Codegen.rowNameUses` in `src/Effect4/Codegen/RowServices.lean`.
  3. Call `rowServiceFault table` inside `Print.printEntry` (and check `name != ns && name != ns ++ "Key"`), then update `printEntry_checks` in `src/Effect4/Codegen/Print.lean` and `src/Effect4/Laws/Api/Codegen.lean`.

#### 2. Medium — `Print.serviceNamesFault`, `paramsNameFault`, and `classNameFault` miss collisions with application service names (`sv.name` and `sv.name ++ "Layer"`)

- **Commits**: `6f32c88cd` (`seat SVC`) and `d2d10b383`.
- **Declarations**: `serviceNamesFault`, `paramsNameFault`, and `classNameFault` in `src/Effect4/Codegen/Print.lean`.
- **Defect**:
  1. `serviceNamesFault` checks `table.any (fun row => row.spelling == sv.name)` instead of `(rowNameUses table).contains sv.name || (rowNameUses table).contains (sv.name ++ "Layer")`. An application service named `Clock` alongside a dotted row `"Clock.now"` passes `serviceNamesFault`, and the file then emits two `const Clock = ServiceMap.Service…` declarations.
  2. `paramsNameFault` checks `defs.any (·.name == q.name)` against definition names (`add`), not service names (`TodoRepo` or `TodoRepoLayer`). A method parameter named `TodoRepo` shadows the service tag inside `TodoRepoLayer`.
  3. `classNameFault` checks payload classes against `d.name` and `d.params`, not against `sv.name` or `sv.name ++ "Layer"`. A payload class named `TodoRepo` collides with `const TodoRepo`.
  4. `serviceFault` (`src/Effect4/Program/Eff.lean`) checks `defs.any (fun d => d.name == sv.name || d.name == sv.name ++ "Layer")`, but does not check whether one service's `sv.name` equals another service's `sv'.name ++ "Layer"`.
- **Proposed Fix (for `seat SVC`)**:
  - In `serviceNamesFault` (`src/Effect4/Codegen/Print.lean`), check `(rowNameUses table).contains sv.name || (rowNameUses table).contains (sv.name ++ "Layer")`.
  - Include `(servicesOf defs).flatMap (fun sv => [sv.name, sv.name ++ "Layer"])` in `paramsNameFault` and `classNameFault` (`src/Effect4/Codegen/Print.lean`), and check cross-service `sv.name == sv'.name ++ "Layer"` in `serviceFault` (`src/Effect4/Program/Eff.lean`).

#### 3. Low — General `Block`, `HostRuns`, and `RefHeap` helpers live inside leaf module `src/Effect4/Laws/Library/Ref/Cache.lean`

- **Commit**: `60f10bc4c` (`seat BANK`, fenced under `seat IMPOSE`).
- **Declarations**: `bodyOf`, `refPoke_peek`, `hostRun_bind_straight`, and `hostRun_bind_call` in `src/Effect4/Laws/Library/Ref/Cache.lean`.
- **Defect**:
  - `bodyOf` (`(blockOf? p).bind fun b => b.2.1[k]?`) is a general definition-block projection that belongs beside `blockOf?` in `src/Effect4/Laws/Program/Block.lean`.
  - `hostRun_bind_straight` and `hostRun_bind_call` are general `hostRun` laws over `RowsSig table` that belong beside `hostRun_bindExit`, `hostRun_straight`, and `hostRun_call` in `src/Effect4/Laws/Program/HostRuns.lean`.
  - `refPoke_peek` (`refPeek heap q = some v → refPoke heap q v = heap`) is a general `RefHeap` law that belongs in `src/Effect4/Laws/Library/Ref/Operations.lean`.
- **Proposed Fix (for `seat IMPOSE`)**:
  - Move `bodyOf` to `src/Effect4/Laws/Program/Block.lean`, `hostRun_bind_straight` and `hostRun_bind_call` to `src/Effect4/Laws/Program/HostRuns.lean`, and `refPoke_peek` to `src/Effect4/Laws/Library/Ref/Operations.lean` when the `seat IMPOSE` fence opens.

#### 4. Low — Duplicate `List.mapM` over `Except` lemmas and byte-order helper in fenced `seat SVC` modules

- **Commits**: `45761a86a` and `d2d10b383`.
- **Declarations**: `mapM_error_mem` and `mapM_ok_each` in `src/Effect4/Laws/Program/ApplicationService.lean`; `bytesLe` in `src/Effect4/Codegen/Checked.lean`.
- **Defect**:
  - `mapM_error_mem` and `mapM_ok_each` in `src/Effect4/Laws/Program/ApplicationService.lean` sit one directory away from `mapM_ok_mem` and `bind_ok` in `src/Effect4/Laws/Program/Authoring.lean`.
  - `bytesLe` in `src/Effect4/Codegen/Checked.lean` re-implements lexicographic byte comparison alongside `Field.ltKey` (`src/Effect4/Data/FieldOrder.lean`).
- **Proposed Fix (for `seat SVC`)**:
  - Move `mapM_error_mem` and `mapM_ok_each` next to `mapM_ok_mem` in `src/Effect4/Laws/Program/Authoring.lean`, and express `bytesLe` in `src/Effect4/Codegen/Checked.lean` through `Field.ltKey` on `Field.bytesKey`.

## Verification and Axiom Gate

- **Changed files (30 files)**:
  - `src/Effect4/Program/Address.lean`
  - `src/Effect4/Program/Refs.lean`
  - `src/Effect4/Program/Typing/Splice.lean`
  - `src/Effect4/Laws/Codegen/Module.lean`
  - `src/Effect4/Laws/Program/Address.lean`
  - `src/Effect4/Laws/Program/AddressMove.lean`
  - `src/Effect4/Laws/Program/Agreement.lean`
  - `src/Effect4/Laws/Program/Hoisting.lean`
  - `src/Effect4/Laws/Program/HoistingTotal.lean`
  - `src/Effect4/Laws/Program/Intro/Errors.lean`
  - `src/Effect4/Laws/Program/Intro/Fibers.lean`
  - `src/Effect4/Laws/Program/Intro/Layer.lean`
  - `src/Effect4/Laws/Program/Intro/Scope.lean`
  - `src/Effect4/Laws/Program/Intro/Sequential.lean`
  - `src/Effect4/Laws/Program/Intro/Weight.lean`
  - `src/Effect4/Laws/Program/NativeActionScope.lean`
  - `src/Effect4/Laws/Program/PathOrder.lean`
  - `src/Effect4/Laws/Program/References.lean`
  - `src/Effect4/Laws/Program/Simulation/Hooks.lean`
  - `src/Effect4/Laws/Program/SourceOpportunityActions.lean`
  - `src/Effect4/Laws/Program/Typed/Commands/Clauses/Gen.lean`
  - `src/Effect4/Laws/Program/Typed/Denotation.lean`
  - `src/Effect4/Laws/Program/Typed/Denotation/Arguments.lean`
  - `src/Effect4/Laws/Program/Typed/Denotation/Terms.lean`
  - `src/Effect4/Laws/Program/Typed/LayerArm.lean`
  - `src/Effect4/Laws/Program/Typed/Mask.lean`
  - `src/Effect4/Laws/Program/Typed/Scope.lean`
  - `src/Effect4/Laws/Program/Typing/PartsTable.lean`
  - `src/Effect4/Laws/Program/Typing/Replace.lean`
  - `src/Effect4/Laws/Program/Typing/Splice.lean`
- **Build command and result**:
  - `LEAN_NUM_THREADS=2 lake build Effect4.Program.Address Effect4.Program.Refs Effect4.Program.Typing.Splice Effect4.Laws.Program.References Effect4.Laws.Program.Address Effect4.Laws.Program.AddressMove Effect4.Laws.Program.PathOrder Effect4.Laws.Program.Hoisting Effect4.Laws.Program.HoistingTotal Effect4.Laws.Codegen.Module Effect4.Laws.Program.ReferenceExpansion Effect4.Laws.Program.Typing.Replace Effect4.Laws.Program.Typing.Splice Effect4.Laws.Program.Typing.PartsTable Effect4.Laws.Program.Typed.Scope Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Typed.Denotation.Terms Effect4.Laws.Program.Typed.Denotation.Arguments Effect4.Laws.Program.Typed.Commands.Clauses.Gen Effect4.Laws.Program.Typed.LayerArm Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Typed.Mask Effect4.Laws.Program.Agreement Effect4.Laws.Program.Intro.Weight Effect4.Laws.Program.Intro.Sequential Effect4.Laws.Program.Intro.Errors Effect4.Laws.Program.Intro.Fibers Effect4.Laws.Program.Intro.Layer Effect4.Laws.Program.Intro.Scope Effect4.Laws.Program.Intro Effect4.Laws.Program.NativeActionScope Effect4.Laws.Program.Simulation.Hooks Effect4.Laws.Program.SourceOpportunityActions`
  - Result: `Build completed successfully (541 jobs).` (0 errors, 0 warnings).
- **Axiom gate command and result**:
  - `LEAN_NUM_THREADS=2 lake env lean scratch/Audit.lean`
  - Result: `#axiom_audit: 5656 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- **Open obligations**: none in the consolidated modules; the four fenced findings in §3 await `seat SVC` and `seat IMPOSE`.
- **Bounded or host-only evidence**: none.
