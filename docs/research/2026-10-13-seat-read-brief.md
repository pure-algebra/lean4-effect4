# Seat READ brief: the emitted module reads back whole, and its keys read by name (2026-10-13)

Status: brief (history, not authority). Coordinator: the main session. Branch `seat/read`,
worktree `~/Dev/lean4-effect4-read`, base `d05312985` on `refactor/phase1-phase3`. The packages
are cloned; your first `lake build` through the slot script restores from Lake's cache.

## The one goal

The to-do emitted as an Effect service (slices E1–E3 of
`docs/research/2026-10-13-emitted-services/README.md`, decisions row 378 (19), (20)) reads back
whole, and a user's types name its services by name. Read seat ROWS's receipt first:
`docs/research/2026-10-13-seat-rows-receipt.md`, items 4 and 8 and its section 7.

## What to land, in order

1. **The class-aware header reader** (ROWS's receipt, item 8). Today `readDefHead`, `readParam`
   and `DefDecl.readable` (`src/Effect4/Codegen/Read.lean`) read declaration columns with the
   class-free `readTyChecked` (`src/Effect4/Codegen/Classes.lean`). So an application whose error
   column carries a payload class (the to-do's `NotFound`) falls outside `blockReadable`
   (`src/Effect4/Laws/Api/ModuleReadable.lean`). Read a class name as its payload record, under
   the module's classes. Prove again `readDefHead_printDef` and `readModule_printModule_defs`.
   Change `ts/eff/read.ts` the same way. Success: the to-do's service block is `blockReadable`.
2. **The row services read back** (ROWS's receipt, item 4). `rowServiceDecls`
   (`src/Effect4/Codegen/RowServices.lean`) prints `export const NsKey = Context.Service<…>(…)`
   and `export const Ns = Object.assign(NsKey, { … })`. No reader reads them, in Lean or in
   TypeScript. Read them back to the row table's services, exactly. Success: the whole emitted
   file of the to-do reads back.
3. **Keys by name** (ROWS's receipt, section 7). A user's type shows
   `Effect<Todo, SqlError, "k30_6">`. Add the smallest key-to-name map: a signature hook
   `keyName : ServiceKey → Option String`, `none` by default, filled from `rowServices`. The key
   spelling in `src/Effect4/Codegen/Types.lean` takes it once (`keyIdentifier`, `keyText`'s
   callers, `readRequirement`). A named key prints as its namespace's literal, so R reads
   `"TodoRepo"`. Every other key keeps `keyText`, so the corpus does not move. One spelling: the
   printer, both readers and `Context.Context<R>` read it from the one place.

## Placement (AGENTS.md, Trust)

Concept `reification` (`docs/core/semantics.md`); requirement R5 or R8 as the read-back laws now
name it (`readModule_printModule_defs`). Reach: the to-do's emitted file, and any module whose
classes and row services the readers name. Not established: tsgo or rc.112 behaviour, which the
gates check.

## Rules

- Reuse first: search the registry, the proof graph and the aesop banks before a new definition.
  The receipt lists what you reused. A duplicate is a defect.
- Seats SVC and BANK run now. SVC owns `src/Effect4/Codegen/Checked.lean`,
  `src/Effect4/Program/Authoring/ApplicationService.lean`, `Test/Dogfood/Scenario/TodoService.lean`
  and the E4 harness under `harness/truth/`. BANK owns `src/Effect4/Library/Ref/*`,
  `src/Effect4/Laws/Library/Ref/*` and `Test/Dogfood/Bank.lean`. Do not edit them, nor
  `lakefile.toml` or `docs/core/decisions.md`. If a guard in `TodoService.lean` should flip,
  say which in the receipt; the coordinator flips it at the merge.
- Root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) only by appending
  at the end.
- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. Never a bare
  `lake build`, never `lake build Test`.
- TypeScript: `bun --no-install` only; import packages only by directory from `ts/eff/node_modules`
  (link or reference the main checkout's, `~/Dev/lean4-effect4/ts/eff/node_modules`). tsgo 7 is the
  only compiler. No downloads.
- Proofs: aesop and its banks where they close; `simp only [...]`; no `simp_all`, `first`, `try`.
  Audit each touched module with `#axiom_audit` at `[propext, Quot.sound]`.
- Behaviour gates your change reaches: `check-ts-reader` (item 1, 2), `check-host-protocol`
  (item 3). Run them in your worktree once each, at the end.
- Commit on `seat/read` by named paths, each item as it builds. Never push. Never `2>/dev/null`.

## The receipt

`docs/research/2026-10-13-seat-read-receipt.md` (force-added): the one thing to know before
merging, base and head, changed files, commands and results, axiom output, each landed theorem's
placement, open obligations, and whether any evidence is bounded.
