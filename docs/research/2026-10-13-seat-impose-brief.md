# Seat IMPOSE brief: the to-do imposes the banked Ref cache by reference (2026-10-13)

Status: brief (history, not authority). Coordinator: the main session. Branch `seat/impose`,
worktree `~/Dev/lean4-effect4-impose`, base: the coordinator's head when the worktree was made.

## The one goal

Decisions row 378 (8): the to-do application, end to end, with one banked module imposed by
reference. The banked module landed: the Ref cache, its model and its transfer law
`cache_agrees` (`src/Effect4/Library/Ref/Cache.lean`, `src/Effect4/Laws/Library/Ref/Cache.lean`),
and its bank entry (`Test/Dogfood/Bank.lean`). Seat BANK's receipt
(`docs/research/2026-10-13-seat-bank-receipt.md`, "How the to-do's `list` would impose the
cache" and "Open obligations") names the missing pieces. Read it first, then the plan of programs
as parameters (`docs/research/2026-10-09-program-parameters.md`, §§ 9–11).

## What to land, in order

1. **Authoring a definition with program parameters, and an invocation with programs.**
   `DefSrc` (`src/Effect4/Program/Authoring.lean`) declares no program parameter, and
   `Def.invoke` writes `perform (call k)`, which the checker refuses for a definition with one
   (`Test/Program/InvokeControls.lean`). Add the surface form that writes `Eff.invoke k r ps`. HO-3
   already prints and reads both (the plan's §11).
2. **Entries that invoke the application's definitions.** `Application.openProgram`
   (`src/Effect4/Program/Authoring/Application.lean`) elaborates an entry with no definition in
   scope. Give an application a block of definitions that its entries invoke, with the block's
   bytes kept, so the built application can pin a banked block's digest (row 378 (4)).
3. **HO-5: a service method with a program parameter.** `printServices` refuses one
   (`serviceFaultOf`, `src/Effect4/Codegen/Print.lean`). Forward its programs, and read it back.
   The reader half touches `src/Effect4/Codegen/Read.lean`, which seat READ is editing: do item 3
   after the coordinator tells you READ has merged, and merge the main line first.
4. **The imposition.** The to-do's `list` reads through the cache, with `TodoRepo.all` as its
   loader; `add`, `complete` and `remove` invalidate after a successful write. The built
   application pins `refCache.digest`. A claim of the to-do that reads `list` is restated against
   the cache's model, carried by `cache_agrees` through the block meaning
   (`src/Effect4/Laws/Program/Block.lean`, `invoke_unfolds_at_limit`). Seat SVC is landing E4 on
   today's to-do: start item 4 only after the coordinator tells you E4 has merged. Then regenerate
   what the to-do's change reaches: lane S (`ocaml/engine/test/scenarios/write.lean`) and the
   keyed lane (`make check-host-protocol`).

## Placement (AGENTS.md, Trust)

Item 4's restated claim: concept `translation-simulation`; requirement R10 (a composed module's
law); its question is a registry claim whose witness carries `cache_agrees` to the to-do. Items
1–3 serve `invoke-typed` and `module-defs-round-trip` (the plan's §10). Write the five lines for
each theorem before you start it.

## Rules

- Reuse first: search the registry, the proof graph and the aesop banks before a new definition.
  The receipt lists what you reused. A duplicate is a defect.
- Seats SVC and READ run now. SVC owns `src/Effect4/Codegen/Checked.lean`,
  `src/Effect4/Program/Authoring/ApplicationService.lean`, `Test/Dogfood/Scenario/TodoService.lean`
  and `harness/truth/service/`. READ owns `src/Effect4/Codegen/{Read,Classes,Types}.lean`,
  `src/Effect4/Laws/Api/ModuleReadable.lean` and `ts/eff/read.ts`. Do not edit them until the
  coordinator says they merged. Never edit `lakefile.toml` or `docs/core/decisions.md`.
- Root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) only by appending
  at the end.
- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. Never a bare
  `lake build`, never `lake build Test`.
- TypeScript: `bun --no-install` only; packages by directory from the linked `node_modules`;
  tsgo 7 is the one compiler. No downloads.
- Proofs: aesop and its banks where they close; `simp only [...]`; no `simp_all`, `first`, `try`.
  Audit each touched module with `#axiom_audit` at `[propext, Quot.sound]`.
- Commit on `seat/impose` by named paths, each item as it builds. Never push. Never `2>/dev/null`.

## The receipt

`docs/research/2026-10-13-seat-impose-receipt.md` (force-added): the one thing to know before
merging, base and head, changed files, commands and results, axiom output, each landed theorem's
placement, open obligations, and whether any evidence is bounded.
