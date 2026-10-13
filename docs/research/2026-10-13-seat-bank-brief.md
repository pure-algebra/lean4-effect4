# Seat BANK brief: the slice's banked module and the claim record's two labels (2026-10-13)

Status: brief (history, not authority). Coordinator: the main session. Branch `seat/bank`,
worktree `~/Dev/lean4-effect4-bank`, base `cfcb95e1b` on `refactor/phase1-phase3`. The
packages are cloned; run your first `lake build` through the slot script and the cache restores.

## The one goal

Land the banked module of the vertical slice, as decisions row 378 rules it: (1) the bank unit,
(2)–(5) the transfer law, reference and staleness, (7) one claim record with two labels, and
(18) Ref as the module, "a cache of the list beside storage". Read row 378 in
`docs/core/decisions.md` first; its rulings are the specification.

## What to land, in order

1. **The claim record's two labels** (row 378 (7)), in `Test/Dogfood/Application.lean`:
   - what a claim is about: an implementation (a banked module) or an application;
   - its evidence: theorem, finite check, outside oracle, monitored, validated, assumed.
   `Grade` becomes the evidence label (its `proved` is `theorem`), so a premise's grade and a
   claim's evidence are one type. Keep `Kind` (where an application claim's truth comes from)
   as it is. The record still holds no status: the plan derives it. Update
   `Test/Dogfood/Scenario/Todo/Claims.lean` only where the rename reaches it.
2. **The banked block.** A cache of a list beside storage, written over Ref's native
   operations (`src/Effect4/Library/Ref.lean`, `Program.Authoring.Ref`). Shape it like the
   library's service blocks (`Semaphore.serviceDefs`, `src/Effect4/Library/Semaphore/Defs.lean`):
   an init that makes the cell, and methods (read through the cache, which loads from storage
   on a miss; invalidate on a write). Prefer the loader as a parameter (programs as parameters,
   HO-1) over a fixed host row, so the block names no application. Keep each method `Straight`
   (`src/Effect4/Program/Fragment.lean`) if you can: then `run_eq_meaning`
   (`src/Effect4/Laws/Program/Agreement/Segment.lean`) carries the proof.
3. **Its Lean model** (row 378 (6)): a Lean definition over the cached value and storage's
   answers, beside `Ref.Model` (`src/Effect4/Library/Ref/Model.lean`).
4. **The transfer law** (row 378 (3)): for every decision tape, each observation of the block's
   code (the results and the wake order) is one its model can make. State it about the block
   itself (row 378 (5)). Reuse `ref_steps_agree` (`src/Effect4/Laws/Library/Ref/Operations.lean`)
   and the equal-observation theorems; do not write a pairwise agreement proof. If the proof is
   out of reach, land the statement as a placed `proof_goal` and the proved steps.
5. **The bank entry** (row 378 (1), (4), (5)): one record holding the block, its digest
   (`Canonical.digest`, `src/Effect4/Store/Domain/Canonical.lean`), its interface (operations,
   rows, types), the model's name and the agreement theorem's name. A `#guard` checks the
   recorded digest against the block, so an edit of the block without a new digest fails the
   build. Its claim is a claim record about an implementation, with evidence `theorem`.

## Placement (AGENTS.md, Trust)

Before the transfer law, write its five lines: concept `translation-simulation`
(`docs/core/semantics.md`), requirement R10 (`docs/core/system-map.md`); the question is a new
registry claim (`tools/ProofGraph/Registry.lean`, appended at the end of its list); its reach is
the block's methods on the `Straight` fragment, under any loader answers; it does not establish
any host's storage behaviour or anything about a fiber-sharing schedule.

## Rules

- Reuse first: search the registry, the proof graph and the aesop banks before a new definition.
  The receipt lists what you reused. A duplicate is a defect.
- Two other seats run now. SVC owns `src/Effect4/Program/Authoring/Application.lean`,
  `src/Effect4/Codegen/Checked.lean` and `tools/Tools/Code/Module.lean`. ROWS owns
  `src/Effect4/Codegen/{Templates,PrintLeaf,Read,Print}.lean`, `ts/eff/` and the keyed lane.
  Do not edit those files, `Test/Dogfood/Scenario/Todo.lean`, `lakefile.toml` or
  `docs/core/decisions.md`. Imposing the cache on the to-do is the coordinator's, after SVC lands;
  write in the receipt how the to-do's `list` would impose it.
- Root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) only by
  appending at the end.
- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. Never a bare
  `lake build`, never `lake build Test`. No bun, no npm, no downloads.
- Proofs: aesop and its banks where they close; `simp only [...]`; no `simp_all`, `first`, `try`.
- Audit each touched module with `#axiom_audit` at `[propext, Quot.sound]`.
- Commit on `seat/bank` by named paths, early and often (the coordinator merges as you go).
  Never push. Temp files only in your worktree's `scratch/` or the coordinator's scratchpad.
- Never use `2>/dev/null`.

## The receipt

`docs/research/2026-10-13-seat-bank-receipt.md` (force-added): first the one thing to know before
merging, then base and head, changed files, commands and results, axiom output, each landed
theorem's placement, open obligations, and whether any evidence is bounded. Propose any decisions
row there.
