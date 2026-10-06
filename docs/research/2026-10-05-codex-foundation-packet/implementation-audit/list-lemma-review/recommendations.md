# Shared list facts and cleanup review

Reviewed main: `0dbb17c3` on `refactor/phase1-phase3`.
Evidence: current source, installed Lean 4.33.1 source, retained receipts and an isolated Python reproduction.
No new Lean build or repository edit occurs in this review.

## Recommended cleanup

The attachment identifies a useful boundary problem.
Five general list facts live under `Effect4.Program.Ty` in `src/Effect4/Laws/Program/Template.lean`.
They concern lists rather than types.

Move these declarations to `Effect4.Constructive.List` in the existing `src/Effect4/Data/Constructive.lean`:

- `flatMap_congr`
- `mem_zip_map_self`
- `mem_zip_middle`
- `eq_of_mem_zip_map`
- `lookup_of_mem_nodup`

Keep their current propositions, hypotheses, proofs and universes during relocation.
Update the eight calls in Template.
Retain a forwarding name only if a checked consumer requires it.
Do not move all 49 helpers or introduce a new utility hierarchy.
Lean supplies useful building blocks, but no exact replacement was found for these five propositions.
The existing shared module already owns constructive list facts and sits below the program and law layers.

One immediate consumer can remove another induction.
`Typed.mem_zip_self` in `Laws/Program/Typed/Membership.lean` follows from the shared `mem_zip_map_self` at the identity function.
Its statement and four callers can stay unchanged.
This proposed shorter proof still needs Lean and axiom checks.

## Fold duplication

Two declarations have the same proposition, including refusal for an out-of-range index:

- private `lookup_weaken` in `Program/Typing/Rules.lean`;
- `getElem?_weaken` in `Laws/Program/Typed/ListFold.lean`.

Expose the existing core helper, using Fold's explicit list proof.
Make `evalTerm_weaken` use it, then remove the duplicate proof.
Both consumers already reach `Program/Typing/Rules.lean`.
Do not move this theorem into `Data.Constructive`: it mentions `Program.Var.weaken`.
Do not make core typing import Laws.

## Placement and acceptance

The five Template helpers continue to serve `template-match-anchored`, under `subtyping-algebra`, requirement R4.
Its top statement remains `Ty.matchTemplate_complete_anchored`.
The shared weakening fact serves `argTy_weaken` and `evalTerm_weaken`, including `fold-typed-atomic-update`, under `store-typing`, requirement R4.
Neither relocation proves a new runtime or target agreement.
Keep the existing registry claims; no additional planned goal is required for renaming or reuse alone.

After a coordinator-assigned build slot, build the changed modules and their affected direct consumers.
Inspect the relocated helpers' axioms and the existing top statements' dependencies.
Retain the key uniqueness and list alignment premises.
Use the current anchored-template and Fold controls, including refusal, captures and insertion under two binders.
The existing root, axiom and proof-style checks own acceptance; add no new gate.
The shared data module has many dependents, so this cleanup must not delay T5's active work.

## Other attachment items

The status crash is reproduced against the actual `lake_cache` function in `scripts/status.py`.
An absent `elan` raises `FileNotFoundError`; explicit cache configuration and disabled-cache controls pass.
Mocked command-failure and command-success controls exercise the existing fallback and toolchain paths.
Catch the missing executable narrowly and use the documented fallback or an explicit unavailable diagnostic.
Do not hide unrelated I/O failures or convert an unavailable measurement into zero.
The exact probe, Python version and source digest are in `status/receipt.json`.

The larger concerns need an updated reading:

- Fold and LOWER are merged. Their merge records retain checks; this review does not rerun them.
- Queue Q0 is landed at `9abf99b6`, including `acceptLoop_length_le` and an explicit planned `positive_suspend_step_capacity`.
- The Queue goal's main registry join still waits. The library-only report does not load the Test declaration.
- T5 is active on operation-term printing. Its gap remains an assigned implementation task.
- Queue's pure cell steps can follow Q0 and Fold independently of T5 and mask. Two implementation seats remain occupied.
- A single release-only agreement case does not retire U-01. That needs the existing migration contract's source and observation review.
- Cache pruning, worktree deletion and an unrequested full sweep are outside this cleanup.

The UI confirms the Effect4 coordinator, active T5 and active DOGFOOD.
This review proposes a later bounded cleanup; it does not dispatch another seat.
