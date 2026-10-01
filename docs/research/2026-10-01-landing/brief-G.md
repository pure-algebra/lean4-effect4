# Seat G brief: row 150 (`FoldLift`) and three small fixes beside it

Written 2026-10-01 by the coordinator. Base: `refactor/phase1-phase3` at `7c881ecc` (seats C and
I merged; main green, 734 jobs, both gates). Worktree `/Users/pooks/Dev/lean4-effect4-seat-G`,
branch `seat/G`; `.lake` cloned from the main checkout, current at the base. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure) and receipt F's item 3
(`receipt-F.md:192-273`) in full; the probe `seat-F/probes/FoldLiftRoute.lean` (428 lines, log
`seat-F/logs/fold-lift-route.log`) is the proved repair, written against `dceae006` plus seat F.
Files you own: `src/Effect4/Laws/Machine/Lift.lean` (the Decision section, `:264-604`),
`src/Effect4/Laws/Program/Guard/Single.lean`, `src/Effect4/Laws/Program/Guard/OuterDriver.lean`,
`src/Effect4/Laws/Auto/Exhaustive.lean`, `Test/Schema/SubAlphabetContract.lean`,
`src/Effect4/Schema/Bridge.lean`, `src/Effect4/Schema/OfShape.lean`, the batteries under `Test/`
a change of yours breaks, `Test/All.lean` at the anchor named below, and your receipt. Seat I2 runs
in parallel on the typed-state cone (`Laws/Program/Typed/**`, `Laws/Program/Signature.lean`,
`Program/Admission.lean`, the generated runner group): never touch those files, and never run a
generator.

**The one thing.** Row 150 is ruled (coordinator, 2026-10-01, the row is the coordinator's): land
`FoldLift` by receipt F's recipe so that the six fold-level hand inductions disappear, with every
`DecisionLift` statement the tree has kept under its present name as a one-line corollary. No
caller changes: `Laws/Program/Typed/Assembly.lean` and `M6Capstone.lean` read `DecisionLift`, and
seat I2 is editing them now.

## The work, in order

1. **`FoldLift`** (`Lift.lean`, Decision section): the structure of the eight premises the fold
   lifts read (`step`, `nil`, `drain`, `ran`, `task`, `skip`, `clockNone`, `clockSome`);
   `ofDecisionLift : DecisionLift … → FoldLift …`; `driveState_one`. `loop_lift`, `loop_entry`,
   `fireFold_lift` (`:484`), `fireState_lift` (`:512`), `flushAllState_lift` (`:522`),
   `advanceState_lift` (`:539`) proved over `FoldLift` with the probe's bodies, and their
   `DecisionLift` forms kept under their present names as one-line corollaries through
   `ofDecisionLift`, statements byte-identical (check each present consumer still elaborates:
   `git grep -l 'fireFold_lift\|fireState_lift\|flushAllState_lift\|advanceState_lift\|loop_lift\|loop_entry'`).
   Narrow build: `Lift.lean` and its direct importers.
2. **The six inductions.** `held_foldLift` in `Single.lean` (from the lemmas the file already
   uses) and `preserved_foldLift` in `OuterDriver.lean` (its `step` from the `DriverContract` at
   fuel 1 through `driveState_one`); then `held_fireFold` (`Single.lean:225`),
   `held_flushAllState` (`:266`), `held_advanceState` (`:347`), `fireFold_preserved`
   (`OuterDriver.lean:95`), `flushAllState_preserved` (`:167`) and `advanceState_preserved` by the
   probe's three-line proofs, statements unchanged (`#print` each before and after and say so).
   `#print axioms` on all six and the two instances. The red control
   `seat-F/probes/HeldInterruptRefuted.lean` (`held_parked`, `edit_unparks`,
   `interrupt_field_false`: `DecisionLift` cannot carry `Held`) lands as a battery
   `Test/Program/GuardFoldLift.lean`, reachable from `Test/All.lean` at the anchor after
   `Test.Program.H2PartOne`, so the reason for `FoldLift` is a checked fact in the tree beside the
   six rederived statements.
3. **`Exhaustive.lean`** (`Laws/Auto/Exhaustive.lean`, the rows' `holder : Name`): a private holder
   prints by its written name, not the `_private.…` mangled form. Find the real API in Lean core
   (look at it, do not guess: the private-name helpers on `Lean.Name` and the environment), apply
   it where the holder is printed, and show one `#guard_msgs` fixture with a private declaration in
   the family's module set (extend `Test/Audit/ExhaustiveFixture.lean` if it has one, else the
   smallest new one beside it).
4. **`Test/Schema/SubAlphabetContract.lean:96-100`**: the comment names a snapshot compared by no
   check (ORG-24). Rewrite the sentence to what is true now: the census listings pin the order by
   `decide`; the baseline directory (`AGENTS.md`, the `Test/fixtures/baseline` row) is read by the
   mirror census only. Reading only; `lake env lean -DwarningAsError=true` of the file.
5. **Row 8's two remaining items, measured.** (i) `Schema/Bridge.lean:214`: `effDocument` keys a
   requirement on half a `ServiceKey` (`service_{k.name.value}`); key by name and service as the
   row says (read the row and `ServiceKey` for the carrier's own spelling), threading the signature
   only if the key needs it. (ii) `Schema/OfShape.lean:128`: `document` maps `defs` with no dedupe;
   dedupe by key and refuse a repeated key with different bodies as a located refusal (a path and a
   reason), never a silent drop. Each if a few lines with its battery (`Test/Schema/**`; a golden
   that changes is regenerated only by the command that owns it, named in the receipt); else
   measure and report the obstacle. Plan §4's stop rule.
6. **Final:** `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green with both gates; the
   twelve slack ceilings of receipt F's M3 still `0 open … ceiling 0`; `#print axioms` for every
   theorem added or re-proved.

## Rules

Plan §4: no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern`, `implemented_by`;
no `simp_all`, `first | …`, `try` under `src/`; hand `simp` as `simp only [...]`; the trust
ceiling `[propext, Quot.sound]`; no case analysis on `Ty` outside `Membership.lean`; aesop with the
named banks; statements kept, proofs restated; commits by explicit paths on `seat/G`, one per step,
after its narrow build; research files force-added; no push; no generator; one lake at a time in
this worktree (`LEAN_NUM_THREADS=4`; seat I2 has the other cores); the coordinator's files
(`docs/core/decisions.md`, `docs/STATE.md`, `README.md`, `AGENTS.md`, `docs/core/system-map.md`,
`Test/Counterexamples/REGISTER.md`, `lakefile.toml`) are never yours: propose lines in the receipt.
Never `git merge`, `git checkout`, `git reset`, `git push`; a refused permission is recorded, not
worked around. Evidence words: proved, reproduced, tested, assumed.

## Receipt

`docs/research/2026-10-01-landing/receipt-G.md` (force-added, committed last): the one thing
first; base and head; every changed path; per step the statements and proofs touched (name,
file:line, axioms); which repeated proofs disappeared (plan §5 item 1: the six inductions, by
name); the commands and their results; what is owed with the exact obstacle; the proposed lines
for rows 150 and 8 and, if a control was added, the register.
