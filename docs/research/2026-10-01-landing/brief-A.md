# Seat A brief: values in the checker's order, the signature as a parameter, inhabitance

Written 2026-10-01 by the coordinator. Base: `bb269fde` on `refactor/phase1-phase3`. Worktree
`/Users/pooks/Dev/lean4-effect4-seat-A`, branch `seat/A` (created; `.lake` current). Read
`docs/research/2026-10-01-landing/plan.md` (§0 items 1, §1 O1, §2, §4) and decisions rows 96,
111–116, 127, 132, 137 (`docs/core/decisions.md` in the main checkout) first. The pass's types
seat is `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/types/` (`note.md`
TY-01…TY-23 and §8; `verify.md` §1–§3; the probes `M5CounterProbe.lean`, `TypesOrderProbe.lean`,
`InhabitedProbe.lean`, `verify-AmendedFitsProbe.lean`, `verify-CapstoneProbe.lean`,
`verify-HandleInhabitedProbe.lean`); the model probe's Σ_app material is
`docs/research/2026-09-30-model-probe/` (`synthesis.md` §2.2, §6 D1–D6; `TREE/R2Probe.lean`;
`pedigree/`), and Codex's audit `docs/research/2026-09-30-codex-review-model-probe/audit.md` §2–§4.
Never edit or build outside your worktree.

**The one thing.** M5 is false today because `Fits` compares a declared type in the raw order
while the checker compares and joins in the normalized order (TY-01, proved; `E4-TYPED-CE-009`).
You land row 137's repair in `Laws/Program/Typed/Membership.lean`, the one module that cases on
`Ty` (row 132), together with shape A of the service table (row 112) and the Σ_app definitions
(rows 111–116), and the inhabitance check (row 127), because all of them edit that module or
`Program/Admission.lean`. Every statement you change is a judgment or an admission rule; no
runtime behaviour changes. Seat B owns `Residual.lean`, `Contracts.lean`, `Stack.lean`,
`Frames.lean`; seat C owns `Assembly.lean`, `Sources.lean`, `Scheduler.lean`, `State.lean`,
`TypedStateDecl.lean`: do not edit those. If a change you need lives there, write the exact lines
in your receipt under "for seat B" or "for seat C" and keep going with a local stand-in in a test.

## The work, in order

1. **Re-establish the counterexample on this tree.** Port `types/M5CounterProbe.lean` and
   `verify-CapstoneProbe.lean` to a battery `Test/Counterexamples/Machine/Semantics/FitsOrder.lean`
   (imported from `Test/All.lean` beside `ValueMembership`), restated against the merged typed
   state (`rerun-on-0c534f06/README.md` says which last steps need restating). Its theorems:
   `m5_false`, `typedState_load_false`, `capstone_false`, the three red controls on `Fits`
   (`not_fits_fiber_normal`, `not_fits_cell_raw`, `not_fits_join`). Commit it red (the
   refutations are of the old judgment and stay as historical controls under local copies of
   the old arms once step 2 lands, as `ValueMembership.lean` keeps its retired judgments).
2. **Row 137 (a).** In `Membership.lean`: name the checker's order once (`Ty.subN a b :=
   sub (normalize a) (normalize b)` lives in `Laws/Program/TypeAlgebra.lean` with `subN_refl`,
   `subN_trans`, `sub_le_subN`, `subN_equiv_iff` from `TypesOrderProbe.lean` if it does not exist;
   `verify.md` TY-17 says `subN_refl`'s axioms were not printed, print them); the handle arms
   `FiberDeclared`, `RefDeclared`/`Equiv`, `PromiseDeclared` compare in `subN`; then prove
   `fits_normalize`, `fits_subN`, `fits_join_left`, `fits_join_right` (the verifier proved them on
   a faithful copy, `verify-AmendedFitsProbe.lean`: `fitsN_normalize`, `fitsN_subN`,
   `fitsN_join_left/right`, `amended_join_holds`); re-prove `fits_mono`, `fits_sub`, `fits_map`
   and every lemma of the module that the change touches (list them). Keep `HandleFits`,
   `ServicesFit`, `Live`, `CauseFits` unchanged. Every dependent that breaks (`Laws` and `Test`)
   is repaired in the smallest way and listed; a dependent in seat B's or C's files is listed for
   them with the exact fix (expect `Residual.lean`'s `asyncPre` deferred arm, `fiberPre`'s
   `awaitAll`/`raceAll`, the completion entries: they are seat B's).
3. **The positive M5 control.** The TY-01 program loads into a typed state under the amendment:
   `typedStateF_load` (`ValueMembership.lean:984`) reduces M5 to "the loaded code is typed at every
   world"; build the `TypedProg` derivation for `prog3` (the verifier left it owed) in
   `FitsOrder.lean` as `prog3_loads_typed`. If a seat-B file blocks it, land the derivation as far
   as the leaf and record the exact missing lemma.
4. **TY-07 `evalTerm_fits`** in `Laws/Program/Typed.lean` (beside `evalTerm_hasTy`,
   `:971-1015`): `termTy sig env t = some ty → EnvTyped w env vals → evalTerm vals t = some v →
   Fits w v ty`, by the term fold; its `fst`/`snd` case over unions of products answers at
   `Ty.join` through `fits_join_*`. TY-08: derive the coarse `WorldValid.cells` reading from the
   strong one by `fits_hasTy` where it is cheap, else record.
5. **Shape A (row 112) and the Σ_app definitions (rows 111–116)** in a new
   `src/Effect4/Laws/Program/Signature.lean` (imported from `Laws.lean` beside the typed modules)
   and `Membership.lean`: `World.serviceTy` as a static world component fixed by the world order
   (`Laws/Program/Typed/World.lean` is yours for this field and its order lemmas; say what you
   changed); `ServicesFit` reading it; the lookup-agreement premises of `servicesFit_map` and
   `fits_map`; `SigExtends`, `SigProgram Σ p` (the checker's reads: operations in `dom Σ`, looked-up
   keys whose codes have carriers), `LawfulSig Σ := (∀ e ∈ Σ, Local e) ∧ Σ.Pairwise Compatible`
   with the clauses of rows 97, 113, 114 and 127 and `admitSig_ok_iff`; `π` for services; the
   monotone family of `R2Probe.lean` moved into `Laws` with C3's reflection by one generic
   `cata_congr_on` for generated folds (TY-04) rather than a hand induction; `typedProg_rows_append`
   with row 116's domain bit beside the red control `typedProg_not_table_monotone` (TY-12). The
   lawfulness evidence travels on `ProgramSource` (row 114): add the field and thread it; if
   `Assembly.lean`'s `typedState_load`/`typedState_reachable` must take it, write the exact
   statement for seat C. Red controls kept as fixtures: `prepend_not_extends`,
   `shadow_not_extends`, `one_code_two_carriers`.
6. **`Program/Admission.lean`** (rows 114, 127; TY-05, TY-03, TY-13): `Table.lawful t = false →
   Table.checkLawful t ≠ none`, and delete the invented key at `:169`; `inhabited : Ty → Bool` as a
   `TyAlgebra` instance (`InhabitedProbe.lean`'s fold), its agreement theorems (sound against
   `Fits` and `Val.hasTy`; complete on the data fragment; the three handle witnesses;
   `handle_inhabited` from `verify-HandleInhabitedProbe.lean`; `inhabited_sub`; one world for
   several handles by fresh keys; `inhabited (normalize t) = inhabited t`), and `admitColumn` at
   every answer, error, request and table column with its own located reason, distinct from the
   `int` scan's (`intType at` for DB-15's scan, `uninhabited at` for DI-67's check; the frozen
   `foundation-wave2.contract.md:217-219` and DI-67's text then need one line each: propose them).
   The register row `E4-TYPED-CE-015` (seat F writes it) is repaired by this step: name the
   theorem that refuses `prod never nat` and `except never never` in the receipt.
7. **Texts in your files**: `Laws/Program/Template.lean:332-333` (the kernel does reduce
   well-founded `Ty.sub` under `decide +kernel`; TY-15); DI-15's identity sentence is the
   coordinator's (propose: "identity is equality of normal forms, the kernel of `subN`").

## Checks

Per step: `LEAN_NUM_THREADS=4 lake build Effect4.Laws.Program.Typed.Membership` and its direct
dependents (`lake build` the modules that import it; `grep -rl "Typed.Membership" src Test`
lists them), the batteries by `lake env lean -DwarningAsError=true`; `#print axioms` for every
theorem landed; the environment census for row 132 (`organization/probes/TyCasesInTyped.lean`
shows how: person-written `Ty` cases only in `Membership`) rerun at the end and its output in the
receipt. At the end: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` once; `make check-cases`
if you added a match on a policy family. No generator.

## Receipt

`docs/research/2026-10-01-landing/receipt-A.md` in your worktree (force-added): the one thing
first; base and head; every changed path; per step the theorems (name, file:line, axioms), the
statements changed with old and new text, the dependents repaired; the lines for seats B and C
and for the coordinator's files (rows 96, 111–116, 127, 137; DI-15; DI-67; the contract line);
what is owed and why.
