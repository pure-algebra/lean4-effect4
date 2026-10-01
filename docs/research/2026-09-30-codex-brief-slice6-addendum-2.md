# Addendum 2 to the slice 6 brief: the repairs the owner approved

Written 2026-09-30, after the owner approved decisions rows 96, 104–107 and 110 as recommended.
Read it with the [brief](2026-09-30-codex-brief-slice6-and-fixes.md) and
[addendum 1](2026-09-30-codex-brief-slice6-addendum-1.md); where they differ, the later document
wins. The source is the design pass ([synthesis](2026-09-30-pass/synthesis.md) §6, slices 1–5).
The coordinator checked every file and line below against the tree at `bbdbb7ac`. Your base is
older, but only documents and two comments changed since.

**The one thing first.** These items repair two real typing bugs and the statements M5–M7 will
prove; they do not prove M5–M7, which is the next brief.
- **Order:** D, F, G, E, H, after A–C.
- **Why D first.** It finishes slice 6, whose last item is the trace agreement, and the owner made
  slice 6 the priority.
- **Then the bugs.** F and G fix bugs a user can reach through the live API. They are small and
  independent of D, so if D stalls on proof work, do them and come back.
- **Then the statements.** E then H repair what M5–M7 will prove.

## Item D: the generic lifts and slice 6's last proofs (rows 110 and 93; plan step 6)

After item C, because users 1 and 2 read the ledger.

1. **The lifts, in a new `src/Effect4/Laws/Machine/Lift.lean`.** It imports
   `Laws/Machine/Approximation`, `Laws/Machine/Keeps` and `Laws/Effects/Protocol`.
   - Signatures: `lift/note.md` §4 P1. Proofs: `lift/Lift.lean`, in the pass folder.
   - Declarations: `StepKeeps`, `driveState_lift`, `driveStep_append`, `Guarded`, `DecisionLift`
     (13 fields), `stepDecisionState_lift`, `answer_of_split`, `AdmittedReplay`,
     `replayEval_lift`.
   - The frame law `driveStep_append` is proved in the probe with `first | …`, which `src/`
     forbids. Restate it arm by arm.
   - Keep the probe's `parkedAt_em` pattern: `by_cases` on an existential reaches
     `Classical.choice`.
2. **Beside the guard's reachability.** Add `foldl_lift` and `reachable_lift` beside
   `Guard.Reachable` (`Laws/Program/Guard/Core.lean:31`).
3. **Re-derive the guard's contract.**
   - `driverContract` (`Laws/Program/Guard/Driver.lean:103`) follows from `driverContract_of_lift`.
   - Delete the four hand inductions it replaces: `driveState_invariants`,
     `reservedKeys_driveState`, `interruptedAt_driveState` and `requestOrInterrupted_driveState`
     (`:18-99`).
   - Check by a dependency walk that the re-derived contract does not reach them, as the lift
     verifier did (`lift/verify.md` §5).
4. **The three users, by hand against the ledger** (plan §5):
   - **user 1, the trace agreement.** `step_agrees` and `reachable_agrees`
     (`Laws/Api/TraceOrigin.lean`) through `reachable_agrees_of`; the `M1Trace` ceiling goes from
     2 to 0.
   - **user 2, ledger well-formedness.** The four lookup facts (unique, bounded, corresponding,
     fresh at creation) on every reachable machine.
   - **user 3, memo ids.** `reachable_memoIdsOk` on the native path. Name the reference path as
     not covered unless the same lift is instantiated there.
   - **The four `update` edits.** With the ledger, the four edits of `AgreesUpdates` should hold
     on every machine (lift note P4); restate them against it.
5. **The input to row 94.** For each user, record what proof search closed and what was written by
   hand. Row 94 decides from that whether to build the command that writes these statements.
6. **Then `forkedOf` and `Agrees` move to `Test/`** as the control (plan §6). The laws are
   `M1Trace.*_forked` (`Laws/Api/Supervision.lean:255-544`), with their proof references and
   gate. List each declaration as moved or restated against the ledger. `Test/` depends on the
   library, never the reverse.
7. **No M6 instance.** The probe's `m6_*` theorems wait for E–H and the M5–M7 brief.

**Commits:** the lifts; the guard's re-derivation; each user; the move.

## Item F: a layer is built in the environment it was checked in (row 104; `E4-PROV-CE-005`)

The checker types a layer's body in the empty environment (`LayerHasTy.effect` at `[]`). The
runtime builds the layer at `p.child 0`, which keeps the enclosing environment
(`Program/Compile.lean:79-80`). Variables are absolute positions, so `var 0` names different
values in the two places.

1. **One entry point.** In `provideLayerWithK` (`Program/Compile.lean:767-781`), build at a closed
   point, `{ p.child 0 with env := [] }`, in both branches (`:774`, `:777`); name a helper for it.
   - Every layer build starts there:
     - `effect` and `effectDiscard` (`constructionAt`, `:741-749`, builds at `q.child 0`);
     - `ref` redirects (`Point.redirect`, `:115-116`);
     - `merge`/`mergeAll` sibling builds (`:1453-1455`);
     - `provide` chains.
   - `child` and `redirect` keep the environment, so the closed point carries through to all of
     them.
   - The program body under the layer (`provideLayerBody p`) keeps the enclosing environment.
     Only the layer's build point changes.
2. **The reference machine, in step.** Change `provideLayerR` (`Laws/Program/DenoteR.lean:525`),
   the `provideLayer` arm (`:671-672`) and `denoteR_provideLayer` (`:1049`) the same way, so that
   `run_eq_ref` keeps its shape.
3. **The runtime side of the judgment.** Prove that every layer build starts at a point with an
   empty environment; it matches `LayerHasTy.effect`'s premise `HasTy sig [] body t`.
4. **Repair the laws that unfold these:** `Laws/Program/{DenoteR,Agreement}.lean`,
   `Laws/Program/Handles/{Layer,Hooks}.lean`, `Laws/Program/Intro/{Layer,Memo}.lean` and
   `Laws/Program/Guard/RaceSites.lean` (a grep for `provideLayerWithK` and `constructionAt`).
5. **Counterexample and controls:** `Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean`,
   imported after item A's `HostHandleForgery`. Build it from `registry/LayerGap.lean` and
   `registry/verify-Gaps.lean`, with the repaired expectations:
   - `errLeak` fails with `"x"` on both machines, as its printed TypeScript does under rc.112;
   - `forkLeak`'s child returns its declared type;
   - `discardLeak` follows the checker;
   - `crash1` no longer dies with `badName`;
   - the controls still fit.

   Register `E4-PROV-CE-005` as REPAIRED.
6. **Regenerate.** `provideLayerWithK` and `constructionAt` are in the engine's closure. Then run
   `dune build` and `make check-ocaml`. Run `errLeak` on the OCaml engine, which nobody has done,
   and record its exit.

**One commit.**

## Item G: a layer's value fits its key's type (row 105; `E4-PROV-CE-006`)

1. **The checker.** In `checkLayer` (`Program/Checker.lean:226-236`), the `succeed key value` and
   `effect key body` arms:
   - look up `sig.serviceTy key`, refusing `.serviceUnknown key` as `service` does (`:216`);
   - require `Ty.sub (Lit.ty value).normalize ty.normalize` (for `effect`, `t.answer` in place of
     `Lit.ty value`), refusing `.valueNotSubtype key _ ty` as `provideService` does (`:219-224`);
   - keep `succeed`'s existing literal check first.

   `Lit.ty` is at `Program/Eff.lean:236`. No new refusal constructor is needed.
2. **The judgment.** `LayerHasTy.succeed` and `.effect` (`Laws/Program/Typing/HasTy.lean:414-426`)
   gain the premises `sig.serviceTy key = some ty` and the subtyping. The sentence "the value's
   type plays no part" goes. This amends a frozen judgment, so:
   - write the old and new statements in the receipt;
   - keep the old judgment locally in the counterexample file, refuted there.
3. **The laws.** `checkLayer_sound` (`Laws/Program/Typing/CheckSound.lean:286`),
   `checkLayer_complete` (`:543`), `layerTy_sound` and `layerTy_complete`
   (`Laws/Program/Typing/Sound.lean:87-93`), the uniqueness lemma at `:151`, and what breaks
   downstream.
4. **Counterexample and controls:** `Test/Counterexamples/Machine/Semantics/LayerValue.lean`,
   imported after item B's `M6Capstone`.
   - `valueLeak`, `succeedLeak` and `crash2` are refused by `Api.typeOf` at their paths with
     `valueNotSubtype`.
   - A key with no service type is refused with `serviceUnknown`.
   - `valueControl` still checks.

   Register `E4-PROV-CE-006` as REPAIRED.
5. **The corpus.** No lane program changes (`registry/verify-LaneReach.lean`: 0 candidates). The
   400 random programs do draw layers (`Test/Program/Gen.lean:193-203`), so rerun `make corpus`
   and confirm that `generated/corpus-index.tsv` is unchanged. If a verdict moves, commit it with
   the list of programs. `checkLayer` is not in the engine's closure: no LCNF regeneration.

**One commit.**

## Item E: the membership judgment `Fits` (row 96; D1–D4 ruled)

1. **The new module, `src/Effect4/Laws/Program/Typed/Membership.lean`.** It holds the definitions
   of `membership/note.md` §2, with the rulings:
   - D1: `inv := Equiv`;
   - D2: the native spellings mean handles declared at `nat`;
   - D3: liveness `Live` is read from the world's tables;
   - D4: `unknown` means declared liveness.

   Two more things go in it:
   - **The fold.** Put the `fold_of Effect4.Program.Typed.Fits` line in this module, not in
     `Folds/Ty.lean`, which would make an import cycle (synthesis K13).
   - **The laws that name no old judgment** (`membership/note.md` §6, proofs in
     `membership/Fits.lean`): `fits_hasTy`, `fits_live`, `fits_sub`, `fits_mono`,
     `fitsExit_mono`, `fitsExit_success_iff`, `fitsExit_failure_iff`, `fitsExit_of_clean`,
     `fitsExit_failure_of_error`, `fits_list_iff`, `fits_fst` and `await_fits`.
2. **Bridge laws.** Laws that name the old judgments (`live_iff_handlesLive`, and the equality
   bridge if you keep it) go in `Typed/Admission.lean` or later, which imports the new module.
3. **Not yet: the runtime's twin.** Its checker `fitsAt` and its reflection lemma stay parked
   with the fiber boundary (synthesis K6). Until then, the runtime's check is `Val.hasTy` plus
   item A's handle-free rule.
4. **Cut over the four modules** `Typed/{Admission,Residual,Stack,Assembly}.lean`, following
   `membership/walk.diff`.
   - The renames: `StrongValue` → `Fits`, `StrongExit` → `FitsExit`, `StrongCause` → `FitsCause`,
     `ServicesOk` → `ServicesFit`. `ValueOk` stays.
   - The measured cost is renames plus eight proof edits.
   - Close `M3bWorld.strongValue_mono` and `strongExit_mono` with `fits_mono` and
     `fitsExit_mono`. Their argument order differs, so `#obligation_audit` needs a checked
     adapter. `M3bWorld` should go from ceiling 3 to 1; record it.
5. **Cut over the tests.** About 60 declarations, roughly 20 of them with small proof edits
   (`membership/inventory.log` §1):
   - `Test/Program/{TypedControl,TypedResidual,TypedStack,LoadedAdmission,AdmissionCensus}.lean`;
   - `Test/Counterexamples/Machine/Semantics/{AsyncHookContract,TrivialPosts}.lean`.
6. **Retire the old definitions** once nothing uses them (build beside, move, delete).
7. **Controls:** `Test/Counterexamples/Machine/Semantics/ValueMembership.lean`, imported after
   `LayerValue`.
   - **Green:** `typedStateF_load_ref` and `typedStateF_load_get` (`membership/verify-fits.lean`).
     `Ref.make(5)` and `Ref.make(5).flatMap(Ref.get)` have a typed loaded state.
   - **Red:** `g1`–`g6` and `typedState_load_false` (`membership/Gaps.lean`), against a local
     copy of the old judgment, as item B keeps `ReviewedRReachable`.
8. **Register.**
   - `E4-TYPED-CE-004` is REPAIRED.
   - Add `E4-TYPED-CE-005`, REPAIRED: G1–G6. The old judgment accepts a wrong handle nested in a
     product, a Result, a successful exit, a union branch, a snapshot, or the native cell
     spelling.
   - Add `E4-TYPED-CE-006`, REPAIRED: G7. Exact-spelling invariance breaks subsumption
     (`fitsEq_not_closed_under_sub`).
9. **Proof search.** The `Effect4.TypedState` bank closes the heap-extension goal; its red control
   is in `membership/Fits.lean:1207-1232`.

Laws only, so no regeneration. Build in order: `Membership`, `Admission`, `Residual`, `Stack`,
`Assembly`, then the tests.

**Commits:** the module; the cut-over; the tests; the retirement.

## Item H: the rest of M6's statement (rows 106–107; `E4-SCHED-CE-016`)

After E.

1. **Fresh tokens (row 106).**
   - Generalize the guard's key lists over the code type (`internalKeys`,
     `Laws/Program/Guard/Core.lean:124-130`, and the queue's command keys) so the reference
     machine reuses them.
   - M6's typed state gains the bound: every internal key and every queued resume key lies below
     `nextToken` (`InternalKeysBelowR`, `QueueFresh`). Restate `StepPreserves` to carry both. The
     shapes are `lift/verify.md` §3 R1; they were not compiled.
   - **Where the bound sits.** Put it in `TypedState` or in `WorldValid` (`Typed/Validity.lean:25`
     already bounds the world's declared tokens). Choose the place that keeps `StepPreserves`
     quantified over every pending list that meets the queue fact, and say why in the receipt.
   - **The open question.** Do the tokens in `f.pending` (`preds.PendingOk`,
     `Typed/Assembly.lean:53`) need the bound too? Answer it with a probe or a reading.
2. **The exit clause (row 107).**
   - The exit field of the typed state (`preds.exit`, `Typed/Assembly.lean:54`) refuses the
     defects the lane forbids (`badDefect`, `Test/Program/ExitTypeLane.lean:34-37`): `badName`,
     `notImplemented`, and `missingService` when nothing is required. Name it to fit, e.g.
     `NoShapeDefect ty ex`.
   - Ordinary defects stay admitted (`E4-TYPED-CE-003`). Update that line's repair column: this
     is the separate statement it asked for, and its proof is M6's.
   - Remove the capstone docstring's disclaimer (addendum 1, item B).
3. **Controls,** added to item B's `M6Capstone.lean`.
   - **Early queue.** It fails `QueueFresh`: token 0 is not below `nextToken = 0`
     (`lift/verify-steppreserves.lean`, `lift/verify-decision.lean`).
   - **`typedState_load` at `perform sleep 1`, under `Fits`.** It is a green control, and it makes
     the old refutations unconditional. It needs a `TypedProg` derivation
     (`Typed/Residual.lean:186`) through the sleep row of `Ψ_F` (`:170`).
   - **Exits.** A fiber that exited with `badName` fails the new clause; a clean exit passes.

   Register `E4-SCHED-CE-016` as REPAIRED.
4. **Ledger names.** Restated obligations keep their names; record any ceiling change.

Laws only. **One commit per row.**

## After this addendum

- **The M5–M7 proofs are the next brief:** `typedState_load` in general, the 18 obligations,
  `decision_preserves`, and then the capstone by `m6_capstone_of_steps` over the lifts.
- **Not here:**
  - numbers (row 108, open);
  - FloatLib (row 109, parked);
  - the fiber boundary and the registry (parked).

## Stop rules, beside the brief's §6

- **F:** stop and list any corpus or truth-lane program, other than the gap programs, whose run
  changes.
- **G:** stop and list any in-tree program, other than the gap programs, that is now refused.
- **E:** record every proof change outside the eight `walk.diff` places and the tests. Continue
  while each is local.
- **H:** if the bound cannot be stated without carrying reachability (the alternative row 106
  rejected), stop and record why.

The receipt is the same file, with a section per item.
