# Seat I2 brief: integrate seat A (values in the checker's order, the signature as data, inhabitance) on top of seat I's result

Written 2026-10-01 by the coordinator. Base: the head of `seat/I` once its receipt is in (seat C's
split reconciled with seats B, E and F; the coordinator names the commit at dispatch), merged
with `seat/A` (head `c3f3df14`, base `bb269fde`) as a textual merge by the coordinator (no
conflicts by `git merge-tree` against both main and `seat/I`). Worktree
`/Users/pooks/Dev/lean4-effect4-seat-I2`, branch `seat/I2`. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then in full: `receipt-A.md`
("Integration", "For seat B", "For seat C", "Decisions for the coordinator"), `receipt-I.md`
(what seat I changed in B's and C's files), and `receipt-C.md` ("Lines for seat A"). All are in
this worktree under `docs/research/2026-10-01-landing/`. Never edit or build outside this
worktree.

**The one thing.** Seat A landed row 137 (`Fits` and the completion lookups in the checker's
order), the Σ_app definitions (rows 111–116), term soundness (`evalTerm_fits`) and inhabitance at
admission (rows 127, 149), green on its own base; its receipt names, by reading, every hunk the
union with seats B and C needs and the one decision the brief's "no generator" rule held back.
You make those hunks, tie the world's service table to the source (row 112), make the joint
switch to the source's signature, wire the emptiness refusal into runner admission with the
generated group regenerated in the fixed order, and end with `LEAN_NUM_THREADS=6 lake build
Effect4.Laws Test.All` green with both gates, the producer chain byte-identical except for the
regenerated runner group, and `dune build` plus `make check-ocaml` green.

## The work, in order

1. **Receipt A's integration hunks 1–9** (its "Integration" section): delete seat B's duplicate
   `completionOk_of_fitsExit` (`Adequacy.lean`; A's at any requirement stays); one home for the
   value facts (delete B's `fits_nat_val`/`fits_unit_val`, uses renamed to `fits_nat_inv`/
   `fits_unit_inv`); `fits_sub` → `fits_subN` at the three `Adequacy.lean` sites; `, rfl` for the
   world order's new conjunct at the five constructions; `servicesFit_map`'s lookup premise
   (`serviceTy_of_le ord.1`) at `Residual.lean`'s `fiberPre_mono`; `Residual.lean`'s
   `deferredCompleteWith` reference arm in `subN`; `FitsOrder.lean`'s local `fiber_inv` replaced by
   `TypedProg.fiber_inv`; the batteries that case-split B's definitions rebuilt; the `Ty.sub_refl`
   sites untouched. Seat I may have moved some of these lines: find each by its text.
2. **Seat A's statements over seat C's split** (receipt A, the list after hunk 9; receipt C "Lines
   for seat A" item 4; receipt C "For seat C" item 6): restate `ValueMembership.typedStateF_load`
   and its instances, `FitsOrder.lean`'s `m5_forces_leaf`, `prog3_loads_typed`, `prog3_leaf`,
   `capstone_implies_load` and the historical `Reviewed.*` over `TypedState root rootTy w m`
   (no queue) and `J = MachineTyped`; the positive control `prog3_loads_typed` gives `J` at load
   through `machineTyped_load`; move M5's reduction lemma beside `typedState_load` in
   `Assembly.lean` restated for the split (receipt C's wording: `closed`, `noMarker`, `code` give
   `∃ w, TypedState root ty w (loadR …)`), the battery keeping a one-line use.
3. **Seat C's sites in one spelling** (receipt A "For seat C" item 1): `Assembly.lean`'s
   `CompletionStrong.ofRefGet` and `Scheduler.lean`'s `FiberColumnsBelow`, `RacePayload.live`,
   `RacePayload.programs` compare by `Ty.subN` (A's name), not the inline form.
4. **Row 112's tie (receipt A D-A3; receipt C "Lines for seat A" item 2):** `w.serviceTy =
   root.sig.serviceTy` as a conjunct of `MachineTyped` (beside `WorldValid`), `initialWorld`
   setting `serviceTy := root.sig.serviceTy` (the default for `services = []` by
   `SigApp.serviceTy_nil`, so every source in the tree is unchanged); `ServicesFit` reads
   `w.serviceTy`; `LawfulSource`'s body becomes A's evidence field on `ProgramSource` (rows 111,
   114); the statements keep the premise's name.
5. **The joint switch to the source's signature** (receipt A "For seat C" items 3 and 4), one
   commit: `PointTyped` (`Typed/Admission.lean`), `CaptureTyped` (`Assembly.lean`), `storePre`'s
   `memoGet` and `asyncPre`'s external arm (`Residual.lean`) read `src.signature` for
   `nativeSignature src.table`; the ledger's M5 and M6 premise reads `typeOfProgram
   root.signature root.program = some rootTy` (equal to the old premise for every source with no
   declarations, `SigApp.signature_nil`); `capture_lookup` re-proved.
6. **Row 116's domain bit** (receipt A "For seat B" item 1): `asyncPre`'s external arm takes
   `bitEntry` (`(nativeSignature root.table).dom op = true ∧` the row's columns below the
   certificate); the tripwire `asyncRowOnly_now` is replaced, `AsyncEntryRows` proved from
   `bitEntry_rows_append`, `typedProg_rows_append` holds outright and moves beside
   `typedProg_mono` in `Residual.lean`.
7. **D-A1, ruled (a): runner admission refuses an empty column.** Apply receipt A's hunk to
   `Program/Admission.lean` (`AdmitRefusal.emptyColumn`, `AdmittedProgram.columnsTable` and
   `columnsType`, the last arm of `admitProgram`), repair its dependents (`admitProgram_eq_ok`,
   `admitProgram_certificate`, `admitted_unique`, the hand-built certificates in
   `Test/Run/RunContract.lean` and `Test/Api/HostSessionContract.lean`, the module docstring's
   list of admission requirements), then regenerate in the fixed order, serially, with
   `LEAN_NUM_THREADS=1`: `make gen-derived`, `make gen-lcnf`, `make gen-eff`, `make gen-wire`,
   `make gen-cas`; every generated difference is committed as the producer wrote it (never
   hand-edited) and listed in the receipt; the tripwire in `Test/Program/AdmissionColumns.lean` is
   deleted and the refusal `#guard`s added; then `opam exec --switch=effect4 -- dune build` in
   `ocaml/` and `make check-ocaml` at the root; `make check-cases` if a match on a policy family
   was added (`AdmitRefusal` is not one; say so if you confirm it).
8. **Optional, if a few lines each:** close the six `f.total` ref rows of `M3bAdequacy` with
   `fits_nat_irrel` (receipt B's `cases f` lemma on `FnName.total`/`partialUpdate` and
   `poke_world`); TY-08's promise half (receipt A "For seat C" item 5). Else record as owed.
9. **Then** `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All`: green, both gates; the ledger
   reports per scope; the row-132 census rerun (seat A's command, in its receipt); `#print axioms`
   for every theorem you added or re-proved.

## Rules

Plan §4 (no `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`, `extern`, `implemented_by`; no
`simp_all`, `first | …`, `try` under `src/`; hand `simp` as `simp only [...]`; the trust ceiling;
no case analysis on `Ty` outside `Membership.lean`; statements kept, proofs restated; red controls
red against their historical definitions, flipped controls positive; commits by explicit paths on
`seat/I2`, one per step, after its narrow build; research files force-added; no push; the
coordinator's files are not yours: propose lines in the receipt). One compiler at a time in this
worktree; generators only in step 7 and only in the fixed order.

## Receipt

`docs/research/2026-10-01-landing/receipt-I2.md` (force-added): the one thing first; base and
head; every changed path; per step the statements and proofs touched (name, file:line, axioms),
the generated files changed and the producer commands with their exit codes; the ledger before
and after; the census; what is owed, with the exact obstacle for anything left; the lines for the
coordinator's files (register cells for `E4-TYPED-CE-006`, `-009`, `-015`; rows 96, 111–116, 127,
137, 149 as receipt A proposes, checked against what you landed).

## Amendments (2026-10-01, after seat I's receipt and Codex's second-eyes review)

Dated additions. Where they differ from the text above, they win.

- **Base named.** `seat/I` head `160012dc` (receipt-I, merged to main as `38686e44`); `seat/A`
  merged by the coordinator as the first commit of `seat/I2`, `a6ec2a28` (no conflicts; `.lake`
  cloned from seat I's worktree, current at its head). This brief and Codex's evidence live in the
  main checkout, `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-landing/` (`brief-I2.md`,
  `codex-second-eyes/`): read them there; edit and build only in this worktree.
- **Step 10 (after step 9's green build): decisions row 156, scope presence as one predicate.**
  Two checked refutations stand after row 139's consumer premises landed. Seat I's: the
  `TypedProg.scopeExit` constructor reads no pre, so `M6Ledger.step_deliver` stays refuted by
  `M6Capstone.H1HaltAmendment.step_deliver_refuted_by_absent_scope` (receipt-I "What is owed",
  with the measured repair). Codex's (`codex-second-eyes/review.md`, `ScopeAllocationPost.lean`,
  `scope-allocation-post.log`; nine theorems at `[propext, Quot.sound]`, five guards, at
  `509d243c`): the five posts that answer a scope handle (`storePost`'s `scopeMake`
  `Residual.lean:90`, `scopeFork` `:97`, `memoBuild` `:101`, `memoRelease` `:104`; `fiberPost`'s
  `ambientScope` `:191`) say only `∃ sc, ans = scopeHandle sc`, so the continuation of an
  allocation must be typed at an absent scope; the checked source `forkAfterMake` (make a
  sequential scope, fork a unit child into it; the checker accepts it at
  `pure (fiberOf unit never)`, the run answers `fiber 1` at fuel 40) has no `TypedProg`
  derivation at any world where scope 0 is absent (`forkAfterMake_denotation_refused`), which
  refutes the exact `DenotesTyped` proposition (`m5_denotation_shape_false`); `makeThenClose_refused`
  is the same without fork machinery; `absent_scope_still_fits` shows membership at `Ty.scope`
  ignores presence (seat A's `HandleFits` scope arm, `Membership.lean:64`, checks the target name
  only, where the external arm checks allocation). Land, in this order, each with its narrow
  build and its own commit:
  1. `ScopeLive (w : World) (sc : Nat) : Prop := (w.state.scopes.entryAt sc).isSome = true`
     once, in `World.lean` beside the world order, with `scopeLive_mono` along the order's
     scope-persistence component (receipt-I names it `ord.1.1.2.2.2.1`). Every site below reads
     it by name; no second spelling of the fact.
  2. `HandleFits`'s scope arm: `target = Ty.scopeTarget ∧ ScopeLive w index`, as the cell,
     promise and external arms read their stores (row 139's clause); `handleFits_map` gains the
     transport. Then `MachineLive.ambientScopes` (`Assembly.lean:251`) is derived from the
     context's membership if that is a few lines, else kept with its docstring naming the
     derivation as owed.
  3. The five posts carry presence at the answer world: as `Fits w' ans Ty.scope` if membership
     now owns the shape (one owner), else `∃ sc, ans = scopeHandle sc ∧ ScopeLive w' sc`;
     `memoRelease` on its scope-handle disjunct. Re-prove the adequacy instances from the actual
     operation (`Adequacy.lean`: `scopeMake_implements` `:662`, `scopeFork_implements` `:684`,
     the memo instances, `ambientScope_answers` `:973` from `MachineLive.ambientScopes` through
     `J`): the step installs the entry (Codex's `#guard`s on `syncOpStep`).
  4. `fiberPre`'s arms (`Residual.lean:144`, `interruptAs`, `runIn`, `scopeExit`, `closeScope`,
     `forkIn`) read `ScopeLive` by name; no change of content.
  5. The `scopeExit` constructor takes `live : ScopeLive w sc` (receipt-I's measured hunk: the
     constructor, `fiber_inv`'s pattern, `typedProg_mono`'s arm, seat E's `Seq.close_typed`,
     seat C's `RawOrderLoad.fiber_inv`). In `M6Capstone.H1HaltAmendment`, `callback_typed`
     takes the premise; the eight controls that fall (`worker_saved`, `typed`, `old_typed`,
     `typedState_input`, `config_input`, `step_deliver_false`, `deliver_preserves_this_state`,
     `step_deliver_refuted_by_absent_scope`) stay as history over one local copy of the judgment
     without the premise and of H1's and the split's states over it (named `Old…`, as `AwaitLoad`
     does); `input_refused (w) : ¬ ConfigTyped rootProgram unitTy w machine commands` replaces
     the red control, proved. `M6Ledger.step_deliver`'s docstring and `MachineLive`'s drop the
     refutation; the ledger line stays open.
  6. The battery `Test/Counterexamples/Machine/Semantics/ScopePresence.lean`, reachable from
     `Test/All.lean` at the anchor: Codex's probe as history (its refutations over local copies
     of the old post and the old membership, or pinned failing by `#guard_msgs (error)` against
     the current judgment, as `AwaitLoad` pins seat C's script) beside the positive controls:
     `forkAfterMake` and `makeThenClose` typed as `TypedProg` derivations at Codex's
     `startingWorld` and through the `DenotesTyped` shape at `point` (the exact proposition of
     `Assembly.lean`'s `DenotesTyped`), the kernel-checked checker certificate and the runtime
     `#guard`s kept. `E4-TYPED-CE-018` becomes REPAIRED by it (propose the cell).
  7. `LEAN_NUM_THREADS=6 lake build Effect4.Laws Test.All` green with both gates; the ledger per
     scope; `#print axioms` for every theorem added or re-proved; the admission census unchanged.
  Plan §4's stop rule holds: a repair past a few lines outside this list stops with a measured
  report. If step 9's receipt is due before step 10 is reached, write it, continue step 10 in the
  same worktree, and update the receipt in place ("After the amendment").
- **Receipt additions:** the lines for rows 139 and 156, `E4-TYPED-CE-018` and
  `E4-SCHED-CE-020`; what `step_deliver`'s ledger line reads after the constructor change (open
  and no longer refuted by that witness, or the exact obstacle).
