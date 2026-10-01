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
