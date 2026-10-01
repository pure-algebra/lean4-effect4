# Item E: four-module cutover candidates

These are review and installation candidates, not active source changes. The coordinator owns
installation and serialized compilation. No Lean, Lake, generator, or Git command was run by
this seat while preparing them. `source-manifest.json` records the exact current source and
candidate SHA-256 hashes; the four `.diff` files compare those bytes directly.

## Scope

- `Admission.lean` imports `Typed.Membership` in place of `Typed.Validity`, retires
  `HandlesLive`, `HandlesFit`, `ServicesOk`, `StrongValue`, `StrongCause`, and `StrongExit`,
  and uses the `cleanExit` moved to Membership. No aliases or unused bridges remain.
- All four modules use `Fits w v ty`, `FitsExit w ty ex`, `FitsCause w errTy cause`, and
  `ServicesFit w services` where the old judgments occurred. `ValueOk` is not replaced.
- Existing lowercase theorem entry points remain: `strongExit_success`,
  `strongExit_of_clean`, `cleanExit_of_never`, `strongValue_bool_true`, `strongExit_bool`,
  and `strongExit_failure_of_error`.
- Current item B definitions are retained exactly: `NoHostAnswer`, `RReachable`,
  `AnswerOk`, `QueueOk`, and `StepPreserves`. The Assembly candidate changes judgments
  mechanically and changes no proof body. There are no new M5–M7 proofs.

## Proof-body accounting

The eight prescribed edits from `membership/walk.diff` are:

1. Admission `strongExit_success`: return the answer membership directly.
2. Admission `strongExit_of_clean`: establish membership of the failure reasons.
3. Admission `cleanExit_of_never`: invert failure membership at the `never` column.
4. Residual `strongValue_bool_true`: direct boolean membership.
5. Residual `strongExit_bool`: return the answer membership directly.
6. Residual `settling_fork`: use the allocated fiber's declared type directly.
7. Stack `strongExit_failure_of_error`: rewrite the error column.
8. Stack `popR_typed`: pass successful membership directly at the iterator and loop sites.

The only proof bodies added outside those eight are these checked-adapter candidates in
`Effect4.Program.Typed` (outside the obligation namespace):

- `strongValue_mono (w w' : World) (ty : Ty) (v : Val)` calls `fits_mono`.
- `strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV)` calls `fitsExit_mono`.

Their complete binder order matches the preserved `M3bWorld` obligation statements. The
candidate connects both with `#obligation_proved`, adds `#obligation_audit M3bWorld`, and
lowers that namespace's ceiling from 3 to 1. `M3bWorld.typedProg_mono` remains wanted.
No existing proof body outside the eight was changed, apart from the mechanical replacement
of the local `StrongExit` type annotation inside `popR_typed`.

## Verification performed here

Static assertions verified source hashes still match the captured originals; no retired
judgment identifier or forbidden trust/proof form remains in the candidates; the B and pending
H definitions above are byte-identical; M3bWorld retains exactly its intended open goal; and
the M6 ceiling remains 20. All four diffs were inspected. Compilation and axiom output are
pending the coordinator's serialized installation.

## Installation checks for the coordinator

Build `Effect4.Laws.Program.Typed.Membership`, `Admission`, `Residual`, `Stack`, and `Assembly`
in dependency order, then their current direct dependents and the migrating tests. In
particular, expect the M3bWorld audit to report two paired laws, zero mismatches, and the
obligation ledger to report one open and two proved. Print axioms of the eight repaired
proofs and both adapters (allowed trust: `[propext, Quot.sound]`; subsets are fine).

The Assembly capstone docstring still names pre-repair counterexamples CE-PROV-005,
CE-PROV-006, and CE-TYPED-004 because its current B wording was preserved. The coordinator
should update this historical-status sentence after F/G/E verification; retain CE-SCHED-016
and the H2 disclaimer until those separate repairs are justified. World.lean and
ForkSource.lean also have old `HandlesFit` vocabulary in comments, outside this seat's scope.
