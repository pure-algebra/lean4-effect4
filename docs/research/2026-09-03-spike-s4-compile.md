# Spike S4: the compile repairs and the general theorem

> **Superseded in part by §9 (S4b), 2026-09-03.** Summary item 7, §4's "exact
> remaining obligation", §5's first bullet and §8's follow-up 3 are stale: the
> `leaveConfig` ruling was taken (repair, not restrict), the compile now resumes
> a region at the *leave*'s configuration, and
> `RegionOracleAgrees.registrations` is proved rather than assumed. §9 is the
> current reading; everything else in this file still holds.

Status: implemented, 2026-09-03. Row S4 of `docs/research/2026-09-03-deep-plan.md`
§2 — packets P1 (one scope per region), P2 (frontier-preserving compile), P3
(`performCatch` as `onSuccessAndFailure`) and P4 (the settled general theorem)
of `docs/research/2026-09-03-deep-flow-to-frames.md`.

Work is in the git worktree
`C:\Users\kokok\Dev\lean4-effect4\.claude\worktrees\agent-a8e6711ea8946c78a`
(branch `worktree-agent-a8e6711ea8946c78a`, based on main `6d83533`, carrying
spike S1's frame-machine changes). **Nothing is committed.** This file is the
only thing written outside the worktree.

## Summary

1. **P1, P2 and P3 are landed and green.** The three compile repairs are in
   `Effect4/Semantics/RegionSimulation.lean`. Every theorem in
   `Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` that read
   `machineAt … ≠ runnerAt …` now reads `machineAt … = runnerAt …`, with the
   fixtures unchanged.
2. **`E4-TARGET-CE-019` closes.** Not by restriction: the `hfin` premise ("no
   release fails") is *discharged*, because `regionInterp.finalizerExit` is
   constantly `Exit.success ()` and the whole close is one `Exit.asVoidAll`
   applied once by the region's scope frame.
3. **The finalisation half of `E4-TARGET-CE-020`/`-021` closes.**
   `compileRegion_not_failure` proves the compile emits `Prim.failure` *nowhere*,
   for every flow, fuel, block, environment and tape; `run_suspend_fixed` and
   `compileAt_zero_fuel_live` prove the machine then stays `FrameStep.running`
   at every machine fuel with an empty trace. The **classification** half (T8)
   is not closed and is stated as a live divergence, as the brief required.
4. **`E4-FLOW-CE-020` is re-read on both halves**: the order half was already
   the runner's; the exit half is now the compile's too.
5. **T5 and T6 are stated in Lean and proved at five flows, not in general.**
   `RegionsSimulate` and `RegionsSimulateExit` are `Prop`-valued definitions
   whose hypothesis is the new structure `RegionOracleAgrees`. They are proved
   at `regionBothSucceed`, `regionNested`, `regionTwoFail`, `regionReleaseFails`
   (the `E4-TARGET-CE-019` fixture) and `regionCatch` (a `performCatch` inside a
   resource-holding region). T6 is against `runRegionsCause`, so it is the whole
   merged failure list.
6. **T7 generalises rather than being reproved**, and gains two members:
   `unwind_to_frame` (the failure-side dual of `close_success`) and
   `region_close_rows`/`region_unwind_rows` (P1 as a general law: one row per
   registration, all against the same exit, for every registration list).
7. **The exact remaining obligation is one clause**:
   `RegionOracleAgrees.registrations`. `closeWalk` is the `leaveConfig` function
   the fence-C note said was owed; the proof that it *is* the runner is not in
   this file. `tapeAfterRegion_diverges` is the minimal witness that it is not
   free, and `unrestricted_finite_agreement_false` is now proved from it rather
   than from a failing release.
8. **No `sorry`, no `Classical.choice`, no frozen surface moved.** `Prim`,
   `PrimInterp`, `FrameEvent`, `test/contracts/frames.contract.md` and every
   census row are untouched.

---

## 1. Files touched

All paths are in the worktree
`C:\Users\kokok\Dev\lean4-effect4\.claude\worktrees\agent-a8e6711ea8946c78a`,
except the last, which is this report in the main checkout.

| File | What changed |
| --- | --- |
| `Effect4/Semantics/RegionSimulation.lean` | the three repairs, the T5/T6 statements, the generalised T7 family; 1 070 → 2 106 lines |
| `Effect4Test/Semantics/RegionSimulationContract.lean` | two new fixtures, the T5/T6 instances, the P1/P3 receipts, 26 new `#check`s |
| `Effect4Test/Semantics/RegionSimulationAxiomReport.lean` | rewritten: 66 `#print axioms` lines in ten groups |
| `Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` | five divergences inverted to agreements; one new divergence (`tapeAfterRegion`) for the remaining obligation |
| `test/counterexamples/REGISTER.md` | repair columns of `E4-TARGET-CE-019`, `-020`, `-021` and `E4-FLOW-CE-020` |
| `test/contracts/frame-simulation.contract.md` | ruling 7 amended; "Open" item 1 closed, item 2 restated; new "Spike S4 amendment" section with its own verification block |
| `docs/research/2026-09-03-spike-s4-compile.md` *(main checkout)* | this report |

Three files were first copied from the main checkout into the worktree,
overwriting the worktree's older copies, as instructed:
`Effect4/Semantics/RegionSimulation.lean`,
`Effect4/Semantics/FrameSimulation.lean`, `Effect4/Runtime/ScopeRestoration.lean`.
`Effect4/Runtime/LiveStack.lean` was **not** touched.

Baseline before any change: `lake build Effect4.Semantics.RegionSimulation`
(the worktree's `.lake` was stale for `FrameSimulation.olean`), then
`lake env lean Effect4/Semantics/RegionSimulation.lean` — exit 0.

---

## 2. The four repairs, with their rc.112 lines

All line numbers are in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.

### P1 — one scope per region (`E4-TARGET-CE-019`, `E4-FLOW-CE-020`)

rc.112 basis:

* `:3938-3947` — `Effect.scoped` is `withFiber` + a fresh `Scope` in the fiber
  context + `onExitPrimitive`: **one** scope per region.
* `:3971-3987` — `Effect.acquireRelease` is `contextWith` +
  `uninterruptibleMask` + `flatMap` + `scopeAddFinalizerExit`. It registers on
  that one scope and **pushes no frame of its own**.
* `:3815-3827` — sequential scope close calls every finalizer with the same
  `exit_`, captures each exit, and combines the collected list only *after* the
  loop.
* `:3826`, `:2025-2038` — the combine is `exitAsVoidAll`: concatenation of the
  failed exits' reasons, no dedup.

What landed. The `enter` arm emits **one** frame:

```lean
Prim.onSuccessAndFailure (compiled body)
  (RegionName.regionCont region enterPoint)
  (RegionName.close      region enterPoint)
```

**Deviation from the brief's literal wording, and why.** The brief asked for
`Prim.onExit` with the finalizer name `RegionName.close region enterPoint`.
That is not available: `Prim.onExit` is the *only* primitive whose arm emits a
`FrameEvent.ranFinalizer` (`Runtime.lean` `finalizerEvents`), and `ranFinalizer`
is the only event besides `yielded` with a service-level shadow. A region
compiled to `Prim.onExit` therefore writes exactly **one** `finalizer` row per
region, while the runner (`Flow.closeReleases`) and the host
(`regions.finalizer(1, exit)` inside `Effect.acquireRelease`'s release lambda,
`SkeletonRender.lean:128-134`) both write **one per release**. The masked traces
would then differ on every region with two registrations — `regionTwoFail` and
`releaseFails` among them — and the three instances the brief requires to stay
closed by evaluation would stop being closed. This is ruling 7 of
`test/contracts/frame-simulation.contract.md` applied to the region frame rather
than to the `enter` row, and it is recorded there as an amendment.

`Prim.onSuccessAndFailure` is the faithful frame: rc.112's scope-closing frame
answers **both** arms (value and cause) and writes no finalizer row of its own,
which is exactly what `onSuccessAndFailure` does. `RegionName.close` is kept as
its **cause** name, so the constructor the brief asked for exists and carries
the region's close.

Each registered release keeps a `Prim.onExit … false` frame, pushed by
`regionInterp.contA` at the acquire's `cont` name. Its `finalizerExit` is
constantly `Exit.success ()`, so `Exit.restoreAfterFinalizer` is the identity
and **no release's outcome can reach the exit another release observes** — the
whole content of `E4-TARGET-CE-019`. The release's *actual* outcome is read by
the region's scope frame from `oracle.release`, collected by `closeExit`, and
applied once.

The close result is `closeExit oracle (oracle.registrations point)`:
`closeFinish` (the zero/one/many policy, bridged to
`Effect4.ScopeMachine.result?` by `closeFinish_eq_result?` because
`ScopeMachine.finish` is `private` to its module) over `Exit.asVoidAll` of the
release exits in `Scope.closeOrder`. `Effect4.Scope.closeResult_single` — one
finalizer returns its own exit *unmerged*, which `E4-RUN-CE-009` forbids
flattening — survives as `closeFinish_single`.

The value arm continues at `row.continue_` when the close succeeds and produces
`Prim.failure closingCause` when it does not, mirroring the runner's
`| [] => regionLoop … | error :: more => fail … rest error more`. The cause arm
appends the closing reasons to the body's — concatenation, matching
`Exit.asVoidAll` and `closeFrame_failure_merge`, never `Cause.combine`, which
dedups by structural equality including annotations (`:242-258`); that is
`E4-FLOW-CE-021`'s sharp fact and `merge_is_concatenation_not_union`'s ruling.

`hfin` is gone from every compiled run: `regionInterp_finalizerExit` is `rfl`.

### P2 — frontier-preserving compile (`E4-TARGET-CE-020`/`-021`, finalisation half)

rc.112 basis: none — there is no opcode here. The runner has simply not reached
the block, so the machine must not produce an *exit*. `docs/DESIGN-BASIS.md`
DB-04 and `Runtime.lean:2435-2439` (`FrameStep.running` at exhausted `run` fuel
is a live frontier, never a failure, defect, interruption or refusal).

The eight arms that sent live work to `Prim.failure Cause.empty` — exhausted
source fuel, a missing block, a stuck plan, an exhausted tape, a mismatched
tape, a malformed `enter`'s `readArgs`, a malformed `acquire`, a malformed
`leave` — now emit `Prim.suspend point`, and `regionSuspendBody` returns that
same suspension, so `FrameFiber.step` is a fixed point that writes no event
(`Runtime.lean` `step_suspend`).

### P3 — `performCatch` as `onSuccessAndFailure`

rc.112 basis: `:3417-3420` (`Effect.result` = `matchEager`) and `:3450-3460`
(`matchCause` → `matchCauseEffect` = `OnSuccessAndFailure`).

The caught perform compiles to
`Prim.onSuccessAndFailure (Prim.suspend point) (RegionName.cont point)
(RegionName.caught point)`. The flow note proposed making `syncValue` produce a
failing primitive; that is not typeable — `syncValue : σ → β` returns a value,
not a `Prim` — so the body is a `Prim.suspend` and `regionSuspendBody` returns
`Prim.failure (Cause.fail error)` on an erroring answer. The machine's `armE`
then resumes at the failure successor through `contE (RegionName.caught point)`,
which reads the error off the cause (`failuresOfCause`). The old shape, where
the error was resolved inside `contA` and no frame ever saw a `Cause`, is gone.

The constructor is spelled `caught`, not `catch`: `catch` is a `do`-notation
token in Lean 4 and cannot be an inductive constructor name.

### P4 — interrupts, deferred

Unchanged from the flow note: the compile carries `masked = []`, `itape = []`
implicitly (nothing in it emits `Prim.setInterruptible` and nothing writes
`interruptedCause`), and `Effect4/Flow/Interrupt.lean` was not touched.

---

## 3. Public declarations added, changed and removed

`Effect4/Semantics/RegionSimulation.lean`, namespace `Effect4.RegionSimulation`.

### Changed

| Name | Old | New |
| --- | --- | --- |
| `RegionName` | 3 constructors: `cont`, `regionCont`, `fin` | 5: `cont`, **`caught`**, `regionCont`, **`close`**, `fin` |
| `RegionName.regionOf` | 3 arms | 5 arms; `caught` → `0` |
| `RegionOracle` | fields `answer`, `release` | + **`registrations : Config → List Config`** |
| `compileRegion` | same type | `.enter` → `onSuccessAndFailure`; `.performCatch` → `onSuccessAndFailure` over `suspend`; eight `Prim.failure Cause.empty` arms → `Prim.suspend point` |
| `regionInterp` | same type | `finalizerExit` constantly `Exit.success ()`; `contE` routes `caught` and `close`; `suspendBody := regionSuspendBody …`; `contA` gains the `regionCont` close check and the `caught`/`close`/`fin` frontier arms; `loopBody` no longer uses `Cause.empty` |
| `statelessOracle` | 2 fields | 3; `answer`/`release` are now `statelessAnswer`/`statelessRelease` so `registrations` can reuse them |
| `unwind_failure` | `(interp) (cause) (hfin : ∀ name exit, …) : ∀ stack, unwindable stack = true → ∀ fuel, …` | `(interp) (cause) : ∀ stack, unwindable stack = true → FinalizersVoid interp (unwindNames stack) → ∀ fuel, …` |
| `close_success` | `(interp) (value) (hfin : ∀ name exit, …) (body) (name) (rest) : ∀ frames, closeable frames = true → …` | `(interp) (value) (body) (name) (rest) : ∀ frames, closeable frames = true → FinalizersVoid interp (closeNames frames) → …` |
| `closeNames` docstring | "before the region frame answers" | "before the frame that answers it" (it now also stops at an `onSuccessAndFailure`) |
| `regionBound` | `4 * runnerFuel + 1` | unchanged value, re-derived per arm in the docstring |
| `step_onSuccess_answers` | `private` | public (it is `close_success`'s `hanswer` witness) |

`regionBound` is **not** lower after P1. The re-derivation is in its docstring:
`jump`/`choose` cost nothing, `perform` two steps, `performCatch` three,
`acquire` three plus one at the close, `enter` one plus one at the close, `ret`
one. P1 removed the *nesting* of the release frames, not the frames: they are
what writes the `finalizer` row rc.112's release lambda writes, so the count
stays at four per runner block plus one.

### Added

Carriers and functions: `RegionName.point`, `Cleanup`, `closeWalk`,
`regionRegistrations`, `releaseExitOf`, `releaseExitsOf`, `closeFinish`,
`closeExit`, `closeFailuresOf`, `isFailure`, `caughtNames`, `regionSuspendBody`,
`statelessAnswer`, `statelessRelease`, `FinalizersVoid`, `releaseFrames`,
`RegionOracleAgrees` (structure), `RegionsSimulate`, `RegionsSimulateExit`.

Theorems: `closeFinish_nil`, `closeFinish_single`, `closeFinish_many`,
`closeFinish_eq_result?`, `closeExit_reasons`, `closeExit_success_iff`,
`compileRegion_not_failure`, `compileRegion_never_fails`,
`compileRegion_catchFree`, `regionSuspendBody_frontier`,
`regionSuspendBody_catch`, `regionSuspendBody_zero`, `step_suspend_fixed`,
`run_suspend_fixed`, `regionInterp_finalizerExit`, `regionInterp_suspend_fixed`,
`compileAt_zero_fuel_live`, `statelessOracle_agrees`, `toOutcome_append`,
`step_onSuccessAndFailure_answers`, `step_onSuccessAndFailure_answers_cause`,
`close_success_of`, `close_success_region`, `unwind_to_frame`,
`unwind_failure_region`, `close_success_region_compiled`,
`unwind_to_frame_region`, `closeNames_releaseFrames`, `closeable_releaseFrames`,
`region_close_rows`, `region_unwind_rows`.

### Removed

Nothing. No declaration was deleted; `Cause.empty` no longer appears in any
compiled program, but the `Cause` lemmas that mention it (`combine_reasons_cons`)
are unchanged.

### Batteries

`Effect4Test/Semantics/RegionSimulationContract.lean` adds `opReleaseBoom`, the
fixtures `regionReleaseFails` and `regionCatch`, `checked`, `SimulatesAt`,
`SimulatesExitAt`, `oracle_agrees`, `registrationsAt`, `caughtOf`, the ten
`T5_*`/`T6_*` instances, `regions_simulate_regionReleaseFails`,
`regions_simulate_regionCatch`, `runnerSide_regionReleaseFails`,
`runnerSide_regionCatch`, four `registrations_*` receipts, five `catch_free`
receipts and the concatenation-not-union example.

`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` renames five
divergence theorems to agreements (`repaired_frames_use_original_exit`,
`failing_release_agrees`, `source_fuel_zero_agrees`,
`source_fuel_after_acquire_agrees`, `unanswered_decision_agrees`,
`unanswered_after_choice_agrees`), adds `machineIsLive` and four `_live`
receipts, `mismatched_decision_machine_is_live`, and the `tapeAfterRegion`
fixture with `tapeAfterRegion_runner_completes`, `tapeAfterRegion_runner`,
`tapeAfterRegion_machine` and `tapeAfterRegion_diverges`.
`unrestricted_finite_agreement_false` is retained and reproved from
`tapeAfterRegion_diverges`.

---

## 4. T5, T6, T7: what is proved

### T7 — proved in general, and generalised

* `unwind_failure` — a failing exit through a whole fragment stack runs exactly
  the finalizers that stack names, in pop order, **every one against the same
  exit**, and yields that exit. Premise weakened from a global `hfin` to
  `FinalizersVoid interp (unwindNames stack)`.
* `close_success_of` — the same for a closing value up to *any* frame that
  answers `contA`, parameterised by a one-step `hanswer` witness.
  `close_success` (an `onSuccess` frame) and `close_success_region` (the
  region's `onSuccessAndFailure` scope frame) are its two corollaries, both by
  `rfl` witnesses.
* `unwind_to_frame` — **new**, the failure-side dual: a failing exit runs the
  `onExit` frames above the first frame declaring a cause arm, all against the
  same exit, and then that frame answers. This is what a region's scope frame
  needs on a failing body.
* `unwind_failure_region`, `close_success_region_compiled`,
  `unwind_to_frame_region` — the same three at `regionInterp`, **with no premise
  at all**, by `regionInterp_finalizerExit`.
* `region_close_rows`, `region_unwind_rows` — **new, and the general form of
  P1**: for *any* registration list `points`, any bodies, any region, the close
  writes `points.length` `finalizer region` rows, every one carrying the same
  closing exit. This is `E4-TARGET-CE-019`'s attacked statement refuted in
  general rather than at a fixture.

### T5 and T6 — stated in general, proved at five flows

```lean
def RegionsSimulate … (oracle) (tape) (input) (fuel' fuel) : Prop :=
  RegionOracleAgrees alphabet flow.flow service answerOf oracle →
  regionBound fuel' ≤ fuel →
  traceOfRun (FrameFiber.run (regionInterp alphabet flow.flow oracle) fuel
      (FrameFiber.start (compileAt alphabet flow.flow ⟨fuel', flow.flow.entry, [input], tape⟩))).2
    = Effects.Trace.project finalizerAndOutcomeMask
        (((Flow.runRegions fuel' flow service nameOf tape input).run []).2)

def RegionsSimulateExit … : Prop :=
  RegionOracleAgrees … → regionBound fuel' ≤ fuel →
  (FrameFiber.run (regionInterp …) fuel (FrameFiber.start (compileAt …))).1
    = FrameStep.finished
        (match ((Flow.runRegionsCause fuel' flow service nameOf tape input).run []).1 with
          | ((.done value, _), _) => Exit.success value
          | ((_, _), failures)    => Exit.failure (causeOfFailures failures))
```

`RegionOracleAgrees` has four clauses: `handle` (the service is stateless — the
flow note's `hOracle`), `answer`, `release` and `registrations`.
`statelessOracle_agrees` discharges the last three by `rfl`, so the only content
at that oracle is whether the `registrations` *definition* is right.

Proved instances, all by kernel evaluation at `Flow.fuelFor`'s runner fuel and
`regionBound`'s machine budget, empty tape, input `5`:

| Flow | What it exercises | T5 | T6 |
| --- | --- | --- | --- |
| `regionBothSucceed` | one region, one release, clean close | `T5_regionBothSucceed` | `T6_regionBothSucceed` |
| `regionNested` | nested regions, failing inner body | `T5_regionNested` | `T6_regionNested` |
| `regionTwoFail` | two releases of one region, failing body | `T5_regionTwoFail` | `T6_regionTwoFail` |
| `regionReleaseFails` | **`E4-TARGET-CE-019`'s own fixture**: two releases, the second failing, clean leave | `T5_regionReleaseFails` | `T6_regionReleaseFails` |
| `regionCatch` | **P3**: a `performCatch` whose operation fails, inside a region that then acquires and closes | `T5_regionCatch` | `T6_regionCatch` |

The pinned literals are in `runnerSide_*`; the corresponding `machineSide`
`#guard`s are the mutation receipts.

### The exact remaining obligation

**One clause: `RegionOracleAgrees.registrations`.** Everything else in T5/T6 is
either discharged by `statelessOracle_agrees` or is the induction over
`Flow.regionLoop` that this clause makes possible.

Concretely, `closeWalk` — the `leaveConfig` function the fence-C note said was
owed — mirrors `compileRegion`'s recursion arm for arm, *including* the two
places where `compileRegion` is known to be wrong: a region's continuation
resumes at `point.fuel - 1` with `point.tape`, i.e. the fuel and decision tape
the **enter** held, while `Flow.regionLoop` continues with the fuel and tape it
holds at the **leave**. So `closeWalk` agrees with `compileRegion` (which is
what the instances need) but does **not** agree with the runner in general
(which is what T5/T6 need).

`tapeAfterRegion` is the minimal witness, and it is in the boundary battery: a
region body that consumes decision site 7, followed by decision site 8 after the
region. The runner completes with `done (success 5)`; the machine meets a site
mismatch at the enter tape and stops live, trace `[]`.
`tapeAfterRegion_diverges` proves it, and
`unrestricted_finite_agreement_false` is now derived from it. No acquire is
involved, so it isolates the `leaveConfig` obligation from P1 and P2.

Closing it means one of two things, and the choice is a ruling, not a proof:

1. make `Config` carry the *leave*'s fuel and tape for a region continuation —
   i.e. give `RegionOracle` a `leaveConfig : Config → Config` field beside
   `registrations`, and prove both agree with `regionLoop` by one induction; or
2. keep the compile as is and state T5/T6 under the extra hypothesis that no
   region body consumes tape (`tapeAfterRegion` is then excluded by hypothesis),
   which is exactly the kind of restriction `E4-TARGET-CE-020`'s repair column
   forbids for the *general* relation but permits for the settled one.

I did not take that ruling; it is the first thing packet P4's remainder has to
decide, and it is now stated in `test/contracts/frame-simulation.contract.md`'s
"Open" item 2.

---

## 5. What I could not prove, and why

* **T5 and T6 in general.** Beyond the `registrations`/`leaveConfig` clause
  above, the induction is a full simulation over `Flow.regionLoop`'s ten arms
  against a machine that spends up to four steps per runner block, using
  `run_add`/`run_mono` to split the budget. `runRegions_fuelFor_finishes`
  (`Approximation.lean:2182`) supplies the runner-side termination and
  `Frame.toScope_closeOrder` the order half, but the step-by-step relation is
  the ~600-line workhorse the flow note priced, and it cannot be written before
  the `leaveConfig` ruling because the relation's `Config` component is exactly
  what changes.
* **T8, the endpoint classification.** Not attempted: it is packet P5. The
  compile now conflates a *refusal* with a *live suspension* — a mismatched tape
  compiles to the same `Prim.suspend` as an exhausted one. This is stated, not
  hidden: `mismatched_decision_is_refusal` (runner) against
  `mismatched_decision_machine_is_live` (machine), with a docstring saying
  `Flow.RunResult.refusedSite` has no `Exit` image so T8 must be a three-way
  classifier.
* **`ScopeMachine.finish` could not be named.** It is `private` to
  `Effect4/Runtime/ScopeMachine.lean`, which is outside this spike's fence, so
  its three arms are restated as `closeFinish` and `closeFinish_eq_result?` is
  the proved bridge to the public `ScopeMachine.result?`. If the landing wants
  one spelling, un-`private`-ing `finish` is a one-word change in a file this
  spike did not open.
* **`ScopeRestoration.resumeClosedScope_complete` is not consumed.** It is the
  step law for a *completed close driven by `ScopeMachine`*; the compiled close
  here is driven by frames, and the bridge between the two is
  `closeFinish_eq_result?` at the exit level only. Wiring
  `resumeClosedScope_complete` in needs the region's close to be a
  `ScopeMachine.State`, which is a carrier the compile does not build. Recorded
  as a reuse the general theorem may want and this spike did not need.
* **`docs/TRACE-DAG.md:50` is now stale** and is outside this spike's fence. Its
  `frame-simulation` row still says the compile "uses nested `onExit` frames for
  registrations and converts fuel/unanswered frontiers to empty failures", and
  that `unwind_failure`/`close_success` "retain their successful-finalizer
  premise". All three clauses are false as of this spike. The row is
  coordinator-owned; flagged, not edited.
* **No census row moved and none was claimed to.** The new theorems carry
  `census:` tags only for rows that already have witnesses
  (`scope.close-sequential`, `scope.close-merge`, `scope.exit-as-void-all`,
  `op.Suspend`, `op.OnSuccessAndFailure`). `scope.scoped` and
  `scope.acquire-release` were deliberately not tagged: they stay `partial` for
  the fiber-`Context` reason `docs/FRAMES-DAG.md:252-253` names, which no
  compile packet touches.
* **No golden, ledger row or host artefact changed.** A fallible release still
  has no lowering (`E4-TARGET-CE-012`), so P1's benefit is Lean-only and the
  host stays silent on it.

---

## 6. Register rows: the new repair text

`test/counterexamples/REGISTER.md`, repair columns only; statuses were left as
they were (`SEEDED`), since promoting a row is a coordinator decision.

**`E4-FLOW-CE-020`** — now: *DISCHARGED both sides (spike S4, 2026-09-03).*
Runner half unchanged; compile half repaired by P1 — one scope frame per region
(`Prim.onSuccessAndFailure`, names `RegionName.regionCont`/`RegionName.close`)
and one `onExit` row-emitter per release whose `finalizerExit` is
`Exit.success ()`, so order and exit now both hold on the machine:
`close_success_region_compiled`, `unwind_to_frame_region` and
`repaired_frames_use_original_exit`.

**`E4-TARGET-CE-019`** — now: *DISCHARGED (packet P1).* One scope, not a nest;
`regionInterp_finalizerExit`; the close is `closeExit` =
`ScopeMachine`'s zero/one/many policy over `Exit.asVoidAll`
(`closeFinish_nil`/`_single`/`_many`, `closeFinish_eq_result?`,
`closeExit_reasons`), applied once and restored once; `hfin` gone; witnesses
retained and inverted (`repaired_frames_use_original_exit`,
`failing_release_agrees`, plus the fixture as an instance of the general
equation: `regions_simulate_regionReleaseFails`, `T5_regionReleaseFails`,
`T6_regionReleaseFails`). rc.112: `:3815-3827`, `:3826`, `:2025-2038`,
`:3971-3987`. Fence C amended; generic `onExit` unchanged.

**`E4-TARGET-CE-020`** — now: *PARTIAL (packet P2).* Finalisation half
discharged — `compileRegion_not_failure`/`_never_fails`,
`step_suspend_fixed`, `run_suspend_fixed`, `compileAt_zero_fuel_live`, and the
`_machine`/`_live`/`_agrees` receipts. Still owed: the general finite-prefix and
residual-state simulation (T8, P5) and the refusal-versus-suspension
classification.

**`E4-TARGET-CE-021`** — now: *PARTIAL (packet P2).* Finalisation half
discharged — an unanswered decision compiles to `Prim.suspend`, the resource
stays held, unconsumed tape is preserved in the residual `Config`. Still owed
and now explicitly stated: the three-way classification (T8), and resuming a
region's continuation with the *leave*'s tape — `tapeAfterRegion_diverges` is
the witness, `RegionOracleAgrees.registrations` the named obligation.

---

## 7. Build results

Run in the worktree. No bare `lake build`, no sweep, no trust gate; one Lean
process at a time.

Baseline, before any edit:

```text
$ lake build Effect4.Semantics.RegionSimulation
Build completed successfully.
$ lake env lean Effect4/Semantics/RegionSimulation.lean
EXIT=0
```

Per-file verification, after all edits:

```text
Effect4/Semantics/RegionSimulation.lean                        exit=0 errors=0 sorry=0
Effect4Test/Semantics/RegionSimulationContract.lean            exit=0 errors=0 sorry=0
Effect4Test/Semantics/RegionSimulationAxiomReport.lean         exit=0 errors=0 sorry=0
Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean exit=0 errors=0 sorry=0
```

The required build:

```text
$ lake build Effect4.Semantics.RegionSimulation \
    Effect4Test.Semantics.RegionSimulationContract \
    Effect4Test.Counterexamples.Target.RegionSimulationBoundary
⚠ [12/48] Replayed Effect4.Runtime.Runtime
ℹ [46/48] Replayed Effect4Test.Semantics.RegionSimulationContract
ℹ [47/48] Replayed Effect4Test.Flow.RegionRunnerContract
ℹ [48/48] Replayed Effect4Test.Counterexamples.Target.RegionSimulationBoundary
Build completed successfully (48 jobs).
```

(The single warning is S1's pre-existing `unusedVariables` lint on
`Effect4/Runtime/Runtime.lean:1883`, not this spike's.)

Axiom report, `lake env lean Effect4Test/Semantics/RegionSimulationAxiomReport.lean`:

```text
exit 0
6  declarations depend on no axioms
64 declarations depend on axioms: [propext] or [propext, Quot.sound]
0  mentions of Classical.choice
0  mentions of sorryAx
```

The axiom report also includes `Effect4Test.Semantics.RegionSimulationAxiomReport`
in the umbrella build:

```text
$ lake build Effect4.Semantics.RegionSimulation \
    Effect4Test.Semantics.RegionSimulationContract \
    Effect4Test.Semantics.RegionSimulationAxiomReport \
    Effect4Test.Counterexamples.Target.RegionSimulationBoundary
Build completed successfully (49 jobs).
```

Nothing is committed. `git status --short` in the worktree shows the six files
this spike changed, plus the files spikes S1 and the LiveStack agent own.

---

## 8. Follow-ups for the coordinator

1. `docs/TRACE-DAG.md:50`'s `frame-simulation` row is stale in three clauses
   (nested `onExit`, empty-failure frontiers, the `hfin` premise). It is
   coordinator-owned and was not edited.
2. `Effect4.ScopeMachine.finish` is `private`; if the landing prefers one
   spelling of the zero/one/many close policy, un-`private` it and replace
   `RegionSimulation.closeFinish` with it, keeping
   `closeFinish_eq_result?` as the deleted bridge's obituary.
3. The `leaveConfig` ruling (§4, two options) is the first decision packet P4's
   remainder needs.
4. `generated/lowering-coverage.tsv`'s `proof` column is still `-` on all 29
   rows. `region-enter`, `region-acquire`, `region-leave` and `perform-catch`
   are now witnessed Lean-side by the five T5/T6 instances; adding
   `proved-lean-side` entries moves no host state
   (`docs/LOWERING-COVERAGE.md:56`) and is a separate, additive packet.

---

## 9. S4b: the leave configuration

Status: implemented, 2026-09-03, in the **main checkout**
`C:\Users\kokok\Dev\lean4-effect4` (not the S4 worktree). Nothing committed.
This section closes S4's one open obligation — clause
`RegionOracleAgrees.registrations` — and takes the ruling §4 deferred.

### 9.1 The ruling

Repair, do not restrict. §4 offered two options: give the oracle a
`leaveConfig` field, or state T5/T6 under a hypothesis that no region body
consumes tape. The second is exactly the kind of restriction
`E4-TARGET-CE-020`'s repair column forbids, so it is out. The route taken is
**(a) of the brief**: `regionInterp.contA`'s `regionCont` arm computes the leave
configuration *under the oracle, at answer time*. `PrimInterp`'s purity is not
violated — the flow note's §2.4 argument is that the tape is data and the answer
function is total and pure, and `statelessOracle` is the standing hypothesis.
Route (b) — carrying the leave configuration through the frame — is not
available: `Prim`'s value carrier is one `β`, the machine hands `contA` only that
`β`, and giving the continuation table a result-configuration index would change
`PrimInterp`'s shape and re-freeze `test/contracts/frames.contract.md`. Route (a)
also costs the oracle nothing: `RegionOracle` still has three fields.

### 9.2 The definition

`closeWalk` is rewritten so that it *is* the runner rather than the compile. It
now takes the oracle's `answer` **and** `release`, and carries the runner's open
region stack in the runner's own shape:

```lean
def closeWalk (alphabet) (flow) (answer release : Config -> Except Val Val) :
    Nat -> BlockId -> Env -> Tape ->
      List Config ->            -- the walked region's own accumulator
      List (List Config) ->     -- nested open regions, innermost first
      List Config × Option LeavePoint
```

* `enter` pushes an empty accumulator onto `inner`;
* `acquire` registers on the innermost open accumulator (`acc` when `inner` is
  empty), latest registered first;
* `leave` pops one nested accumulator — refusing to continue if any of *its*
  releases fails, because the runner's `fail` diverts there — or, when `inner`
  is empty, ends the walk;
* every other arm mirrors `Effect4.Flow.regionLoop` arm for arm, spending one
  unit of fuel per block.

Because the recursion is now structural in the runner's own fuel, no separate
step budget is needed and the agreement below is an ordinary induction.

```lean
structure LeavePoint where
  value : Val        -- what the `leave` hands on
  resume : Config    -- where `regionLoop` continues: continue_ block, [value],
                     -- and the fuel and tape held *at the leave*

def regionWalk … (point : Config) : List Config × Option LeavePoint
def regionRegistrations … point : List Config := (regionWalk … point).fst
def leaveConfig … point : Option Config := (regionWalk … point).snd.map LeavePoint.resume
```

`leaveConfig` is `none` exactly when the body does not reach a `leave` — a
failure, a frontier, a refusal, or a nested region that closes badly. In every
one of those cases the scope frame's *value* arm is never demanded (the cause
arm answers, or the machine stays suspended), so `Prim.suspend point` is the
honest filler.

### 9.3 The compile

```lean
| RegionName.regionCont _ point =>
  match closeExit oracle (oracle.registrations point) with
  | Exit.failure closing => Prim.failure closing
  | Exit.success _ =>
    match leaveConfig alphabet flow oracle.answer oracle.release point with
    | some resume => compileRegion alphabet flow resume.fuel resume.block [value] resume.tape
    | none => Prim.suspend point
```

The frame still supplies the *value* (that is what a frame can carry); the walk
supplies the fuel, block and tape (that is what it cannot). `flow.row?` moved
out of `contA` and into the walk's `leave` arm, where the runner reads it —
`current.region.bind flow.row?` of the *leave* block, not of the enter.
`regionInterp_regionCont_resume` states the arm as an equation.

Under S4 the same arm read
`compileRegion alphabet flow (point.fuel - 1) row.continue_ [value] point.tape`.
The receipts show the size of the difference: at `regionBothSucceed` the enter
holds fuel 5 at block 0 (`enterPoint_regionBothSucceed`), so S4 resumed at fuel
4, while the runner resumes at fuel 2 (`leaveConfig_regionBothSucceed`).

### 9.4 The agreement lemma

One lemma per runner arm, then the induction, then the corollary at an `enter`.
All are in `Effect4/Semantics/RegionSimulation.lean`, namespace
`Effect4.RegionSimulation`.

The runner writes rows and the walk does not, so the agreement is stated up to a
prefix of rows:

```lean
def RunPrefix {α} (left right : Effect4.Flow.RunM Id α) : Prop :=
  ∃ rows, ∀ log, left.run log = right.run (log ++ rows)
```

with `refl`, `of_eq`, `trans` and `emit`. Nothing is assumed about which rows
the runner writes, which is why the statement needs no second copy of the
runner's log.

**Per runner arm** (each an equation on `Effect4.Flow.regionLoop` at `fuel + 1`,
proved by `simp only` on the definition):
`regionLoop_jump`, `regionLoop_choose` (the arm S4's compile disagreed with),
`regionLoop_perform`, `regionLoop_performCatch_ok`,
`regionLoop_performCatch_error`, `regionLoop_enter`, `regionLoop_acquire`,
`regionLoop_leave`. Plus `logOperation_prefix` (an operation's rows are a
prefix and nothing else, from `Effect4.Flow.logOperation_run`).

**The close**: `closeReleases_cons_ok`, `closeReleases_success` and
`closeFrame_success` — a frame whose registrations all release cleanly closes
with no failure and writes only rows. The bridge between the walk's
`anyReleaseFails` and the runner's `closeFailures` is `statelessAnswer_of` plus
`registeredRelease`, which pairs an acquire point with the `(releaser, resource)`
entry the runner conses onto `Frame.releases`.

**The induction**:

```lean
theorem closeWalk_agrees_regionLoop
    (hservice : ∀ op request, service.handle op request = answerOf op request) :
  ∀ fuel block env tape acc inner regs leave innerFrames outer rest,
    closeWalk alphabet flow (statelessAnswer …) (statelessRelease …)
        fuel block env tape acc inner = (regs, some leave) →
    innerFrames.map Flow.Frame.releases = inner.map (registeredReleases …) →
    outer.releases = registeredReleases … acc →
    RunPrefix
      (Flow.regionLoop alphabet flow service nameOf fuel block env tape
        (innerFrames ++ outer :: rest))
      (leaveStep alphabet flow service nameOf answerOf outer.region regs leave rest)
```

`leaveStep` is what the runner does at the `leave`: close the walked region's
frame — whose releases are exactly `registeredReleases … regs` — with the leave
value, then continue at `leave.resume` or `fail` on a failing release. So the
theorem says, in one statement, both halves the register asked for: the
registrations the compile closes against *are* the runner's `Frame.releases`,
and the configuration the compile resumes at *is* the one the runner holds at
the leave.

**The corollary at an `enter`**: `leaveConfig_agrees_runRegions`, plus
`leaveConfig_of_regionWalk` and `regionRegistrations_of_regionWalk` tying the
walk's two components to the two public functions.

**The only premise is `hservice`** — the service is stateless on this alphabet.
That is D2's `stateless` (`Effect4/Flow/Region.lean:465`) in the oracle form the
flow note's §2.4 fixes, it is what `statelessOracle` already carries, and it is
not a restriction on flows. There is no hypothesis about tape, about region
bodies, about nesting depth or about which arms a body uses.

### 9.5 T5 and T6

**Not proved in general, and stated as a `Prop`, as the brief's fallback
requires.** What S4b removes is the `leaveConfig`/`registrations` clause; what is
left is the *machine-side* induction — relating `FrameFiber.run`'s steps to the
runner's blocks with `run_add`/`run_mono` and `regionBound`, and
`Frame.toScope_closeOrder` for the order. `runRegions_fuelFor_finishes`
(`Effect4/Semantics/Approximation.lean:2182`) supplies the runner-side
termination and is unchanged; `resumeClosedScope_complete` is still not consumed,
for the reason §5 gives (the compiled close is driven by frames, not by a
`ScopeMachine.State`).

The exact remaining obligation, as `Prop`-valued definitions in
`Effect4/Semantics/RegionSimulation.lean`:

```lean
def RegionsSimulateAll (alphabet) : Prop :=
  ∀ flow service answerOf nameOf oracle tape input fuel' fuel,
    RegionsSimulate alphabet flow service answerOf nameOf oracle tape input fuel' fuel

def RegionsSimulateExitAll (alphabet) : Prop := …  -- the same over RegionsSimulateExit
```

and, at the boundary battery's fixed stateless service,
`AllFiniteInputsAgree` (retained, no longer refuted).

**It is not vacuous.** Two witnesses, both in
`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean`:

* `finite_agreement_has_content` — at `failingRelease` the equation holds with
  *both sides non-empty* (`[finalizer 1 (success 5), finalizer 1 (success 5),
  done (failure "boom")]`), so the obligation is not "two empty lists are
  equal";
* `unrestricted_finite_classification_false` — the machine and the runner still
  differ, on the endpoint: `decisionCycle` at tape `[⟨8, false⟩]` is a
  `refusedSite` for the runner and a live suspension for the machine
  (`mismatched_decision_classification_diverges`). `Endpoint`,
  `runnerEndpoint` and `machineEndpoint` spell the three-way classifier the
  machine has only two readings of. That is T8, packet P5, untouched here.

No restriction on flows was introduced anywhere.

### 9.6 The inverted witness

`tapeAfterRegion` — a region body that consumes decision site 7, followed by
site 8 after the region — was S4's minimal witness that the walk was not the
runner. After S4b:

| Theorem | S4 | S4b |
| --- | --- | --- |
| `tapeAfterRegion_machine` | `some []` | `some [.done (.success (.nat 5))]` |
| `tapeAfterRegion_diverges` | proved | **deleted** |
| `tapeAfterRegion_agrees` | — | added: machine = runner |
| `tapeAfterRegion_agrees_other_branch` | — | added: the other edge and the other tape |
| `unrestricted_finite_agreement_false` | proved from the above | **deleted** — the trace equation has no counterexample left |
| `unrestricted_finite_classification_false` | — | added: what survives is the *endpoint* half |

The five instance receipts (`T5_*`, `T6_*`, `regions_simulate_*`,
`runnerSide_*`, the four `registrations_*`, the five `catch_free`) are unchanged
and still closed by evaluation; the `regionBothSucceed`, `regionNested`,
`regionTwoFail`, `regionReleaseFails` and `regionCatch` masked traces are
byte-identical to S4's. `regionBound` is unchanged at `4 * runnerFuel + 1`; its
docstring gains the S4b re-derivation (the compile now unrolls only blocks the
runner spends fuel on, so the per-block budget is exact rather than
mis-aligned).

A scratch search — not committed, run with `lake env lean` on a probe file in
the session scratchpad — compared `machineAt` against `runnerAt` over eight
region flows (including a nested region with decisions on both sides of it, a
region re-entered through its own `continue_`, and a caught failure that leaves
on the error edge), 22 fuels each and 91 tapes each: **16 016 cases, zero
mismatches.** That is evidence, not a receipt; the receipts are the theorems
above.

### 9.7 Public declarations added and changed

`Effect4/Semantics/RegionSimulation.lean` (2 115 → 2 801 lines), namespace
`Effect4.RegionSimulation`.

**Changed**

| Name | S4 | S4b |
| --- | --- | --- |
| `closeWalk` | `(answer) : Nat → BlockId → Env → Tape → List Config → List Config × Option Val` | `(answer release) : Nat → BlockId → Env → Tape → List Config → List (List Config) → List Config × Option LeavePoint`; mirrors the runner, not the compile |
| `regionRegistrations` | `(answer) point` | `(answer release) point`, defined as `(regionWalk … point).fst` |
| `regionInterp` | `contA`'s `regionCont` arm resumed at `point.fuel - 1`, `flow.row? ⟨region⟩`, `point.tape` | resumes at `leaveConfig alphabet flow oracle.answer oracle.release point`; the arm's `region` binder is now unused |
| `statelessOracle` | `registrations := regionRegistrations … (statelessAnswer …)` | `… (statelessAnswer …) (statelessRelease …)` |
| `RegionOracleAgrees.registrations` | "the missing induction" | a definition check on the oracle; the induction is `closeWalk_agrees_regionLoop` |
| `regionBound` | `4 * runnerFuel + 1` | same value, docstring re-derived for the leave-fuel resume |

**Added** — carriers and functions: `LeavePoint`, `anyReleaseFails`,
`registeredRelease`, `registeredReleases`, `regionWalk`, `leaveConfig`,
`RunPrefix`, `leaveStep`, `RegionsSimulateAll`, `RegionsSimulateExitAll`.

**Added** — theorems: `RunPrefix.refl`, `RunPrefix.of_eq`, `RunPrefix.trans`,
`RunPrefix.emit`, `logOperation_prefix`, `regionLoop_jump`, `regionLoop_choose`,
`regionLoop_perform`, `regionLoop_performCatch_ok`,
`regionLoop_performCatch_error`, `regionLoop_enter`, `regionLoop_acquire`,
`regionLoop_leave`, `anyReleaseFails_cons`, `closeReleases_cons_ok`,
`statelessAnswer_of`, `registeredReleases_nil`, `closeReleases_success`,
`closeFrame_success`, `closeWalk_agrees_regionLoop`,
`leaveConfig_agrees_runRegions`, `leaveConfig_of_regionWalk`,
`regionRegistrations_of_regionWalk`, `regionInterp_regionCont_resume`.

**Removed from the library:** nothing.

**Batteries.** `Effect4Test/Semantics/RegionSimulationContract.lean` (323 → 382)
adds 26 `#check`s, `leaveConfigOf`, `enterPointOf` and six leave-configuration
receipts. `Effect4Test/Semantics/RegionSimulationAxiomReport.lean` (96 → 132)
adds groups R11 (24 lines) and R12 (6 lines).
`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` (227 → 285)
inverts `tapeAfterRegion_machine`, adds `tapeAfterRegion_agrees`,
`tapeAfterRegion_agrees_other_branch`, `finite_agreement_has_content`,
`Endpoint`, `runnerEndpoint`, `machineEndpoint`, `AllFiniteInputsClassify`,
`mismatched_decision_classification_diverges` and
`unrestricted_finite_classification_false`, and deletes
`tapeAfterRegion_diverges` and `unrestricted_finite_agreement_false`.

### 9.8 Build results

One Lean process at a time; no bare `lake build`, no sweep, no trust gate.

```text
Effect4/Semantics/RegionSimulation.lean                          exit=0 errors=0 sorry=0
Effect4Test/Semantics/RegionSimulationContract.lean              exit=0 errors=0 sorry=0
Effect4Test/Semantics/RegionSimulationAxiomReport.lean           exit=0 errors=0 sorry=0
Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean exit=0 errors=0 sorry=0

$ lake build Effect4.Semantics.RegionSimulation \
    Effect4Test.Semantics.RegionSimulationContract \
    Effect4Test.Semantics.RegionSimulationAxiomReport \
    Effect4Test.Counterexamples.Target.RegionSimulationBoundary
Build completed successfully (49 jobs).

$ lake build Deep.ForkFlow
Build completed successfully (48 jobs).
```

Axiom report: exit 0, 9 declarations depend on no axioms, 91 depend on
`[propext]` or `[propext, Quot.sound]`, 0 mentions of `sorryAx`, 0 of
`Classical.choice`. The only warning in any of these builds is S1's pre-existing
`unusedVariables` lint at `Effect4/Runtime/Runtime.lean:1883`.

**`workshop/Deep/ForkFlow.lean` is not broken.** It builds green and was not
edited. It calls `compileRegion` (unchanged), matches on `RegionName` (unchanged,
still five constructors), and uses `statelessOracle`, `closeExit`,
`oracle.registrations`, `regionSuspendBody`, `regionBound`, `performCont`,
`catchCont` and `compileRegion_not_failure` — all unchanged in signature. It does
not mention `closeWalk` or `regionRegistrations`. One thing the coordinator
should know: `Deep.ForkFlow`'s `forkTable` (the `regionCont` arm of its `contA`,
around `workshop/Deep/ForkFlow.lean:805`; the file is being edited by another
lane, so the line may have moved) overrides `contA` with **its own copy** of that
arm, and the copy still reads

```lean
| RegionName.regionCont region point =>
  match closeExit oracle (oracle.registrations point) with
  | Exit.failure closing => Prim.failure closing
  | Exit.success _ =>
    match flow.row? ⟨region⟩ with
    | some row => compileFork … (point.fuel - 1) row.continue_ [value] point.tape
    | none => Prim.suspend point
```

— the **enter**'s fuel and tape, i.e. the shape S4b just repaired. It compiles
and nothing regresses, but `Deep.ForkFlow` now carries the defect S4b removed
from `regionInterp`. The one-line fix, when that spike lands, is to replace those
four lines with the `leaveConfig` match, exactly as `regionInterp.contA` does.
`forkOracle` needs no change (it is `statelessOracle`).

### 9.9 Out of fence, and stale

* `test/contracts/frame-simulation.contract.md` is now stale in four places and
  was **not** edited (it is outside this spike's fence): "Open" item 2
  (`:191-201`) still says the `leaveConfig` proof is owed and cites
  `tapeAfterRegion_diverges`; `:275` and `:420-422` still cite
  `unrestricted_finite_agreement_false`, which is deleted; the "Spike S4
  verification" block should gain
  `Effect4Test.Semantics.RegionSimulationAxiomReport` and `Deep.ForkFlow`.
* `docs/TRACE-DAG.md:50` was already flagged stale by S4 and still is.
* `harness/trace/Generate.lean frame-trace` prints to stdout and has no golden
  file, so nothing needed regenerating; the harness uses only `regionInterp`,
  `statelessOracle`, `regionBound`, `compileAt`, `traceOfRun` and
  `finalizerAndOutcomeMask`, none of which changed signature.
* No census row, ledger row, golden or host artefact moved, and none was
  claimed to.
