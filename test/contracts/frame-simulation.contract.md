# Frame-machine simulation of `interpret` — light contract

Status: GREEN, authored and implemented together 2026-09-03 (packet D4 fences B
and C; light ceremony, two new modules and no change to any frozen surface)

Implementation fences:
`Effect4/Semantics/FrameSimulation.lean` (fence B, the value half) and
`Effect4/Semantics/RegionSimulation.lean` (fence C, the finalizer half), plus
twelve appended theorems in `Effect4/Runtime/Runtime.lean` (packet D4 fence A,
frozen in `Effect4Test/Runtime/FramesContract.lean` section F10)

Lean batteries:
`Effect4Test/Semantics/FrameSimulationContract.lean`,
`Effect4Test/Semantics/RegionSimulationContract.lean`

Axiom reports:
`Effect4Test/Semantics/FrameSimulationAxiomReport.lean`,
`Effect4Test/Semantics/RegionSimulationAxiomReport.lean`

Proof graphs: `FRAME-PG-STACK` in `docs/FRAMES-DAG.md` (the fence A section and
the fence B section at the end); the `semantics` edge of
`docs/TRACE-DAG.md`

Packet source: `docs/research/2026-09-03-frame-simulation.md`, packet D4 of
`docs/research/2026-09-03-reification-plan.md`

## What is claimed

`Effect4.FrameSimulation.compile_simulates`. For

- a first-order alphabet `a` and its monomorphic signature `Flow.Sig a`, where
  every request and every answer is `Effects.Trace.Val`;
- a handler `H` into `ExceptT (Cause Val Unit Unit Unit) (StateT St Id)`;
- a program `p : Program (Flow.Sig a) Val` and an initial state `s0`;
- the answer tape `tape` with `answersOf H p s0 = tape`;
- any `fuel` with `bound tape ≤ fuel`,

the frame machine started on `compile 0 p` with the continuation table
`tapeInterp p tape` **finishes**, and the exit it yields is
`exitOf ((interpret H p).run.run s0).1`.

`compile_simulates_fail` is the same statement for a handler whose error carrier
is the raw user error, through `run_liftFail`.

## What is not claimed

- **That the machine computes `interpret`.** It does not. `PrimInterp` is a
  record of pure total functions, so the machine has nowhere to put a handler's
  monad; the answers are *supplied* by the tape. `hOracle` is what makes the pure
  table legitimate, and quoting the theorem without it is misquoting it. The
  content is that the machine's **control flow** — which continuation runs, in
  which order, with which exit — equals the algebra's, given agreeing answers.
  This is a simulation modulo an effect oracle.
- **Anything about the host.** No Lean theorem reaches JavaScript;
  `FRAME-L9-HOST-EVIDENCE` and the `bridges` edge of `docs/TRACE-DAG.md` stay
  open by construction.
- **Anything about interruption or concurrency.** Fence A proves the interrupt
  half of the machine is *inert* on this fragment, which is not the same as
  modelling it. Interruption remains evidence-only until A1 and a two-fiber
  model.
- **Anything about finalizers, brackets or regions, from `compile_simulates`.**
  `Program` has `pure` and `vis` and no bracket former, and `Handler.handle`
  takes an operation and never a subcomputation, so `FrameEvent.finalizersRun`
  has no algebra-side counterpart. That half is fence C, below, stated against
  `Effect4.Flow.runRegions` instead.
- **Any coverage number.** `docs/RUNTIME-COVERAGE.md` scores clause by clause,
  and a composite theorem is nobody's clause. **No census row turns green.**
  What changes is the *kind* of evidence for `rule.frames-are-primitives`,
  `op.Success`, `op.Sync` and `op.OnSuccess`: from single-transition equations to
  a composed run. Recording that on `rule.frames-are-primitives` is a separate
  packet with a separate claim, under the `runtime-coverage` procedure.

## CATEGORIES

- `interpreter` — `compile` and `tapeInterp` are a compilation plus its table;
- `algebraic-laws` — `exitOf`/`exceptOf` round-trip, `residual_append`,
  `interpret_pure`/`interpret_vis`;
- `total-functions` — every definition is total and first-order over finite data;
- `protocol-state` — the compiled fragment is closed (`inFragment`), so no mask
  combinator, `exitFrame`, `whileLoop` or `iterator` is ever entered.

## Rulings this packet makes, and why

1. **The tape carries outcomes, not bare answers.** The research packet writes
   `tape : List Val`. That statement is false: a handler may fail at an
   operation, a bare `List Val` cannot record where, so the machine has no way to
   fail and the two sides disagree on every failing run. `Answer` is the
   two-constructor outcome alphabet (`ok`, `failed`), and `Tape := List Answer`.
   The failing occurrence is the last entry, and no entry follows it.
2. **`bound` is a function of the tape.** The packet writes `bound p` with "the
   sup over the taken branch, discharged along the tape". The taken branch *is*
   the tape, so `bound tape = 2 * tape.length + 1`: two machine steps per
   performed operation (push the `OnSuccess` frame; run the `Sync` and pop it)
   and one to yield the exit. Under `hOracle` this is `bound (answersOf H p s0)`,
   a function of `p`, `H` and `s0`. The battery's last `#guard` is the tightness
   receipt: one unit below `bound` the run has *not* finished, and that is a live
   DB-04 frontier and not a result.
3. **Empty annotations are not a hypothesis, in either fence.** The research
   packet asks for one (its section 5(b)). In fence B the risk it names is
   unreachable: `Cause.combine` is reached only through
   `Exit.restoreAfterFinalizer` on an `onExit` arm, which this fragment never
   emits (`compile_inFragment`, `tapeContA_inFragment`). In fence C, where
   `onExit` frames are exactly what `acquire` pushes, it is reachable and still
   not needed, and the reason is sharper than avoidance: `Cause.combine` is
   `Cause.dedup` of the concatenation, `dedup` keeps the *first* occurrence
   (`Effect4.Cause.dedup_cons`), and `Exit.toOutcome` reads the first `fail`
   reason — so the head of a merged cause is the head of the body's cause
   whatever annotations either side carries. `RegionSimulation.toOutcome_combine`
   proves it unconditionally. Section 5(b) stays live only for a statement that
   compares whole *causes* rather than their wire projection; neither fence
   does.
4. **The name alphabet is gated.** `ν := Nat` and `σ := Nat`, and two `example`s
   in the module and two in the battery assert `DecidableEq Code` and
   `DecidableEq Machine`. The trap `docs/FRAMES-DAG.md` separation 4 exists to
   forbid — `ν := Σ op, (S.Answer op → Program S Val)` — elaborates fine and
   silently drops decidable equality from the emitted `Prim`, turning every
   `frame-arm` census row from a statement about frames into a statement about
   Lean functions. These four ascriptions fail to elaborate if anyone does it.
5. **Module placement is an open ownership question.**
   `Effect4/Semantics/FrameSimulation.lean` imports `Effect4/Runtime/Runtime.lean`,
   and `docs/ARCHITECTURE.md` places Runtime **above** Semantics
   (`docs/FRAMES-DAG.md` separation 2). No other module under
   `Effect4/Semantics/` imports this one, so the established Runtime → Semantics
   edge is not reversed for any existing module; but if the merge prefers strict
   directory layering the module moves to `Effect4/Runtime/FrameSimulation.lean`
   unchanged. Flagged here rather than resolved unilaterally.
6. **`Flow.Sig` is unified.** The local `Effect4.FrameSimulation.Flow.Sig`, once
   marked `-- to be unified with Denotation.lean`, is gone.
   `Effect4/Semantics/FrameSimulation.lean` imports
   `Effect4/Semantics/Denotation.lean` and uses `Effect4.Flow.Sig`; the five
   `variable` lines move from `Alphabet.{0,0} Ty` to `FlowAlphabet.{0,0} Ty`,
   `Flow.Sig a` resolves through the enclosing namespace, and every theorem
   statement is unchanged.
7. **`enter` does not compile to `onExit`.** Fence C compiles `enter` to
   `Prim.onSuccess body ν` and only `acquire` to `Prim.onExit`. The reason is
   forced, not stylistic: the row `enter`/`leave` writes has **no** frame-machine
   shadow — `FrameEvent.toTrace` sends everything but `ranFinalizer` and
   `yielded` to `none` — so compiling `enter` to `Prim.onExit` would manufacture
   a `finalizer` row the runner never writes, and the masked traces would differ
   on every region. `acquire`'s `Prim.onExit … false` is rc.112's `scopedFrame`,
   which is what `Effect.acquireRelease` lowers to, and the frames stack in
   registration order so they pop latest-first: the order
   `E4-TARGET-CE-012..014` pin for the host and `Frame.toScope_closeOrder`
   proves for the runner.
8. **The name alphabet of fence C carries the run point.** `ν := RegionName`,
   an inductive over `Config = Nat × BlockId × Env × Tape`. That is first-order
   data with a derived `DecidableEq`, so ruling 4's gate holds unchanged; the
   battery re-asserts `DecidableEq Code`, `DecidableEq RegionName` and
   `DecidableEq Config`. `Config.fuel` is a *step counter* — the runner spends
   one unit per block — so a point is reached at most once in a run and no
   separate occurrence index is needed. `compileRegion` recurses structurally on
   its fuel argument rather than on `Config.fuel`, which is what keeps the
   compiled program kernel-reducible and the fence C instances provable by
   `rfl`.

## Open

**Fence C is partial, and says so.** The general `regions_simulate` is *owed*:
its exact wording is in the header of `Effect4/Semantics/RegionSimulation.lean`,
and no definition stands in for it. What is closed:

- `unwind_failure` and `close_success`, in full generality — the machine's
  finalizer half. A failing exit propagating through a fragment stack runs
  exactly the finalizers that stack names, in pop order, every one against the
  *same* exit, and then yields that exit; a closing value runs the `onExit`
  frames above the answering `onSuccess` frame, latest-registered first, and then
  the region frame answers with its named continuation.
- The instances `regions_simulate_regionBothSucceed` (one region, one release),
  `regions_simulate_regionNested` (nested regions) and
  `regions_simulate_regionTwoFail` (two releases of one region closing on a
  failing body), each by kernel evaluation, each with both sides pinned to a
  literal so the equation cannot hold vacuously.

The blocking divergence the fence B note recorded is **settled**, and settled by
packet D2 rather than by weakening anything: the region runner now carries a
merged failure list in close order (`closeFrame_failure_merge`), so the
machine's `Cause.combine bodyCause finalizerCause` and the runner's list are
related by the projection `failuresOfCause` — the direction that is a total
function — with `causeOfFailures` as its section and
`failuresOfCause_causeOfFailures` as the retraction.

Two things stay open, and they are different in kind.

1. **A failing release is a real divergence, not a proof gap.**
   `closeReleases` gives every release of one close the *same* closing exit,
   while the machine threads the exit each finalizer restores, so on a close
   whose first release fails the two disagree on the second release's
   `finalizer` row. Both general theorems therefore carry `hfin`: every
   finalizer succeeds. That is exactly the hypothesis `regionReleaseFails`
   violates, which is also why that flow has no host golden
   (`E4-TARGET-CE-012`). Closing it means deciding which emitter is right and
   re-pinning the neighbour of `E4-FLOW-CE-019`.
2. **The general induction needs a second copy of the runner.** The runner's
   `leave` continues at `row.continue_` with the fuel and decision tape it holds
   *at the leave*, while the frame `enter` pushes is named at the *enter*.
   Closing it needs a `leaveConfig` that walks a region body to its close under
   the oracle, plus a proof that it agrees with the runner — its own fence.

`harness/trace/Generate.lean frame-trace` prints both sides of the equation for
every region program, so the pair can be pinned as a golden without waiting for
either.

## Verification

```text
lake build Effect4
lake env lean Effect4/Semantics/FrameSimulation.lean
lake env lean Effect4Test/Semantics/FrameSimulationContract.lean
lake env lean Effect4Test/Semantics/FrameSimulationAxiomReport.lean
lake env lean Effect4/Semantics/RegionSimulation.lean
lake env lean Effect4Test/Semantics/RegionSimulationContract.lean
lake env lean Effect4Test/Semantics/RegionSimulationAxiomReport.lean
lake env lean --run harness/trace/Generate.lean frame-trace
lake build Effect4Test
./scripts/test-trust-gate.sh
```

Every public theorem of this packet is within `propext` / `Quot.sound`; the
`#print axioms` receipts are in the axiom report.

## Independent boundary amendment, 2026-09-03

The current region compilation does not satisfy the unrestricted region trace
equation. This amendment supersedes ruling 7's claim that acquisition
registrations are nested `scopedFrame`s, the proposed complete-run
`leaveConfig` replay as a sufficient repair, and any reading of GREEN as a
general fence-C result. The existing proved value simulation, generic frame
laws, Scope laws and region-runner meanings remain unchanged. The existing
`unwind_failure` and `close_success` remain conditional on their actual `hfin`
premise; they do not establish cleanup with arbitrary failing releases.

The independent witnesses are in
`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean`, based on
repository commit `8351f88939cf03dcdb9487b5f9b0a11792632800`. They reuse
`Effect4Test.Flow.RegionRunnerContract.releaseFails`, already linked by
`E4-FLOW-CE-019` and `E4-FLOW-CE-020`; `E4-TARGET-CE-012` continues to refuse a
typed fallible release at the TypeScript lowering boundary.

### Source and decisive controls

The source pin is `effect@4.0.0-rc.112`, upstream commit
`2600f62f4532026928454dcea8d1c48557b3f942`, with
`src/internal/effect.ts` SHA-256
`0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`.
`vendor/effect-4.0.0-rc.112/README.md` owns the package integrity. In the pinned
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3815-3827`, sequential scope
close calls every finalizer with the same `exit_`, captures each exit, and
combines the resulting list only after the loop. `scoped` installs one scope
callback at lines 3938-3946; `acquireRelease` registers on that scope at lines
3971-3987. The generic `onExit` arms at lines 4017-4027 restore or merge the
exit after each callback. These are distinct compositions.

- **E4-TARGET-CE-019:** an admitted scope registers A, then B; its body succeeds
  with `5`; B's release fails. The runner gives both releases `success 5`.
  The compiled nested frames give B `success 5` and A `failure "boom"`.
  Both finish with that failure. The same two registrations with successful
  releases form a positive control: both traces contain two successful
  finalizer observations followed by successful completion.
- **E4-TARGET-CE-020:** at source fuel zero, the runner is a fuel frontier and
  its masked trace is empty; the compiled machine reports `done interrupted`.
  At source fuel two, after acquisition, the runner remains live without
  cleanup; the machine runs a finalizer with `interrupted` and then reports
  completion. The machine is given `regionBound` fuel in both cases.
- **E4-TARGET-CE-021:** an admitted resource-bearing decision cycle reaches
  unanswered site 7, both with an initially empty tape and after consuming a
  true decision. The runner remains live without cleanup, whereas the machine
  finalizes and reports interruption. A false decision exits and closes
  successfully on both sides. A mismatched site remains a distinct refusal
  with the unmatched tape retained on the runner side.

`unrestricted_finite_agreement_false` refutes the universally quantified trace
equation even for the fixed stateless service used by these admitted fixtures.
The battery compiles because it proves the mismatches; this is a green
counterexample battery against a false claim, not an implemented repair.

`test/counterexamples/target/region-simulation-boundary.mjs` preserves the
scratch host experiment. It checks installed package version and source hash
against this pin before comparing scope cleanup with nested `onExit` cleanup.
The `die` control uses an effect whose error row is `never`; the `fail` control
deliberately executes JavaScript outside `acquireRelease`'s public TypeScript
release signature. All three finite cases, including successful cleanup,
passed on Node.js 22.23.2. This evidence confirms the source-policy distinction;
it neither widens current lowering admission nor closes the host bridge.

### Required replacement and observations

The replacement must execute scope registration and cleanup independently of
the source runner. It must retain canonical first-order scope state and a
closing phase containing the original closing exit, pending releases,
captured release exits, and actual continuation. Reuse the existing Scope,
Exit and Cause owners. Register only after successful acquisition, mark the
scope closed before cleanup, execute every pending release with the same
original exit while retaining state produced before failure, and apply the
scope merge followed by `restoreAfterFinalizer` once per scope. An enclosing
scope observes the resulting exit of the inner scope. A completed-run oracle
that replays the source and supplies registrations or cleanup traces does not
satisfy this representation requirement.

The general obligation is a finite-prefix simulation with a residual-state
relation for every admitted flow, finite tape and matching service/decision
responses, including failing releases. The relation must connect the current
continuation and environment, unconsumed tape, open scopes and registrations,
service state, and cleanup progress. Endpoints distinguish success, failure,
refusal and live suspension. Fuel exhaustion and unanswered choices retain
pending work without finalization; supplying fuel or a compatible decision
continues that stored work. No settled-only, successful-release-only or
complete-tape premise may replace this general obligation. A settled trace
equality may be an intermediate theorem or corollary.

Prove the cleanup sub-execution against `Scope.closeExitsM` and the existing
zero/one/many `Scope.closeResult` policy, then connect one scope callback to
`Prim.scopedFrame` and `Exit.restoreAfterFinalizer`. The explicit
`FRAME-FB-FINALIZER-EFFECT` boundary in `docs/FRAMES-DAG.md` currently collapses
callback execution to `PrimInterp.finalizerExit`; a nominal constructor alone
does not close it. Finalizer trace rows must arise from actual cleanup steps,
not from a projection that invents them from a completed source trace.

The old `finalizerAndOutcomeMask` retains finalizer and outcome rows only.
Operation, answer, operation-failure, decision, region and frontier rows are
discarded. `Exit.toOutcome` further loses complete causes and annotations.
The new general relation must retain frontier identity and residual state
outside this mask. `Exit.asVoidAll` keeps duplicate cleanup reasons, while
`Cause.combine` may deduplicate when merging a failed body with cleanup.
Therefore `failuresOfCause_causeOfFailures` is only the stated retraction;
it does not establish equality between an arbitrary final target cause and
the runner's complete failure list.

### Narrow verification

```text
lake env lean Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean
node test/counterexamples/target/region-simulation-boundary.mjs /absolute/path/to/node_modules/effect
```

The Lean file prints an axiom receipt for every theorem. Root imports,
generated register projections, package builds, runtime coverage and the new
production execution component remain separate coordinator-owned work.
