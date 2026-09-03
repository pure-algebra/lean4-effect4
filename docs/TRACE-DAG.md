# Trace agreement proof graph

Status: opened 2026-09-02 with the trace lane; every edge but `semantics` and
`bridges` closed the same day; those two were `required-open` by ruling for
this phase. Amended 2026-09-03: `semantics` is closed for the Lean-to-Lean pair
(the runner is `interpret` of a denotation, packet D1); `bridges` and the host
half of `semantics` stay open by construction — no Lean statement reaches the
host.
Also on 2026-09-03 the frame machine half closed **for the Lean pair only** on 2026-09-03
(packet D4, `Effect4.FrameSimulation.compile_simulates`); read its scope line
before quoting it, and do not read it as closed globally. `bridges` stays open
by construction: no Lean statement reaches the host.

The graph-bearing owner is `TRACE-PG-AGREEMENT`. Its subject is one shared,
service-level trace alphabet (`Effects.Trace.Event`, minted in lean4-effects) and
the claim that two emitters of it agree under a named mask. The emitters are the
traced service over the algebra (`Family.Service.traced`), the Flow runner, and the
host through a Tracer hook and a service proxy. The frame-level stream the host can
also produce (`frames.jsonl`) is recorded and never compared: it is not an emitter
of this alphabet until a projection from `Effect4.FrameEvent` exists
(`docs/FRAMES-DAG.md` separation 7 keeps that projection a bridge obligation).

```text
TRACE-ALPHABET (Effects/Trace.lean)
   |
   +--> TRACED-SERVICE ---- interpret_traced_fst ----> ALGEBRA (Effects/Algebra)
   |
   +--> FLOW-RUNNER (Effect4/Semantics/Runs.lean) ---- internal oracle (m2) ----> TRACED-SERVICE
   |
   +--> HOST-TRACER (harness/trace, effect4-tools)
   |
   v
AGREEMENT under Mask (Effect4/Semantics/Observation.lean)
   |                  \
   v                   --> LOWERING-COVERAGE ledger (docs/LOWERING-COVERAGE.md)
FRAME-BRIDGE (required-open): FrameEvent.toTrace, scheduler Event.toTrace

DENOTATION (Effect4/Semantics/Denotation.lean, D1)
  FLOW-RUNNER = interpret (traceHandler service nameOf) . denote, closed by outcomeRows
  so the Lean pair agrees by theorem, not by comparison under a mask
```

## Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | `Effects.Trace.Event`, `Trace.Mask`, `Trace.Val` frozen by `EffectsTest/Trace/TraceContract.lean` (lean4-effects v0.3.0, `test/contracts/trace.contract.md`) |
| construction | `required-closed` | `Family.Service.traced` and `Family.Service.tracedExcept` (v0.3.1); `X.traced`, `X.tracedExcept` emitted by `effect_signature`; receipts in `Effect4Test/Semantics/ObservationContract.lean` |
| laws | `required-closed` | `interpret_traced_fst`, `interpret_tracedExcept_fst`, `project_project`, `project_m2`, `agree_of_agree_m2`, all within `propext`/`Quot.sound` (`EffectsTest/Trace/AxiomReport.lean`) |
| flow-runner | `required-closed` | Flow v2 runner (`Effect4/Semantics/Runs.lean`: `plan`/`step`/`loop`, `FlowService`, `Frontier`, the decision tape `Effect4/Flow/Decision.lean`) with laws `run_checked_not_stuck`, `run_fuel_mono`, `step_choose_consumes_one`, `plan_checked` within the ceiling (`Effect4Test/Flow/RunnerAxiomReport.lean`); the straight-line embedding `Script.toFlow` (`Effect4/Target/TypeScript/ScriptFlow.lean`) is admitted by `Effects.admit`; the internal oracle: `generated/traces/flow/*.empty.tsv` (face `lean-flow`) agree with the traced-service goldens under `m2` (`Generate.lean oracle`, part of `scripts/check-trace-goldens.sh`; planted mutant 4/4) |
| semantics | **closed for the Lean pair: runner = `interpret ∘ denote`; host stays evidence** (2026-09-03) | `Effect4/Semantics/Denotation.lean` (packet D1, `test/contracts/flow-denotation.contract.md`): a `CheckedFlow` denotes a `Program (Sig a ⊕ₛ DecSig)` — the alphabet through `Alphabet.toFamily` at the constant denotation `Val`, plus a decision summand answering `Unit`. T1 `runTape_eq_interpretRun`: the runner at every fuel is `interpret` under `(guarded traced service).toHandler.sum decisionHandler`, closed by `outcomeRows` (`done` and `frontier` have no former in the algebra and are a function of the result, not operations of any summand). T2 `denoteFuel_eq_denote`: at `fuelFor`'s allotment the fuelled denotation is the fuel-free `denote`, well-founded on `(tape.length, (raw.reachSet block).length)` through `reachSet_length_lt_of_edge` and `CyclesWF`, carried by the `LoopBudget` invariant of `Effect4/Semantics/Fuel.lean`. The `m2` oracle is an instance of T1 on the `incr`, `chooser` and `chosenLoop` flows (`Effect4Test/Semantics/DenotationContract.lean`). Still open on this edge: regions (a scope summand, packet D2), the `Script` embedding (D5), the frame machine (D4), and everything host-side, which stays evidence |
| frame-simulation | `required-closed` **for the Lean pair only** | **Value half.** `Effect4.FrameSimulation.compile_simulates` (`Effect4/Semantics/FrameSimulation.lean`, packet D4, `test/contracts/frame-simulation.contract.md`): for `bound tape <= fuel` and `answersOf H p s0 = tape`, the frame machine started on `compile 0 p` finishes with `exitOf ((interpret H p).run.run s0).1`, with `H` into `ExceptT (Cause Val Unit Unit Unit) (StateT St Id)`; `compile_simulates_fail` is the `Cause.fail` specialisation. It covers the compiled fragment only (`success`, `failure`, `sync`, `onSuccess`; `inFragment` and `compile_inFragment` prove the rest is unreachable). **Finalizer half** (2026-09-03, `Effect4/Semantics/RegionSimulation.lean`): stated against `Effect4.Flow.runRegions`, because `Program` has no bracket former. `compileRegion` compiles an admitted region flow in the shape `Effect4/Target/TypeScript/RegionLower.lean` lowers to — `enter` to `Prim.onSuccess` (its row is `leave`, which has no `FrameEvent` shadow), `acquire` to the `sync` gadget then `Prim.onExit … (RegionName.fin …) false`, so the finalizer order is the host's latest-first order pinned by `E4-TARGET-CE-012..014`. `unwind_failure` and `close_success` are general theorems about the machine's finalizer half; `regions_simulate` itself is **owed**, its exact wording in the module header, and is closed by evaluation at `regionBothSucceed`, `regionNested` and `regionTwoFail` (`Effect4Test/Semantics/RegionSimulationContract.lean`, both sides pinned to literals). The D2 merge ruling makes the payload agree: `Cause.combine` is `dedup` of the concatenation, `dedup` keeps the first occurrence, and `Exit.toOutcome` reads the first `fail` reason, so `toOutcome_combine` needs no empty-annotation hypothesis. Still open: a *failing* release, where the runner gives every release of one close the same closing exit while the machine threads the accumulating one; and the general induction, which needs a `leaveConfig` walking a region body to its close. **Scope line, read it before quoting the row:** both halves are simulations *modulo an effect oracle* — `PrimInterp` is pure and total, the answers are supplied, and `hOracle` is what makes that legitimate; what is proved is that the machine's control flow, exit and finalizer rows equal the emitter's given agreeing answers. Neither says anything about the host: **the host agreeing with either emitter is still executable evidence under a mask, never a theorem.** Do not close this row globally |
| representation | `required-closed` | TSV wire form rendered only in `Effect4/Target/TypeScript/Trace.lean` (exact-module admission); no `String` in the alphabet |
| counterexamples | `required-closed` | `EF-TRACE-CE-001..003` (lean4-effects), `E4-SEM-CE-008..009`, `E4-TARGET-CE-009..010`; planted mutants in `scripts/test-trace-goldens-gate.sh` (3/3) |
| bridges | `required-open` | `FrameEvent.toTrace`, `FrameEvent.traceOf`, `Event.toTrace` and `Exit.toOutcome` are defined in `Effect4/Target/TypeScript/Simulation.lean` (P-T11): finalizers and outcomes project, everything else to `none`; the patched rc.112 copy (`harness/trace/patched/`, seven observation-only hunks) records frame-level rows in `harness/trace/receipts/patched/` and `scripts/check-trace-patched.sh` pins three scope facts (two releases latest-first through the loop, a single release inline, nested single releases inline inner-first) while every service-level trace stays equal; no theorem relates a host row to a `FrameEvent`, so the primitive stream is still not evidence. Packet D4 does **not** close this row and cannot: `FRAME-L9-HOST-EVIDENCE` and the reification plan's refusal row both say no Lean statement reaches the host. What changed is smaller and real — `FrameEvent.toTrace` / `traceOf` are no longer definitions with nothing on the Lean side to compare, because `compile_simulates` gives the frame machine a proved relation to `interpret`; the frame stream itself is still recorded and never compared |
| targets | `required-closed` | `harness/trace/check.sh`: fixture drift for the straight-line module (`fixture.ts`) and the dispatch-form module (`flow-fixture.ts`, `Effect4/Target/TypeScript/FlowLower.lean`, ruling R7), four host gates, every golden under every mask at a large yield threshold and at the rc.112 floor of 3 (the flow goldens through `flow-tail.ts` with the `Decisions` service answering from the golden's tape), type receipts from `tsc.original` for both modules; region programs (`Effect4/Target/TypeScript/RegionLower.lean`: `Effect.scoped`, `Effect.onExit`, `Effect.acquireRelease`, never `try/finally`) run with a `Regions` service reporting `enter`, `leave` and `finalizer` with the exits the host handed them; receipts under `harness/trace/receipts/` and `receipts/flow/` |
| trust | `required-closed` | axiom receipts for every trace law; gate exemptions for the renderer, the DSL and the numerator only; `scripts/test-trust-gate.sh` green |
| structured-agreement | `required-open` | **partially closed in Lean, 2026-09-03.** *Proved* (`Effect4/Target/TypeScript/StructureLaws.lean`, `propext`/`Quot.sound`): `emitWith_wellScoped` — in the emitted statements every `continue l` sits inside its `while l`, and every `break l` names a block label of the graph; `structuredBody_wellScoped` discharges its `BodyScoped` hypothesis for Effect4's own `lowerBlockWith`, and `graphOf_closed` its `GraphClosed` hypothesis. This is the half row `E4-TARGET-CE-013` violated: `emitWith`'s wrapping of a loop-header entry is what the theorem needs, and the pre-fix emission makes it false. It needs neither reducibility nor the correctness of the dominator computation — `Structure.dominates` *is* the walk up the `idom` chain `emitNode` descends. *Open, exactly*: (a) `BreakScopedStatement` — every `break L<t>` is enclosed by its `label L<t>:`; blocked on two facts about the pinned `typescript` package that Effect4 cannot state over its definitions: `Structure.idom t` lies on the `idom` chain of every predecessor of `t` (correctness of the Cooper–Harvey–Kennedy iteration in `Structure.idoms`) and a forward edge's target comes later in `Structure.rpo` than its source. (b) trace agreement itself, which needs a control-flow interpreter for the emitted statement skeleton (statement recorded in `test/contracts/flow-structured-lowering.contract.md`). Executable receipts stand in for (a) on the packet's flows: `Effect4Test/Target/TypeScript/StructureLawsContract.lean` runs the strict predicate `wellScopedList [] []` on the swap loop, the label-free chain and the entry-loop-header flow. Host evidence unchanged: every flow golden through `structured-tail.ts`, the property corpus through `property-structured-tail.ts`, 1277 cases each way, a planted `continue`→`break` mutant caught |
| coverage | `required-closed` | `generated/lowering-coverage.tsv` (twenty-four rules: eight straight-line `checked`, eight dispatch-form `covered`, three region `checked`, four structured `covered`, `dispatch-fallback` `checked` on the irreducible program by the property loop `generated/lowering-property.tsv`: 200 generated flows, 1277 host runs, 276 frontiers, 318 sites both ways, 3/3 planted lowering mutants caught), `scripts/check-lowering-coverage.sh`, planted mutants (4/4) |
| approximation | `required-open` (both runner halves closed in Lean, 2026-09-03) | `Effect4/Semantics/Approximation.lean` (DB-04 laws over the tape runner: fuel exhaustion is a live `frontier`, never a failure or refusal, and more fuel only extends a frontier run). **The region half landed 2026-09-03** over D2's merged failure list: `regionStep_log_extends`, `regionLoop_fuel_stable` (a settled run is bit-identical at every larger fuel -- result, tape, merged failure list, log and service state), `region_obs_mono`/`region_obs_chain` and their `runRegions` forms, `regionLoop_frontier_live` (a fuel frontier is a `fuel` frontier, never `failed`, never `refused`, and the merged failure list is empty) and `regionLoop_failed_head` (a failing run's merged list is headed by the error the wire reports, the carrier `closeFrame_failure_merge` fixes). The region fuel formula is the erased flow's: `regionFuelFor flow tape = fuelFor flow.erase tape = (tape.length + 1) * flow.blocks.length + 1`, and `runRegions_fuelFor_finishes` proves it suffices, so `runRegionsColimitDefault` is total. Receipts on `regionNested`, `regionTwoFail`, `regionBothSucceed` and a merged-failure program in `Effect4Test/Semantics/ApproximationContract.lean`; axioms in `Effect4Test/Semantics/ApproximationAxiomReport.lean` (`propext`, `Quot.sound`). `Generate.lean region-frontier` emits the Lean-face frontier golden of each region program at one fuel below finishing. The row stays open because nothing host-side is claimed: no gate compares a host run at a region fuel frontier |
| logic | `required-closed` for the Lean pair (2026-09-03) | DB-06 over D1's denotation, `Effect4/Semantics/Logic.lean`: `box`/`dia`/`total`/`wp` relative to an answer specification, `wp_iff_wlp_and_total` (every program) and `Flow.wp_iff` (a flow against a tape and input; partiality is the unanswered frontier and the refusal, never fuel), `box_sound`/`dia_complete` against `interpret` for deterministic handlers (`DetRun`: `StateT σ Id` and every `StateT` layer over it, so the runner's `RunM`), `Flow.wlp_runDefault`/`wp_runDefault` through T1/T2, and `box_ofOracle_iff` (against an oracle the box is evaluation, which is what `Effect4Test/Semantics/LogicContract.lean` decides on `incr` and `chooser`). Axioms within the ceiling (`LogicAxiomReport.lean`). Says nothing about the host |
| equivalence | `required-closed` for the Lean pair (2026-09-03) | `Effect4/Semantics/Equivalence.lean`: `Flow.Equiv` (the same denotation against every tape and input; fuel-free by T2), an equivalence relation, with the congruences `Equiv.interpret`, `Equiv.runTape`/`runDefault` (result, unconsumed tape and log agree under every service, from every log, at any sufficient fuel, by T1), `Equiv.log`, `Equiv.wp`/`wlp`/`total`, `equiv_iff_denoteFuel` (the executable face at the allotted fuel) and `equiv_of_erase_eq`. Packet D3's T4 is an instance of this relation on the skeleton denotations. Says nothing about the host |

## Required semantic separations

1. **Service level, not primitive level.** An event names an operation of a family,
   its request and answer, a decision site, a region, a finalizer, or the outcome.
   The seventeen rc.112 primitives are not events of this alphabet.
2. **Masks are projections.** `project mask` is a filter; `m1` keeps operations,
   answers, failures and the outcome; `m2` adds decisions, regions and finalizers.
   `project m1 = project m1 ∘ project m2` is a theorem, and a fixture pair that agrees
   under `m1` and differs under `m2` is a required self-test.
3. **Outcome is annotation-blind and host-error-identity-blind** under `m1`:
   `(tag, reason tags in order, fail payload)`. This is a decision, recorded here,
   not an accident of the encoder (`FRAME-FB-STACK-ANNOTATION`, `FRAME-FB-HOST-ERROR`).
4. **Two tapes.** The choice tape answers `decide` sites by occurrence with a site
   check; the scheduler tape is the single-fiber preset in this phase. They are
   never reconciled here.
5. **Frontiers compare as frontiers.** Fuel and tape exhaustion end a trace with
   `frontier`; a host op budget ends it the same way. Neither is a failure.
6. **Layer build and teardown are outside the compared window.** Host traces carry
   phase sentinels; agreement covers the `run` phase only.
7. **Answers are recorded as typed.** The host proxy encodes an answer by the
   operation's declared answer spelling, so a `void` answer is unit whatever the
   host returns. Found on the first host run: rc.112's `Ref.set` returns the
   mutable ref at runtime under a declared `Effect<void>`; the untyped encoder
   died on it and the trace ended in `done {"failure":[]}`.
8. **Scheduler insensitivity is checked, not assumed.** Every golden runs twice on
   the host, at a large `MaxOpsBeforeYield` (zero yields required) and at the
   smallest value that progresses, which on rc.112 is 3 (the op is counted before
   the yield check and the yield wrapper costs two ops, so 1 and 2 loop forever).
   The service-level rows must be identical; the frame stream shows the yields.

## What agreement does not establish

Semantic preservation beyond the corpus; anything about primitives or frames;
interruption; concurrency or scheduler order; types (a separate receipt); layer
build, memoization and provided-scope semantics; host error identity, stack
annotations, defect payloads; termination; byte identity of the generated program;
and any statement about the host from a Lean theorem. These are the refusal rows
of `docs/LOWERING-COVERAGE.md`.

Packet D4 (2026-09-03) moves exactly one item on that list, and only half of it:
"anything about primitives or frames" now has a **Lean** half —
`Effect4.FrameSimulation.compile_simulates` relates the frame machine to
`interpret` on the compiled fragment, relative to an answer tape. The **host**
half does not move: no theorem relates a host row to a `FrameEvent`, and the
frame stream is still recorded and never compared. Interruption, concurrency,
types, layer build, host error identity, stack annotations, defect payloads,
termination and byte identity all stay exactly where they were.
