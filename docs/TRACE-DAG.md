# Trace agreement proof graph

Status: opened 2026-09-02 with the trace lane; every edge but `semantics` and
`bridges` closed the same day; those two are `required-open` by ruling for
this phase.

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
```

## Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | `Effects.Trace.Event`, `Trace.Mask`, `Trace.Val` frozen by `EffectsTest/Trace/TraceContract.lean` (lean4-effects v0.3.0, `test/contracts/trace.contract.md`) |
| construction | `required-closed` | `Family.Service.traced` and `Family.Service.tracedExcept` (v0.3.1); `X.traced`, `X.tracedExcept` emitted by `effect_signature`; receipts in `Effect4Test/Semantics/ObservationContract.lean` |
| laws | `required-closed` | `interpret_traced_fst`, `interpret_tracedExcept_fst`, `project_project`, `project_m2`, `agree_of_agree_m2`, all within `propext`/`Quot.sound` (`EffectsTest/Trace/AxiomReport.lean`) |
| flow-runner | `required-closed` | Flow v2 runner (`Effect4/Semantics/Runs.lean`: `plan`/`step`/`loop`, `FlowService`, `Frontier`, the decision tape `Effect4/Flow/Decision.lean`) with laws `run_checked_not_stuck`, `run_fuel_mono`, `step_choose_consumes_one`, `plan_checked` within the ceiling (`Effect4Test/Flow/RunnerAxiomReport.lean`); the straight-line embedding `Script.toFlow` (`Effect4/Target/TypeScript/ScriptFlow.lean`) is admitted by `Effects.admit`; the internal oracle: `generated/traces/flow/*.empty.tsv` (face `lean-flow`) agree with the traced-service goldens under `m2` (`Generate.lean oracle`, part of `scripts/check-trace-goldens.sh`; planted mutant 4/4) |
| semantics | `required-open` | no simulation theorem in this phase; agreement is executable evidence under a mask, never a denotation |
| representation | `required-closed` | TSV wire form rendered only in `Effect4/Target/TypeScript/Trace.lean` (exact-module admission); no `String` in the alphabet |
| counterexamples | `required-closed` | `EF-TRACE-CE-001..003` (lean4-effects), `E4-SEM-CE-008..009`, `E4-TARGET-CE-009..010`; planted mutants in `scripts/test-trace-goldens-gate.sh` (3/3) |
| bridges | `required-open` | `FrameEvent.toTrace`, `Event.toTrace` in `Effect4/Target/TypeScript/Simulation.lean` (P-T11); until then the primitive stream (`frames`) is not evidence |
| targets | `required-closed` | `harness/trace/check.sh`: fixture drift for the straight-line module (`fixture.ts`) and the dispatch-form module (`flow-fixture.ts`, `Effect4/Target/TypeScript/FlowLower.lean`, ruling R7), four host gates, every golden under every mask at a large yield threshold and at the rc.112 floor of 3 (the flow goldens through `flow-tail.ts` with the `Decisions` service answering from the golden's tape), type receipts from `tsc.original` for both modules; region programs (`Effect4/Target/TypeScript/RegionLower.lean`: `Effect.scoped`, `Effect.onExit`, `Effect.acquireRelease`, never `try/finally`) run with a `Regions` service reporting `enter`, `leave` and `finalizer` with the exits the host handed them; receipts under `harness/trace/receipts/` and `receipts/flow/` |
| trust | `required-closed` | axiom receipts for every trace law; gate exemptions for the renderer, the DSL and the numerator only; `scripts/test-trust-gate.sh` green |
| coverage | `required-closed` | `generated/lowering-coverage.tsv` (nineteen rules: eight straight-line `checked`, eight dispatch-form `covered`, three region `checked` by the property loop `generated/lowering-property.tsv`: 200 generated flows, 1277 host runs, 276 frontiers, 318 sites both ways, 3/3 planted lowering mutants caught), `scripts/check-lowering-coverage.sh`, planted mutants (4/4) |

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
