# Trace agreement proof graph

Status: opened 2026-09-02 with the trace lane; `semantics` and `bridges` are
`required-open` by ruling for this phase.

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
   +--> FLOW-RUNNER (Effect4/Semantics/Runs.lean)        [after Flow v2]
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
| identity | `required-open` | `Effects.Trace.Event`, `Trace.Mask`, `Trace.Val` frozen by `EffectsTest/Trace/TraceContract.lean` (P-T1) |
| construction | `required-open` | `Family.Service.traced`; `X.traced` emitted by `effect_signature` (P-T1b) |
| laws | `required-open` | `interpret_traced_fst`, `project_project`, `project_full`, `m1_refines_m2` (P-T1) |
| semantics | `required-open` | no simulation theorem in this phase; agreement is executable evidence under a mask, never a denotation |
| representation | `required-open` | TSV wire form rendered only in `Effect4/Target/TypeScript/Trace.lean` (exact-module admission); no `String` in the alphabet |
| counterexamples | `required-open` | `EF-TRACE-CE-001..003` (lean4-effects), mask-drift row `E4-SEM-CE-*` (P-T1b) |
| bridges | `required-open` | `FrameEvent.toTrace`, `Event.toTrace` in `Effect4/Target/TypeScript/Simulation.lean` (P-T11); until then the primitive stream is not evidence |
| targets | `required-open` | `harness/trace/check.sh`: fixture drift, four host gates, all masks (P-T3, P-T4) |
| trust | `required-open` | axiom receipts for the P-T1 lemmas; gate exemptions for renderer and drivers only |
| coverage | `required-open` | `generated/lowering-coverage.tsv` with its drift gate and planted mutants (P-T5) |

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

## What agreement does not establish

Semantic preservation beyond the corpus; anything about primitives or frames;
interruption; concurrency or scheduler order; types (a separate receipt); layer
build, memoization and provided-scope semantics; host error identity, stack
annotations, defect payloads; termination; byte identity of the generated program;
and any statement about the host from a Lean theorem. These are the refusal rows
of `docs/LOWERING-COVERAGE.md`.
