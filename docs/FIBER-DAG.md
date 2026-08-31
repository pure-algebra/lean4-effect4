# Fiber representative proof DAG

Status: breaker-frozen, RED, 2026-08-31

This document is the bounded ownership and proof graph for the first
Fiber/scheduler/interruption representative. It is not a concurrency runtime,
an Effect compatibility claim, or a cutover approval. Production remains
unchanged until the red contract has an independently implemented green proof
graph.

## Scope

The representative contains only the polynomial information needed to state
and test forked-fiber lifecycle observations, relative to an externally
admitted terminal alphabet `τ`:

- nominal `FiberId` values;
- fiber lifecycle status parameterized by an externally owned terminal
  observation `τ`;
- interruption masks and pending requests;
- cleanup lifecycle and execution count;
- explicit scheduler decisions collected into a finite tape;
- an observable event trace;
- one explicit `Machine.WellFormed` admission predicate over raw machines;
- a one-decision transition relation and finite taped runs.

The concurrency layer adds no effect syntax, callback, Promise, host task,
continuation, clock, priority, work stealing, daemon policy, structured scope,
supervision tree, result payload, or fairness premise. `Race.lean` and
`Supervision.lean` remain empty breadth stubs.

This does not claim that arbitrary `τ` is first-order: `τ := Nat -> Nat` is a
legal Lean instantiation. Full reification is discharged later by the terminal
alphabet's `Semantics.Exit` and codec admission, without minting a second
terminal carrier here.

## Required semantic separations

Concurrency owns neither `Cause`/`Exit` nor the shared `Semantics.Frontier`
alphabet. `FiberState τ`, `Machine τ`, decisions, and events are parameterized
by a terminal observation type `τ`. `InterruptBoundary τ` supplies only the
distinguished interruption observation; a later `Semantics.Exit`
instantiation must prove that typed failure, defect, and interruption remain
distinct.

`SchedulerRefusal` remains a separate carrier for an invalid taped decision.
Finite tape exhaustion is the separate `ReplayResult.frontier machine` arm,
with no second Frontier carrier minted in Scheduler. Cleanup state and trace
remain outside terminal observations, refusals, and frontier so none of these
arms erases whether cleanup ran.

## Declaration and proof graph

```text
FIBER-L0-ID --------------------------.
FIBER-L0-PASSIVE-ALPHABETS ---------. |
                                      v v
FIBER-L1-STATE --> FIBER-L1-ADMISSION --> FIBER-L2-STEP
                                               |       |
FIBER-L1-DECISION-TAPE --------------'       |
                                              v
                                      FIBER-L3-RUNS
                                      /    |     \
                                     v     v      v
                         FIBER-L4-DETERMINISM   FIBER-L4-JOIN
                                               FIBER-L4-INTERRUPT
                                               FIBER-L4-CLEANUP
                                      \      |      /
                                       v     v     v
                                  FIBER-L5-COUNTEREXAMPLES
                                             |
                                             v
                                  FIBER-L6-HOST-EVIDENCE (later)
```

`FIBER-L0-ID` and `FIBER-L0-PASSIVE-ALPHABETS` close with local constructor,
decidable-equality, and case-exhaustion receipts. They do not receive invented
proof graphs. `FIBER-L1` through `FIBER-L5` form one operational and cleanup
proof graph because changing any of them can change replay, join, interruption,
or cleanup meaning.

## Node ownership

| Node | Production owner after dispatch | Required receipt |
| --- | --- | --- |
| `FIBER-L0-ID` | `Effect4/Concurrency/Fiber.lean` | exact structure and `DecidableEq` |
| `FIBER-L0-PASSIVE-ALPHABETS` | `Fiber.lean`, `Interrupt.lean`, `Scheduler.lean` | constructor census and exhaustive cases |
| `FIBER-L1-STATE` | `Effect4/Concurrency/Fiber.lean` | first-order fields parameterized by `τ`; terminal, mask, pending-request, cleanup projections |
| `FIBER-L1-ADMISSION` | `Effect4/Concurrency/Scheduler.lean` | unique IDs; unique, closed cleanup-event history agreeing with per-fiber counts; lifecycle coherence; closed waiting targets |
| `FIBER-L1-DECISION-TAPE` | `Effect4/Concurrency/Scheduler.lean` | every scheduler choice is explicit data |
| `FIBER-L2-STEP` | `Scheduler.lean` and `Interrupt.lean` | exact relational one-decision semantics with explicit refusal and `InterruptBoundary τ` |
| `FIBER-L3-RUNS` | `Effect4/Concurrency/Scheduler.lean` | total admitted finite replay recursively tied to `Step`, with distinct finished/refused/frontier arms |
| `FIBER-L4-DETERMINISM` | `Effect4/Concurrency/Scheduler.lean` | fixed-tape uniqueness only |
| `FIBER-L4-JOIN` | `Effect4/Concurrency/Scheduler.lean` | operational laws over `Step`: blocking before `.done`; repeatable, cleanup-free observation only after cleanup |
| `FIBER-L4-INTERRUPT` | `Effect4/Concurrency/Scheduler.lean` | operational laws over `Step`: immediate delivery when unmasked, deferral when masked, delivery on unmask, and no completion that erases a pending request |
| `FIBER-L4-CLEANUP` | `Effect4/Concurrency/Scheduler.lean` | operational laws over `Step`/`Runs`: count monotonicity, unique observable cleanup events, trace/count agreement, terminal preservation, and cleanup on a finished run |
| `FIBER-L5-COUNTEREXAMPLES` | `Effect4Test/Counterexamples/Concurrency/FiberRepresentative.lean` | seven proved finite witnesses and axiom report |
| `FIBER-L6-HOST-EVIDENCE` | later Effect TypeScript conformance packet | direct runtime/type receipts plus auxiliary language-service diagnostics |

## Graph-edge ledger

The graph-bearing owner is `FIBER-PG-REPRESENTATIVE`. Passive leaves link to
this graph; they do not receive duplicate graphs.

| Edge | Breaker state | Closure evidence |
| --- | --- | --- |
| identity | `required-open` | exact public declaration snapshot plus the type rows in the owning contract |
| construction | `required-open` | constructors, projections, passive case receipts, and `Machine.WellFormed` admission |
| semantics | `required-open` | admitted-total `Step`, exact `stepEval` clauses and trace deltas, `Runs` recursion through `Step`, projection equations, positive decision-clause coverage, and distinct replay arms |
| laws | `required-open` | the fixed-tape, join, interruption/mask, and cleanup theorem spine |
| representation | `not-applicable` | this representative claims no serialization, normalization, or round trip |
| counterexamples | `required-open` | all seven witnesses exist, but their repairs cannot close before implementation |
| bridges | `not-applicable` | no embedding or compatibility bridge is claimed in this packet |
| targets | `not-applicable` | TypeScript/runtime/language-service evidence is deliberately a later graph node |
| trust | `required-open` | public theorem `#print axioms` receipts after implementation |
| coverage | `required-open` | the frozen contract must join every exported declaration to one owner route |

## Proof closure required before implementation promotion

The representative proof graph closes only when all of these are green in the
same revision:

1. exact public declarations match the frozen Lean contract;
2. passive finite alphabets have local exhaustive-case receipts;
3. machine admission and its decidability receipt are present;
4. the operational step and run relations are present;
5. admitted `Step` and finite replay are total, `Step` is extensionally fixed
   by exhaustive `stepEval` equations, machine projections are fixed, every
   decision constructor has an inhabited positive clause, and one
   admitted nonempty finite run is proved finished;
6. exact nil/cons equations tie `Runs` to `Step`, with nil tapes classified as
   finished or exhausted-frontier;
7. fixed-tape determinism is kernel checked;
8. join-before-done blocking, including finalization, plus post-cleanup join
   agreement and repeat observation are kernel checked;
9. all three interruption/mask laws are kernel checked;
10. atomic cleanup, the `transition_cleanupEventIds` equation, stepwise
    cleanup-count monotonicity, unique/closed cleanup history, trace/count
    agreement, terminal preservation, and finished-run safety are kernel checked;
11. all seven registered attacks remain executable and rejected by the repaired
   laws;
12. `#print axioms` is recorded for every public law;
13. the complete project test suite passes with no `sorry` or `admit`.

This closes only the representative operational proof graph. It does not close
the Effect concurrency category, scheduler cutover, TypeScript generation, or
host compatibility.

## Determinism and nondeterminism ruling

The full semantics is relational over explicit scheduler decisions. An
untaped state may have several legal next steps. Determinism is claimed only
after the complete finite decision tape is fixed. The tape records order,
including interruption versus completion. A finite exhausted tape returns a
`ReplayResult.frontier` arm; it does not fabricate a terminal observation or
refusal.

No theorem in this packet mentions fairness, starvation freedom, eventual
completion, or an infinite schedule. Those are outside the representative.

The implication-only spine is insufficient: empty `Step` and `Runs` relations
satisfy uniqueness and every safety implication. `E4-CONC-CE-006` proves that
failure. Admission-qualified total steps and replay, exhaustive `stepEval`
equations and trace deltas, exact replay recursion through `Step`, fixed
projection equations, inhabited positive decision cases, exact nil-tape
classification, and a finite finished witness are therefore part of the
operational graph rather than optional examples.

## External evidence boundary

`PORT-MANIFEST.md` pins the Effect runtime and records the installed tsgo and
language-service evidence. Those sources inform later host fixtures, but they
do not prove this Lean model. Host closure requires direct runtime and type
observations; language-service diagnostics are an auxiliary gate and cannot
turn an unknown Effect symbol into a passing result.
