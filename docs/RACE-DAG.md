# Binary raceFirst representative proof DAG

Status: breaker-frozen, RED, 2026-08-31

This is the bounded ownership and proof graph for one binary `raceFirst`
representative.  It extends the proved Fiber/scheduler/interruption model.  It
does not define first-success racing, `raceAll`, host execution, fairness, or a
new terminal-result algebra.

## Reuse ruling

Race is a coordinator over the existing concurrency calculus, not a second
calculus beside it.

| Race need | Reused owner | New Race data |
| --- | --- | --- |
| coordinator, contenders, selected winner, loser | `FiberId` | none |
| child lifecycle and terminal observation | `FiberState τ` | none |
| fibers plus cleanup trace | `Machine τ` | `RaceState τ` wraps one machine and one optional winner |
| interruption masks and cleanup | `InterruptMask`, `InterruptBoundary τ`, `CleanupState` | none |
| executable child transitions | `SchedulerDecision τ`, `stepEval`, `Step` | `RaceDecision.scheduler` embeds them |
| nondeterministic tie resolution | none | `RaceDecision.selectWinner` |
| stopped invalid choices | `SchedulerRefusal` | `RaceRefusal.scheduler` plus race-domain refusals |
| finite depletion | existing frontier pattern | `RaceReplayResult.frontier`; no Frontier type |
| observable cleanup | `Event τ`, `Trace τ` | no Race event or trace |

Forbidden duplicate production carriers are `RaceId`, `RaceSide`,
`RaceMachine`, `RaceEvent`, `RaceOutcome`, and `RaceExit`.  There is no result
success test in this packet: `τ` stays opaque.

## Declaration DAG

```text
proved FiberId/FiberState/InterruptBoundary/Machine/stepEval
                         |
                         v
RACE-L0-SPEC --------> RACE-L1-STATE-ADMISSION
      |                         |
      v                         v
RACE-L1-DECISION --------> RACE-L2-STEP
                                  |
                                  v
                           RACE-L3-REPLAY
                           /      |      \
                          v       v       v
                 RACE-L4-WINNER  LOSER  FRAME
                           \      |      /
                            v     v     v
                      RACE-L5-COUNTEREXAMPLES
                                  |
                                  v
                       RACE-L6-HOST (later)
```

| Node | Owner | Required result |
| --- | --- | --- |
| `RACE-L0-SPEC` | `Effect4/Concurrency/Race.lean` | three distinct existing fiber IDs; active resolved coordinator; both contenders present; contender and loser equations |
| `RACE-L1-STATE-ADMISSION` | same | one existing machine plus optional winner; machine admission, valid spec, done selected winner, cancellation-started selected loser |
| `RACE-L1-DECISION` | same | embedded scheduler choice or explicit winner choice; exact pre/post-selection scope predicates |
| `RACE-L2-STEP` | same | pure total evaluator and its exact graph relation; scheduler delegation and winner-selection equations |
| `RACE-L3-REPLAY` | same | settlement checked before tape consumption; settled/refused/frontier remain distinct |
| `RACE-L4-WINNER` | same | first done contender must be selected before more child progress; choice is stable and terminal-preserving |
| `RACE-L4-LOSER` | same | active loser is interrupted by the coordinator; masked delivery remains live; return waits for cleanup |
| `RACE-L4-FRAME` | same | every non-contender fiber is unchanged |
| `RACE-L5-COUNTEREXAMPLES` | `Effect4Test/Counterexamples/Concurrency/RaceRepresentative.lean` | `E4-CONC-CE-008` through `011` compile independently of Race production |
| `RACE-L6-HOST` | later packet | not part of this graph closure |

`RaceSpec`, `RaceDecision`, and `RaceRefusal` are finite or passive leaves.
They receive constructor/equation receipts and exact ownership rows, not
ceremonial proof graphs.  `RaceState.WellFormed`, `RaceStep`, `RaceRuns`, and
settlement carry the graph because changing any one changes race meaning.

## Decision-tape extension

`RaceTape τ = List (RaceDecision τ)` where a decision is either an embedded
`SchedulerDecision τ` or `selectWinner winner`.

Before selection:

1. scheduler decisions may schedule, mask, unmask, complete, or clean up only
   the two contenders;
2. join and direct interruption are outside this bounded race;
3. as soon as a contender is `.done`, every scheduler decision refuses with
   `winnerSelectionRequired`; and
4. `selectWinner` must name a done contender.

Selection is the nondeterministic observation.  If both contenders are already
done, two different one-choice tapes retain the tie rather than hiding it in a
map iteration order.  If the loser is active, selection delegates exactly to
`requestInterrupt coordinator loser`.  An unmasked loser begins finalization;
a masked loser retains a pending interruption and requires an explicit
`exitMask` decision.

After selection, the only embedded decisions in scope are `exitMask loser`
and `cleanup loser`.  Replay returns `settled result` only after the selected
winner and loser are both `.done` with cleanup complete.  A depleted tape
before that point is `frontier`, including the masked-pending case.  It is not
a refusal.

## Proof graph edges

Graph owner: `RACE-PG-BINARY-FIRST-COMPLETION`.

| Edge | Breaker state | Closure evidence |
| --- | --- | --- |
| identity | `required-open` | exact public signature snapshot; structure/inductive constructor metadata; extensionality iff receipts; environment-level duplicate and first-success fence |
| construction | `required-open` | exact `validIn_iff`, `wellFormed_iff`, contender/loser equations, and no-winner requirement in `needsWinner_iff` |
| semantics | `required-open` | exact graph equations for step and replay; settlement-before-consumption |
| laws | `required-open` | fixed-tape determinism, invariant preservation, winner/loser/cleanup/frame spine |
| representation | `not-applicable` | no serialization or normalization claim |
| counterexamples | `required-open` | four executable attacks plus production repair links |
| bridges | `required-open` | exact delegation to existing `stepEval`; no copied scheduler semantics |
| targets | `not-applicable` | no TypeScript, runtime, or language-service claim |
| trust | `required-open` | later axiom receipts for every public theorem |
| coverage | `required-open` | later generated join over every exported Race declaration |

## Exact law spine

The Lean contract freezes these families:

- exact `RaceStep = graph raceStepEval` and admitted `RaceRuns = graph
  raceReplayEval`;
- field-level iff equations for contender membership, contender completion,
  winner demand, pre/post-selection scheduler scope, and settlement;
- exact extensionality iff receipts for both structures and exhaustive case
  receipts for both result envelopes;
- Lean environment checks for the two exact structures, four exact inductives,
  forbidden duplicate carriers, and first-success declarations;
- non-vacuous coverage of all five allowed pre-selection scheduler forms;
- exact advanced/refused equations for both scheduler-lifting helpers;
- before-selection delegation, winner-required blocking, outside-scope
  refusal, post-selection loser-only delegation, and settled refusal;
- invalid/already-selected/not-done winner equations;
- active-loser selection delegates to scheduler interruption; inactive loser
  selection records the winner without changing the machine;
- replay settlement, empty-frontier, advanced-cons, and refused-cons equations;
- one-step and fixed-tape determinism, totality, and invariant preservation;
- winner contender/done, once-only selection, winner and winner-terminal
  stability, with terminal stability requiring a well-formed pre-state;
- active loser interruption, selected loser progress restriction, both-child
  cleanup at settlement, and one cleanup event per child;
- unrelated-fiber frame;
- settled-prefix suffix irrelevance;
- a masked pending loser with empty tape is a frontier; and
- one finite settling run plus two distinct tie-resolution tapes.

No theorem claims untaped determinism, eventual settlement, fairness,
starvation freedom, first success, host equivalence, or full concurrency
closure.

## Counterexample closure

| Stable ID | Smallest retained attack | Forced repair |
| --- | --- | --- |
| `E4-CONC-CE-008` | same scheduler machine, distinct chosen winners | explicit winner in state and tape |
| `E4-CONC-CE-009` | failed completion followed by successful completion | keep this packet at first completion; do not silently substitute first success |
| `E4-CONC-CE-010` | winner terminal exists while loser is finalizing | settlement waits for loser cleanup |
| `E4-CONC-CE-011` | masked pending loser can still unmask and finalize | tape depletion is frontier, not refusal or settlement |

## Promotion gate

Implementation may be promoted only when the fixed contract is green, the
four standalone witnesses remain green with axiom-free receipts and root-module
closure, the full package builds, every public law has a kernel dependency
receipt, the environment declaration fence reacts, and all applicable graph
edges are mechanically joined.  This gate closes only the binary
first-completion representative.
