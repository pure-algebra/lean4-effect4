# Binary raceFirst representative contract

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence: `Effect4/Concurrency/Race.lean`

Lean battery: `Effect4Test/Concurrency/RaceRepresentativeContract.lean`

Counterexamples: `E4-CONC-CE-008` through `E4-CONC-CE-011`

Red verifier: `scripts/check-race-representative-red.sh`

Proof graph: `docs/RACE-DAG.md`

## Claim boundary

This packet freezes one binary first-completion race, called `raceFirst`.  It
coordinates two existing fibers inside one existing scheduler machine.  Its
only new semantic fact is which contender was selected.  Every child
transition, interruption, mask, cleanup state, and event delegates to the
proved Fiber/scheduler/interruption calculus.

This packet does not define first-success `race`, `raceAll`, success/failure
classification, effect syntax, scopes, supervision, structured concurrency,
fairness, host execution, TypeScript compatibility, or generated code.  The
terminal alphabet `τ` is opaque.  In particular, no predicate in this packet
can ask whether a terminal observation is a success.

## Existing-type disposition

| Need | Required owner and spelling | Disallowed duplicate |
| --- | --- | --- |
| three roles and selected winner | `FiberId` | `RaceId`, `RaceSide` |
| child state | `FiberState τ` | race-local child state |
| machine and trace | `Machine τ`, `Event τ`, `Trace τ` | `RaceMachine`, `RaceEvent`, race trace |
| cancellation | `InterruptBoundary τ`, `InterruptMask`, `SchedulerDecision.requestInterrupt` | race-local cancellation outcome |
| cleanup | `CleanupState`, `Machine.cleanupState`, `cleanupCount`, `cleanupEventIds` | race cleanup carrier or counter |
| terminal result | caller-supplied `τ` | `RaceOutcome`, `RaceExit` |
| scheduler failure | `SchedulerRefusal`, wrapped by `RaceRefusal.scheduler` | copied scheduler refusal cases |

The following additions are justified because the existing calculus does not
contain them:

- `RaceSpec` identifies coordinator, left contender, and right contender;
- `RaceState τ` adds one `Option FiberId` winner to one `Machine τ`;
- `RaceDecision τ` is the sum of an existing scheduler decision and an
  explicit winner selection;
- `RaceRefusal τ` classifies invalid race-level choices without confusing
  them with scheduler failures or tape exhaustion; and
- race step/replay result envelopes retain race state on every arm.

## Frozen carriers

```lean
structure RaceSpec where
  coordinator : FiberId
  left : FiberId
  right : FiberId

structure RaceState (τ : Type u) where
  machine : Machine τ
  winner : Option FiberId

inductive RaceDecision (τ : Type u)
  | scheduler (decision : SchedulerDecision τ)
  | selectWinner (winner : FiberId)

abbrev RaceTape (τ : Type u) := List (RaceDecision τ)

inductive RaceRefusal (τ : Type u)
  | scheduler (refusal : SchedulerRefusal)
  | schedulerOutsideRace (decision : SchedulerDecision τ)
  | winnerSelectionRequired
  | winnerNotContender (winner : FiberId)
  | winnerNotDone (winner : FiberId)
  | winnerAlreadySelected (winner : FiberId)
  | raceSettled (winner : FiberId)

inductive RaceStepResult (τ : Type u)
  | advanced (state : RaceState τ)
  | refused (refusal : RaceRefusal τ) (state : RaceState τ)

inductive RaceReplayResult (τ : Type u)
  | settled (result : τ) (state : RaceState τ)
  | refused (refusal : RaceRefusal τ) (state : RaceState τ)
  | frontier (state : RaceState τ)
```

Constructor order, field order, namespaces, and theorem propositions are
frozen by the Lean battery.  Binder names may differ.  A Lean environment
gate additionally requires `RaceSpec` and `RaceState` to be structures with
their sole `mk` constructors and exact field order, and requires
`RaceDecision`, `RaceRefusal`, `RaceStepResult`, and `RaceReplayResult` to be
inductives with exactly the listed constructor sets.  The same environment
gate rejects the six named duplicate carriers and every Race-module
declaration carrying a first-success or `raceAll` spelling; this is declaration
inspection, not a source-text convention.

## Admission and observations

`RaceSpec.IsContender spec id` means `id = spec.left ∨ id = spec.right`.
`spec.loser spec.left = spec.right` and conversely.  `RaceSpec.ValidIn spec
machine` requires all three role IDs to be pairwise distinct, both contenders
to be present, and the resolved coordinator to be present and active.  The
coordinator condition makes the delegated interruption request an admitted
scheduler action rather than an arbitrary wrapper around a missing requester.
`validIn_iff` freezes that conjunction independently of the structure
constructor.

`RaceState.ContenderDone spec state id` requires that `id` is a contender and
its existing `FiberState.status` is `.done`.  `RaceState.NeedsWinner` holds
exactly when no winner has been recorded and either contender is done.

`RaceState.WellFormed spec state` contains exactly four obligations:

1. `state.machine.WellFormed`;
2. `spec.ValidIn state.machine`;
3. a recorded winner is a done contender; and
4. if the selected loser remains active, it is masked with a pending
   interruption.

`wellFormed_iff` freezes exactly those four fields, so changing both the
structure and its consumers cannot silently move the admission boundary.

The fourth field is the cancellation-started invariant.  An unmasked active
loser is moved to finalization by selection; a masked active loser stays
active only while the interrupt is pending.  Finalizing and done losers need
no synthetic interruption step.

`RaceState.Settled spec state result` requires an explicit contender winner,
that winner's stored terminal observation to equal `result`, and both
contenders to be `.done` with cleanup `.done`.  `settledResult?` is the pure
projection and `settledResult_eq_some` proves its exact agreement with this
judgment.  The battery separately freezes a field-level `settled_iff`, so an
implementation cannot make both the predicate and projection agree on an
unrelated condition.

## Refusal classification

The arms are disjoint by construction and have these meanings:

| Arm | Meaning |
| --- | --- |
| `scheduler refusal` | an allowed delegated scheduler decision reached an existing scheduler refusal |
| `schedulerOutsideRace decision` | the embedded decision targets another fiber or is not admitted in the current race phase |
| `winnerSelectionRequired` | a contender is done, so more child scheduling would erase first-completion order |
| `winnerNotContender id` | the explicit choice names neither child |
| `winnerNotDone id` | the named contender has not completed |
| `winnerAlreadySelected id` | winner selection was attempted a second time |
| `raceSettled id` | direct stepping was attempted after settlement |

`RaceReplayResult.frontier` is deliberately absent from this table.  A finite
tape ending before settlement is live evidence that another choice is needed,
not an invalid decision.

## Operational semantics

```lean
raceStepEval : InterruptBoundary τ -> RaceSpec -> RaceState τ ->
  RaceDecision τ -> RaceStepResult τ

RaceStep boundary spec before decision result : Prop :=
  result = raceStepEval boundary spec before decision

raceReplayEval : InterruptBoundary τ -> RaceSpec -> RaceState τ ->
  RaceTape τ -> RaceReplayResult τ

RaceRuns boundary spec initial tape result : Prop :=
  initial.WellFormed spec /\
  result = raceReplayEval boundary spec initial tape
```

The helper `RaceStepResult.fromScheduler before` preserves the current winner,
updates the wrapped machine on advancement, and wraps a scheduler refusal.
`fromWinnerSelection winner before` records the winner only when delegated
loser interruption advances; if the delegated scheduler step refuses, the
winner remains unselected.  All four advanced/refused helper equations are
frozen independently; the delegation laws therefore cannot be satisfied by
arbitrary helper definitions.

### Before selection

When neither contender is done, the following existing scheduler decisions
are in scope only when they target a contender: `schedule`, `enterMask`,
`exitMask`, `complete`, and `cleanup`.  Their meaning is exactly `stepEval`.
`join` and direct `requestInterrupt` are outside this bounded operator.
`beforeSelection_iff` enumerates exactly those five forms and a positive
left-contender theorem inhabits every form, preventing an empty scope from
satisfying delegation vacuously.  `afterSelection_iff` enumerates exactly
loser `exitMask` and loser `cleanup`.

After any contender becomes `.done`, an embedded scheduler decision refuses
with `winnerSelectionRequired`.  This forces the next advancing race decision
to identify the observed first completion.  `selectWinner id` refuses unless
`id` is a done contender.

If the selected loser's existing status is active, selection delegates to:

```lean
stepEval boundary before.machine
  (.requestInterrupt spec.coordinator (spec.loser winner))
```

If the loser is already finalizing or done, selection records the winner and
leaves the machine unchanged.

### After selection

Before settlement, only `.exitMask loser` and `.cleanup loser` are in scope.
Both continue to delegate to `stepEval`.  This is enough for the only active
post-selection case: a masked loser with a pending interruption first unmasks
into interruption finalization and then cleans up.  A finalizing loser cleans
up directly.  A done loser needs no further child step.

### Replay

Replay checks `settledResult?` before reading the next tape element.  Therefore
a settled prefix ignores every suffix.  If no settlement exists and the tape
is empty, replay returns `frontier state`.  Otherwise one advanced step
recurses and one refused step stops with the retained state.

## Theorem burden

The exact Lean battery freezes:

1. constructors, projections, aliases, admission fields, passive case
   receipts, and exact iff equations for contender membership, contender
   completion, winner demand, phase scope, and settlement; the state projection
   of every step and replay constructor is fixed to its carried state;
   structure/inductive metadata gates freeze every constructor set, while
   `RaceSpec.ext_iff`, `RaceState.ext_iff`, and exhaustive step/replay case
   receipts freeze the public observation boundaries;
2. exact step and run graph equations;
3. exact scheduler delegation and race-level refusal equations;
4. exact active- and inactive-loser winner-selection equations;
5. exact settled, empty-frontier, advanced-cons, and refused-cons replay
   equations;
6. step and fixed-tape determinism;
7. step/replay totality and preservation of race well-formedness;
8. selected winner is a done contender, is selected once, remains stable, and
   retains its terminal observation from a well-formed pre-state;
9. an active loser selection emits the existing interruption request and
   post-selection advancement is loser-only;
10. settlement implies both child cleanups ran exactly once and are present
    in the existing cleanup-event projection;
11. unrelated fiber state is framed;
12. a settled prefix ignores its remaining tape;
13. a masked pending loser with an empty tape is a frontier;
14. an inhabited finite settling run; and
15. one admitted tie state with distinct left- and right-winner tapes.

The last two results prevent a vacuous or unreachable relation.  None of these
laws asserts liveness for arbitrary tapes.

## Counterexamples

The standalone witness file imports Scheduler, not Race, so all four attacks
compile while production remains empty.

- `E4-CONC-CE-008`: erase the winner projection from two tie resolutions and
  the scheduler states become identical although the selected IDs differ.
- `E4-CONC-CE-009`: the smallest completion tape `[failed, succeeded]` has a
  different first completion and first success.  This packet freezes only the
  former.
- `E4-CONC-CE-010`: the winner terminal is observable while the loser remains
  finalizing with pending cleanup; the exact trace contains only the winner's
  cleanup event.
- `E4-CONC-CE-011`: a masked pending loser has an advancing `exitMask` step;
  treating that point as settled or refused destroys a live continuation.

## Acceptance

The breaker phase is complete when the witness file compiles, production
dependencies compile, the contract fails for the named missing Race
declarations, all four stable rows occur exactly once in both ledgers, no
forbidden proof escape appears, each witness has an axiom-free `#print axioms`
receipt, the green witness module is imported by `Effect4Test.lean`, and the
known-red list contains this contract module exactly once.  Other concurrent
breaker lanes may have their own known-red rows.  No production implementation
or assurance closure is part of this packet.

The later builder phase removes the known-red row only after the fixed battery
is green.  Full promotion additionally requires the graph closure described in
`docs/RACE-DAG.md`; that later work is not authorized by this breaker packet.
