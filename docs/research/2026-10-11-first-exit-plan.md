# First-exit race repair plan

The current timeout form races waiting fibers instead of observing the attempt and timer directly.
The owner selects retries after declared timeout-form failures and retains the four-attempt bound.
The implementation repair separately adds the pinned runtime's first-exit selection.

## Contract and placement

Concept: reactive-scheduling. Requirement: R4.
The completion worker accepts the first observed entrant exit unchanged and keeps it while later entrants exit.
The worker requests interruption of remaining entrants.
The existing settlement path waits for their completion before publishing the accepted exit to the parent.
The semantic cut is `Observer.raceCallback` at the entrant's published exit.
The source is `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, `raceAllFirst`, beginning at 1535.

Concept: translation-simulation. Requirement: R10.
The consumer is the timeout form and the scenario's corrected retry claim.
The corrected observation records a completed timeout form's attempt identity, selected entrant identity and returned exit.
Reply application stays separate from the timeout form's returned exit.
The two controls retain success and nonretryable replies followed by a yielding attempt and a timer winner.

Concept: scope-lifetime-finalization. Requirement: R11.
The consumer is the first-exit race settlement path.
Its property is cleanup before publication, using the existing masked interrupt-and-await path.
The change establishes no fairness, progress, deadline ordering, or host/compiler agreement by itself.

## Representation and ownership

Use the existing `Eff` free object and the existing machine race record.
Add the data constructor `ActionTerm.raceAllFirst` with the same entrant child signature as `raceAll`.
Keep the old constructor, its arity, and its first-success meaning.
Add `WithFiberAction.raceAllFirst` beside the old machine action.
Add a data race mode to the machine race record, defaulting to first success.
Keep frozen `Supervision.raceComplete` as the first-success worker.
Add a first-exit worker that retains arbitrary `Cause` data without decoding or rebuilding it.
Record the selected entrant identity at its observer callback.
Reuse the existing registration and settlement paths.

The generated folds and lifts come from the source signature.
The new syntax's arrows are compilation, an interpreter map, and generated traversal folds.
No closure, Lean function, or runtime object enters stored syntax.

## Slices and checks

1. Compile the machine completion worker and its actual-consumer laws.
2. Compile the machine action and observer dispatch with focused tests.
3. Regenerate the syntax families and compile admission, compilation, codec, printing and reading.
4. Replace the derived timeout form and record completed timeout outcomes.
5. Preserve the old retry proposition and its retained Lean counterexample.
6. Build the touched modules and run their exact `axiom_audit`.

The coordinator then runs the reached behaviour gates: `check-truth`, `check-host-protocol`, `check-target`, and `check-ts-reader`.
Machine changes also reach `check-native`, `check-compiler`, and `check-ocaml` where those routes consume the new action.
Codec changes reach the program corpus and reader controls.
The coordinator records any narrower profile refusal rather than claiming unsupported target execution.
No first-success contract changes in this plan.

## Frozen interface proposal

```lean
inductive Effect4.Supervision.RaceMode
  | firstSuccess
  | firstExit

def Effect4.Supervision.raceCompleteFirst
  (s : RaceAllState β ε δ ι α) (child : FiberId) (exit : Exit β ε δ ι α) :
  RaceAllState β ε δ ι α

def Effect4.Supervision.raceCompleteWith
  (mode : RaceMode) (s : RaceAllState β ε δ ι α)
  (child : FiberId) (exit : Exit β ε δ ι α) : RaceAllState β ε δ ι α

-- Existing source signature gains one constructor.
ActionTerm.raceAllFirst (entrants : Effs Op)

-- Existing machine action gains one constructor.
WithFiberAction.raceAllFirst (entrants : List κ) (site : Option (List Nat) := none)

-- Existing machine race gains defaulted fields.
Race.mode : Supervision.RaceMode := .firstSuccess
Race.selected : Option FiberId := none
```

`raceCompleteFirst` leaves an unknown child unchanged.
If the first live child exits, it removes that child and accepts that exact exit.
It sets cleanup-needed from the remaining live children and clears prior cleanup registration data.
For later callbacks, it delegates to the existing worker, which keeps the accepted exit.
`raceCompleteWith .firstSuccess` is exactly the existing `raceComplete`.
`raceCompleteWith .firstExit` is exactly `raceCompleteFirst`.

The callback sets `selected` only for first-exit mode and only at the first acceptance.
First-success callbacks retain the default `selected` field.
This restriction keeps existing first-success machine equations unchanged.
`beginRace` receives an optional mode after its existing optional site.
It defaults that mode to first success.

The machine retains race entries after settlement and cancellation.
The source assigns `races` only at initial construction, append, and `updateRace`.
No new trace event is needed.
Read the selected child from the race and its source-list site from persistent fork records.
The first entrant has the attempt role; the second has the timer role.
The selected exit is `race.state.accepted`.

Acceptance precedes loser cleanup and the form's return.
The scenario therefore logs the timeout form's complete captured exit in an `onExit` finalizer.
That finalizer runs after the race's settlement cleanup, before the retry loop consumes the form's exit.
The log pairs the committed attempt count with that exit in a third reference cell.
The observation pairs completed log entries with the corresponding first-exit race's selected child.
A selected exit alone does not count as a completed timeout outcome.

The placement of the worker laws is reactive scheduling, R4, serving the existing timeout retry claim.
The consumer chain is completion worker, observer dispatch, timeout form, then corrected retry predicate.
The required worker laws are exact first acceptance, immutable acceptance on later callbacks, and unknown-child refusal.
