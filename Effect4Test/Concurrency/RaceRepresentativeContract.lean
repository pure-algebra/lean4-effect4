/-
Contract packet: `test/contracts/race-representative.contract.md`

Breaker-owned red battery.  The implementation phase must not edit this file.
It remains red until `Effect4/Concurrency/Race.lean` supplies this exact
binary `raceFirst` surface and theorem spine.
-/

import Lean
import Effect4.Concurrency.Scheduler
import Effect4.Concurrency.Race

namespace Effect4Test.Concurrency.RaceRepresentativeContract

open Effect4
open Lean Elab Command

universe u

private def failRaceShape (subject : Name) (detail : MessageData) :
    CommandElabM α :=
  throwError m!"race declaration shape mismatch for {subject}: {detail}"

private def checkRaceInductive (environment : Environment) (typeName : Name)
    (constructors : List Name) (fields : Option (List Name)) :
    CommandElabM Unit := do
  let information ← match environment.find? typeName with
    | some (.inductInfo information) => pure information
    | some _ => failRaceShape typeName "expected an inductive declaration"
    | none => failRaceShape typeName "declaration is absent"
  unless information.all == [typeName] do
    failRaceShape typeName m!"expected a non-mutual declaration, found {information.all}"
  unless information.ctors == constructors do
    failRaceShape typeName
      m!"constructors: expected {constructors}, found {information.ctors}"
  match fields with
  | some expectedFields =>
      let some structureInformation := getStructureInfo? environment typeName
        | failRaceShape typeName "expected structure metadata"
      unless structureInformation.fieldNames.toList == expectedFields do
        failRaceShape typeName m!"fields: expected {expectedFields}, found {structureInformation.fieldNames.toList}"
  | none =>
      if (getStructureInfo? environment typeName).isSome then
        failRaceShape typeName "expected an inductive, found structure metadata"

private def nameOwnedByModule (environment : Environment) (name moduleName : Name) :
    Bool :=
  match environment.getModuleIdxFor? name with
  | none => false
  | some moduleIndex => environment.header.moduleNames[moduleIndex]? == some moduleName

private def charListPrefix : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && charListPrefix expectedRest actualRest

private def charListContains (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | actual@(_ :: rest) =>
      charListPrefix needle actual || charListContains needle rest

private def stringContains (actual expected : String) : Bool :=
  charListContains expected.toList actual.toList

private def isFirstSuccessRaceName (name : Name) : Bool :=
  let spelling := name.toString
  let finalComponent := name.getString!
  stringContains spelling "success" ||
    stringContains spelling "Success" ||
    stringContains spelling ".raceAll" ||
    stringContains spelling ".RaceAll" ||
    finalComponent == "race"

private def hierarchicalName (components : List String) : Name :=
  components.foldl Name.str Name.anonymous

elab "#effect4_check_race_forbidden_declarations" : command => do
  let environment ← getEnv
  let forbiddenCarriers :=
    [hierarchicalName ["Effect4", "RaceId"],
      hierarchicalName ["Effect4", "RaceSide"],
      hierarchicalName ["Effect4", "RaceMachine"],
      hierarchicalName ["Effect4", "RaceEvent"],
      hierarchicalName ["Effect4", "RaceOutcome"],
      hierarchicalName ["Effect4", "RaceExit"]]
  for name in forbiddenCarriers do
    if (environment.find? name).isSome then
      throwError m!"race forbidden duplicate declaration is present: {name}"
  for (name, _information) in environment.constants.toList do
    if nameOwnedByModule environment name
        (hierarchicalName ["Effect4", "Concurrency", "Race"]) &&
        isFirstSuccessRaceName name then
      throwError m!"race forbidden first-success declaration is present: {name}"

elab "#effect4_check_race_declaration_shapes" : command => do
  let environment ← getEnv
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceSpec"])
    [hierarchicalName ["Effect4", "RaceSpec", "mk"]]
    (some [Name.mkSimple "coordinator", Name.mkSimple "left", Name.mkSimple "right"])
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceState"])
    [hierarchicalName ["Effect4", "RaceState", "mk"]]
    (some [Name.mkSimple "machine", Name.mkSimple "winner"])
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceDecision"])
    [hierarchicalName ["Effect4", "RaceDecision", "scheduler"],
      hierarchicalName ["Effect4", "RaceDecision", "selectWinner"]] none
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceRefusal"])
    [hierarchicalName ["Effect4", "RaceRefusal", "scheduler"],
      hierarchicalName ["Effect4", "RaceRefusal", "schedulerOutsideRace"],
      hierarchicalName ["Effect4", "RaceRefusal", "winnerSelectionRequired"],
      hierarchicalName ["Effect4", "RaceRefusal", "winnerNotContender"],
      hierarchicalName ["Effect4", "RaceRefusal", "winnerNotDone"],
      hierarchicalName ["Effect4", "RaceRefusal", "winnerAlreadySelected"],
      hierarchicalName ["Effect4", "RaceRefusal", "raceSettled"]] none
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceStepResult"])
    [hierarchicalName ["Effect4", "RaceStepResult", "advanced"],
      hierarchicalName ["Effect4", "RaceStepResult", "refused"]] none
  checkRaceInductive environment (hierarchicalName ["Effect4", "RaceReplayResult"])
    [hierarchicalName ["Effect4", "RaceReplayResult", "settled"],
      hierarchicalName ["Effect4", "RaceReplayResult", "refused"],
      hierarchicalName ["Effect4", "RaceReplayResult", "frontier"]] none

#effect4_check_race_forbidden_declarations
#effect4_check_race_declaration_shapes

section Surface

/-! The race reuses `FiberId` and `Machine`; it mints neither side nor machine IDs. -/

#check (@RaceSpec : Type)
#check (@RaceSpec.mk : FiberId -> FiberId -> FiberId -> RaceSpec)
#check (@RaceSpec.coordinator : RaceSpec -> FiberId)
#check (@RaceSpec.left : RaceSpec -> FiberId)
#check (@RaceSpec.right : RaceSpec -> FiberId)
#synth DecidableEq RaceSpec
#synth Repr RaceSpec
#check (@RaceSpec.ext_iff : forall (left right : RaceSpec),
  left = right <->
    left.coordinator = right.coordinator /\
    left.left = right.left /\
    left.right = right.right)

#check (@RaceSpec.IsContender : RaceSpec -> FiberId -> Prop)
#check (@RaceSpec.isContender_iff : forall spec id,
  RaceSpec.IsContender spec id <-> id = spec.left \/ id = spec.right)
#check (@RaceSpec.isContenderDecidable : forall spec id,
  Decidable (RaceSpec.IsContender spec id))
#check (@RaceSpec.isContender_left : forall spec,
  RaceSpec.IsContender spec spec.left)
#check (@RaceSpec.isContender_right : forall spec,
  RaceSpec.IsContender spec spec.right)
#check (@RaceSpec.loser : RaceSpec -> FiberId -> FiberId)
#check (@RaceSpec.loser_left : forall (spec : RaceSpec),
  spec.loser spec.left = spec.right)
#check (@RaceSpec.loser_right : forall (spec : RaceSpec),
  spec.loser spec.right = spec.left)

#check (@RaceSpec.ValidIn : forall {τ : Type u}, RaceSpec -> Machine τ -> Prop)
#check (@RaceSpec.ValidIn.mk : forall {τ : Type u}
    {spec : RaceSpec} {machine : Machine τ},
  spec.coordinator ≠ spec.left ->
  spec.coordinator ≠ spec.right ->
  spec.left ≠ spec.right ->
  (exists fiber, machine.fiber spec.coordinator = some fiber /\
    FiberStatus.Active fiber.status) ->
  (exists fiber, machine.fiber spec.left = some fiber) ->
  (exists fiber, machine.fiber spec.right = some fiber) ->
  RaceSpec.ValidIn spec machine)
#check (@RaceSpec.validIn_iff : forall {τ : Type u}
    (spec : RaceSpec) (machine : Machine τ),
  RaceSpec.ValidIn spec machine <->
    spec.coordinator ≠ spec.left /\
    spec.coordinator ≠ spec.right /\
    spec.left ≠ spec.right /\
    (exists fiber, machine.fiber spec.coordinator = some fiber /\
      FiberStatus.Active fiber.status) /\
    (exists fiber, machine.fiber spec.left = some fiber) /\
    (exists fiber, machine.fiber spec.right = some fiber))

/-! The only extension of scheduler state is the explicit chosen winner. -/
#check (@RaceState : Type u -> Type u)
#check (@RaceState.mk : forall {τ : Type u},
  Machine τ -> Option FiberId -> RaceState τ)
#check (@RaceState.machine : forall {τ : Type u}, RaceState τ -> Machine τ)
#check (@RaceState.winner : forall {τ : Type u},
  RaceState τ -> Option FiberId)
#check (@RaceState.ext_iff : forall {τ : Type u}
    (left right : RaceState τ),
  left = right <->
    left.machine = right.machine /\
      left.winner = right.winner)

#check (@RaceState.ContenderDone : forall {τ : Type u},
  RaceSpec -> RaceState τ -> FiberId -> Prop)
#check (@RaceState.contenderDone_iff : forall {τ : Type u}
    (spec : RaceSpec) (state : RaceState τ) (id : FiberId),
  RaceState.ContenderDone spec state id <->
    RaceSpec.IsContender spec id /\
      (state.machine.fiber id).map FiberState.status = some .done)
#check (@RaceState.NeedsWinner : forall {τ : Type u},
  RaceSpec -> RaceState τ -> Prop)
#check (@RaceState.needsWinner_iff : forall {τ : Type u}
    (spec : RaceSpec) (state : RaceState τ),
  RaceState.NeedsWinner spec state <->
    state.winner = none /\
      (RaceState.ContenderDone spec state spec.left \/
        RaceState.ContenderDone spec state spec.right))
#check (@RaceState.needsWinnerDecidable : forall {τ : Type u} spec state,
  Decidable (RaceState.NeedsWinner spec state))

#check (@RaceState.WellFormed : forall {τ : Type u},
  RaceSpec -> RaceState τ -> Prop)
#check (@RaceState.WellFormed.mk : forall {τ : Type u}
    {spec : RaceSpec} {state : RaceState τ},
  Machine.WellFormed state.machine ->
  RaceSpec.ValidIn spec state.machine ->
  (forall winner, state.winner = some winner ->
    RaceState.ContenderDone spec state winner) ->
  (forall winner loserState, state.winner = some winner ->
    state.machine.fiber (spec.loser winner) = some loserState ->
    FiberStatus.Active loserState.status ->
    loserState.mask = InterruptMask.masked /\
      loserState.interruptPending = true) ->
  RaceState.WellFormed spec state)
#check (@RaceState.wellFormed_iff : forall {τ : Type u}
    (spec : RaceSpec) (state : RaceState τ),
  RaceState.WellFormed spec state <->
    Machine.WellFormed state.machine /\
    RaceSpec.ValidIn spec state.machine /\
    (forall winner, state.winner = some winner ->
      RaceState.ContenderDone spec state winner) /\
    (forall winner loserState, state.winner = some winner ->
      state.machine.fiber (spec.loser winner) = some loserState ->
      FiberStatus.Active loserState.status ->
      loserState.mask = InterruptMask.masked /\
        loserState.interruptPending = true))

#check (@RaceState.Settled : forall {τ : Type u},
  RaceSpec -> RaceState τ -> τ -> Prop)
#check (@RaceState.settled_iff : forall {τ : Type u}
    (spec : RaceSpec) (state : RaceState τ) (result : τ),
  RaceState.Settled spec state result <->
    exists winner,
      state.winner = some winner /\
      RaceSpec.IsContender spec winner /\
      state.machine.terminal winner = some result /\
      (state.machine.fiber spec.left).map FiberState.status = some .done /\
      (state.machine.fiber spec.right).map FiberState.status = some .done /\
      state.machine.cleanupState spec.left = some .done /\
      state.machine.cleanupState spec.right = some .done)
#check (@RaceState.settledResult? : forall {τ : Type u},
  RaceSpec -> RaceState τ -> Option τ)
#check (@RaceState.settledResult_eq_some : forall {τ : Type u}
    {spec : RaceSpec} {state : RaceState τ} {result : τ},
  RaceState.settledResult? spec state = some result <->
    RaceState.Settled spec state result)

/-! A race tape extends, rather than replaces, the scheduler tape. -/
#check (@RaceDecision : Type u -> Type u)
#check (@RaceDecision.scheduler : forall {τ : Type u},
  SchedulerDecision τ -> RaceDecision τ)
#check (@RaceDecision.selectWinner : forall {τ : Type u},
  FiberId -> RaceDecision τ)
#check (@RaceTape : Type u -> Type u)
example (τ : Type u) : RaceTape τ = List (RaceDecision τ) := rfl

#check (@RaceDecision.BeforeSelection : forall {τ : Type u},
  RaceSpec -> SchedulerDecision τ -> Prop)
#check (@RaceDecision.beforeSelection_iff : forall {τ : Type u}
    (spec : RaceSpec) (decision : SchedulerDecision τ),
  RaceDecision.BeforeSelection spec decision <->
    (exists id, decision = .schedule id /\
      RaceSpec.IsContender spec id) \/
    (exists id, decision = .enterMask id /\
      RaceSpec.IsContender spec id) \/
    (exists id, decision = .exitMask id /\
      RaceSpec.IsContender spec id) \/
    (exists id result, decision = .complete id result /\
      RaceSpec.IsContender spec id) \/
    (exists id, decision = .cleanup id /\
      RaceSpec.IsContender spec id))
#check (@RaceDecision.beforeSelectionDecidable : forall {τ : Type u}
    spec decision, Decidable (RaceDecision.BeforeSelection spec decision))
#check (@RaceDecision.AfterSelection : forall {τ : Type u},
  RaceSpec -> FiberId -> SchedulerDecision τ -> Prop)
#check (@RaceDecision.afterSelection_iff : forall {τ : Type u}
    (spec : RaceSpec) (winner : FiberId) (decision : SchedulerDecision τ),
  RaceDecision.AfterSelection spec winner decision <->
    decision = .exitMask (spec.loser winner) \/
      decision = .cleanup (spec.loser winner))
#check (@RaceDecision.afterSelectionDecidable : forall {τ : Type u}
    spec winner decision,
  Decidable (RaceDecision.AfterSelection spec winner decision))
#check (@RaceDecision.beforeSelection_left_coverage : forall {τ : Type u}
    (spec : RaceSpec) (result : τ),
  RaceDecision.BeforeSelection spec (.schedule spec.left) /\
  RaceDecision.BeforeSelection spec (.enterMask spec.left) /\
  RaceDecision.BeforeSelection spec (.exitMask spec.left) /\
  RaceDecision.BeforeSelection spec (.complete spec.left result) /\
  RaceDecision.BeforeSelection spec (.cleanup spec.left))

/-! Race refusals classify invalid choices; tape depletion is not among them. -/
#check (@RaceRefusal : Type u -> Type u)
#check (@RaceRefusal.scheduler : forall {τ : Type u},
  SchedulerRefusal -> RaceRefusal τ)
#check (@RaceRefusal.schedulerOutsideRace : forall {τ : Type u},
  SchedulerDecision τ -> RaceRefusal τ)
#check (@RaceRefusal.winnerSelectionRequired : forall {τ : Type u},
  RaceRefusal τ)
#check (@RaceRefusal.winnerNotContender : forall {τ : Type u},
  FiberId -> RaceRefusal τ)
#check (@RaceRefusal.winnerNotDone : forall {τ : Type u},
  FiberId -> RaceRefusal τ)
#check (@RaceRefusal.winnerAlreadySelected : forall {τ : Type u},
  FiberId -> RaceRefusal τ)
#check (@RaceRefusal.raceSettled : forall {τ : Type u},
  FiberId -> RaceRefusal τ)

#check (@RaceStepResult : Type u -> Type u)
#check (@RaceStepResult.advanced : forall {τ : Type u},
  RaceState τ -> RaceStepResult τ)
#check (@RaceStepResult.refused : forall {τ : Type u},
  RaceRefusal τ -> RaceState τ -> RaceStepResult τ)
#check (@RaceStepResult.state : forall {τ : Type u},
  RaceStepResult τ -> RaceState τ)
#check (@RaceStepResult.state_advanced : forall {τ : Type u}
    (state : RaceState τ),
  (RaceStepResult.advanced state).state = state)
#check (@RaceStepResult.state_refused : forall {τ : Type u}
    (refusal : RaceRefusal τ) (state : RaceState τ),
  (RaceStepResult.refused refusal state).state = state)
#check (@RaceStepResult.fromScheduler : forall {τ : Type u},
  RaceState τ -> StepResult τ -> RaceStepResult τ)
#check (@RaceStepResult.fromWinnerSelection : forall {τ : Type u},
  FiberId -> RaceState τ -> StepResult τ -> RaceStepResult τ)
#check (@RaceStepResult.fromScheduler_advanced : forall {τ : Type u}
    (before : RaceState τ) (machine : Machine τ),
  RaceStepResult.fromScheduler before (.advanced machine) =
    .advanced { before with machine := machine })
#check (@RaceStepResult.fromScheduler_refused : forall {τ : Type u}
    (before : RaceState τ) (refusal : SchedulerRefusal) (machine : Machine τ),
  RaceStepResult.fromScheduler before (.refused refusal machine) =
    .refused (.scheduler refusal) { before with machine := machine })
#check (@RaceStepResult.fromWinnerSelection_advanced : forall {τ : Type u}
    (winner : FiberId) (before : RaceState τ) (machine : Machine τ),
  RaceStepResult.fromWinnerSelection winner before (.advanced machine) =
    .advanced { before with machine := machine, winner := some winner })
#check (@RaceStepResult.fromWinnerSelection_refused : forall {τ : Type u}
    (winner : FiberId) (before : RaceState τ)
    (refusal : SchedulerRefusal) (machine : Machine τ),
  RaceStepResult.fromWinnerSelection winner before (.refused refusal machine) =
    .refused (.scheduler refusal) { before with machine := machine })

#check (@RaceReplayResult : Type u -> Type u)
#check (@RaceReplayResult.settled : forall {τ : Type u},
  τ -> RaceState τ -> RaceReplayResult τ)
#check (@RaceReplayResult.refused : forall {τ : Type u},
  RaceRefusal τ -> RaceState τ -> RaceReplayResult τ)
#check (@RaceReplayResult.frontier : forall {τ : Type u},
  RaceState τ -> RaceReplayResult τ)
#check (@RaceReplayResult.state : forall {τ : Type u},
  RaceReplayResult τ -> RaceState τ)
#check (@RaceReplayResult.state_settled : forall {τ : Type u}
    (result : τ) (state : RaceState τ),
  (RaceReplayResult.settled result state).state = state)
#check (@RaceReplayResult.state_refused : forall {τ : Type u}
    (refusal : RaceRefusal τ) (state : RaceState τ),
  (RaceReplayResult.refused refusal state).state = state)
#check (@RaceReplayResult.state_frontier : forall {τ : Type u}
    (state : RaceState τ),
  (RaceReplayResult.frontier state).state = state)

#check (@raceStepEval : forall {τ : Type u}, InterruptBoundary τ ->
  RaceSpec -> RaceState τ -> RaceDecision τ -> RaceStepResult τ)
#check (@RaceStep : forall {τ : Type u}, InterruptBoundary τ ->
  RaceSpec -> RaceState τ -> RaceDecision τ -> RaceStepResult τ -> Prop)
#check (@raceReplayEval : forall {τ : Type u}, InterruptBoundary τ ->
  RaceSpec -> RaceState τ -> RaceTape τ -> RaceReplayResult τ)
#check (@RaceRuns : forall {τ : Type u}, InterruptBoundary τ ->
  RaceSpec -> RaceState τ -> RaceTape τ -> RaceReplayResult τ -> Prop)

end Surface

section ExactEquations

#check (@RaceDecision.cases_receipt : forall {τ : Type u}
    (decision : RaceDecision τ),
  (exists schedulerDecision,
    decision = RaceDecision.scheduler schedulerDecision) \/
  (exists winner, decision = RaceDecision.selectWinner winner))

#check (@RaceRefusal.cases_receipt : forall {τ : Type u}
    (refusal : RaceRefusal τ),
  (exists schedulerRefusal,
    refusal = RaceRefusal.scheduler schedulerRefusal) \/
  (exists decision,
    refusal = RaceRefusal.schedulerOutsideRace decision) \/
  refusal = RaceRefusal.winnerSelectionRequired \/
  (exists winner, refusal = RaceRefusal.winnerNotContender winner) \/
  (exists winner, refusal = RaceRefusal.winnerNotDone winner) \/
  (exists winner, refusal = RaceRefusal.winnerAlreadySelected winner) \/
  (exists winner, refusal = RaceRefusal.raceSettled winner))

#check (@RaceStepResult.cases_receipt : forall {τ : Type u}
    (result : RaceStepResult τ),
  (exists state, result = RaceStepResult.advanced state) \/
  (exists refusal state, result = RaceStepResult.refused refusal state))

#check (@RaceReplayResult.cases_receipt : forall {τ : Type u}
    (result : RaceReplayResult τ),
  (exists terminal state, result = RaceReplayResult.settled terminal state) \/
  (exists refusal state, result = RaceReplayResult.refused refusal state) \/
  (exists state, result = RaceReplayResult.frontier state))

#check (@raceStep_iff : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision result},
  RaceStep boundary spec before decision result <->
    result = raceStepEval boundary spec before decision)

#check (@raceRuns_iff : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial tape result},
  RaceRuns boundary spec initial tape result <->
    RaceState.WellFormed spec initial /\
      result = raceReplayEval boundary spec initial tape)

/-! Before a completion is observable, scoped child scheduler steps delegate. -/
#check (@raceStepEval_scheduler_before : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision},
  before.winner = none ->
  Not (RaceState.NeedsWinner spec before) ->
  RaceDecision.BeforeSelection spec decision ->
  raceStepEval boundary spec before (.scheduler decision) =
    RaceStepResult.fromScheduler before
      (stepEval boundary before.machine decision))

/-! Once a child is done, no further scheduler step may obscure first completion. -/
#check (@raceStepEval_scheduler_needsWinner : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision},
  before.winner = none ->
  RaceState.NeedsWinner spec before ->
  raceStepEval boundary spec before (.scheduler decision) =
    .refused .winnerSelectionRequired before)

#check (@raceStepEval_scheduler_outside_before : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision},
  before.winner = none ->
  Not (RaceState.NeedsWinner spec before) ->
  Not (RaceDecision.BeforeSelection spec decision) ->
  raceStepEval boundary spec before (.scheduler decision) =
    .refused (.schedulerOutsideRace decision) before)

/-! After selection, only the loser's unmask and cleanup steps remain in scope. -/
#check (@raceStepEval_scheduler_after : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner decision},
  before.winner = some winner ->
  RaceState.settledResult? spec before = none ->
  RaceDecision.AfterSelection spec winner decision ->
  raceStepEval boundary spec before (.scheduler decision) =
    RaceStepResult.fromScheduler before
      (stepEval boundary before.machine decision))

#check (@raceStepEval_scheduler_outside_after : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner decision},
  before.winner = some winner ->
  RaceState.settledResult? spec before = none ->
  Not (RaceDecision.AfterSelection spec winner decision) ->
  raceStepEval boundary spec before (.scheduler decision) =
    .refused (.schedulerOutsideRace decision) before)

#check (@raceStepEval_scheduler_settled : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner result decision},
  before.winner = some winner ->
  RaceState.settledResult? spec before = some result ->
  raceStepEval boundary spec before (.scheduler decision) =
    .refused (.raceSettled winner) before)

#check (@raceStepEval_select_already : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before selected attempted},
  before.winner = some selected ->
  raceStepEval boundary spec before (.selectWinner attempted) =
    .refused (.winnerAlreadySelected selected) before)

#check (@raceStepEval_select_notContender : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before attempted},
  before.winner = none ->
  Not (RaceSpec.IsContender spec attempted) ->
  raceStepEval boundary spec before (.selectWinner attempted) =
    .refused (.winnerNotContender attempted) before)

#check (@raceStepEval_select_notDone : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before attempted},
  before.winner = none ->
  RaceSpec.IsContender spec attempted ->
  Not (RaceState.ContenderDone spec before attempted) ->
  raceStepEval boundary spec before (.selectWinner attempted) =
    .refused (.winnerNotDone attempted) before)

#check (@raceStepEval_select_missingLoser : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner},
  before.winner = none ->
  RaceState.ContenderDone spec before winner ->
  before.machine.fiber (spec.loser winner) = none ->
  raceStepEval boundary spec before (.selectWinner winner) =
    .refused (.scheduler (.unknownFiber (spec.loser winner))) before)

#check (@raceStepEval_select_active : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner loserState},
  before.winner = none ->
  RaceState.ContenderDone spec before winner ->
  before.machine.fiber (spec.loser winner) = some loserState ->
  FiberStatus.Active loserState.status ->
  raceStepEval boundary spec before (.selectWinner winner) =
    RaceStepResult.fromWinnerSelection winner before
      (stepEval boundary before.machine
        (.requestInterrupt spec.coordinator (spec.loser winner))))

#check (@raceStepEval_select_inactive : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner loserState},
  before.winner = none ->
  RaceState.ContenderDone spec before winner ->
  before.machine.fiber (spec.loser winner) = some loserState ->
  Not (FiberStatus.Active loserState.status) ->
  raceStepEval boundary spec before (.selectWinner winner) =
    .advanced { before with winner := some winner })

/-! Replay checks settlement before consuming another choice. -/
#check (@raceReplayEval_settled : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial result tape},
  RaceState.settledResult? spec initial = some result ->
  raceReplayEval boundary spec initial tape = .settled result initial)

#check (@raceReplayEval_nil_frontier : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial},
  RaceState.settledResult? spec initial = none ->
  raceReplayEval boundary spec initial [] = .frontier initial)

#check (@raceReplayEval_cons_advanced : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial decision tape middle},
  RaceState.settledResult? spec initial = none ->
  raceStepEval boundary spec initial decision = .advanced middle ->
  raceReplayEval boundary spec initial (decision :: tape) =
    raceReplayEval boundary spec middle tape)

#check (@raceReplayEval_cons_refused : forall {τ : Type u}
    {boundary : InterruptBoundary τ}
    {spec initial decision tape refusal stopped},
  RaceState.settledResult? spec initial = none ->
  raceStepEval boundary spec initial decision = .refused refusal stopped ->
  raceReplayEval boundary spec initial (decision :: tape) =
    .refused refusal stopped)

end ExactEquations

section LawSpine

#check (@raceStep_deterministic : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision left right},
  RaceStep boundary spec before decision left ->
  RaceStep boundary spec before decision right -> left = right)

#check (@raceStep_total : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {spec before decision},
  exists result, RaceStep boundary spec before decision result)

#check (@raceStep_preserves_wellFormed : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision result},
  RaceState.WellFormed spec before ->
  RaceStep boundary spec before decision result ->
  RaceState.WellFormed spec result.state)

#check (@raceFixedTape_deterministic : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial tape left right},
  RaceRuns boundary spec initial tape left ->
  RaceRuns boundary spec initial tape right -> left = right)

#check (@raceFiniteReplay_total : forall {τ : Type u}
    (boundary : InterruptBoundary τ) {spec initial tape},
  RaceState.WellFormed spec initial ->
  exists result, RaceRuns boundary spec initial tape result)

#check (@raceRuns_preserves_wellFormed : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial tape result},
  RaceRuns boundary spec initial tape result ->
  RaceState.WellFormed spec result.state)

#check (@raceStep_records_done_winner : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before winner after},
  before.winner = none ->
  RaceStep boundary spec before (.selectWinner winner) (.advanced after) ->
  after.winner = some winner /\
    RaceState.ContenderDone spec before winner)

#check (@raceStep_winner_stable : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision after winner},
  before.winner = some winner ->
  RaceStep boundary spec before decision (.advanced after) ->
  after.winner = some winner)

#check (@raceStep_winner_terminal_stable : forall {τ : Type u}
    {boundary : InterruptBoundary τ}
    {spec before decision after winner terminal},
  RaceState.WellFormed spec before ->
  before.winner = some winner ->
  before.machine.terminal winner = some terminal ->
  RaceStep boundary spec before decision (.advanced after) ->
  after.machine.terminal winner = some terminal)

#check (@raceStep_unrelated_fiber_frame : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec before decision after id},
  id ≠ spec.left -> id ≠ spec.right ->
  RaceStep boundary spec before decision (.advanced after) ->
  after.machine.fiber id = before.machine.fiber id)

#check (@selectWinner_active_loser_interrupts : forall {τ : Type u}
    {boundary : InterruptBoundary τ}
    {spec before winner loserState after},
  RaceState.WellFormed spec before ->
  before.winner = none ->
  RaceState.ContenderDone spec before winner ->
  before.machine.fiber (spec.loser winner) = some loserState ->
  FiberStatus.Active loserState.status ->
  RaceStep boundary spec before (.selectWinner winner) (.advanced after) ->
  exists suffix,
    after.machine.trace = before.machine.trace ++
      (Event.interruptRequested spec.coordinator (spec.loser winner) :: suffix))

#check (@postSelection_only_loser_progress : forall {τ : Type u}
    {boundary : InterruptBoundary τ}
    {spec before winner decision after},
  before.winner = some winner ->
  RaceStep boundary spec before (.scheduler decision) (.advanced after) ->
  RaceDecision.AfterSelection spec winner decision)

#check (@settled_suffix_irrelevant : forall {τ : Type u}
    {boundary : InterruptBoundary τ} {spec initial result tape},
  RaceState.WellFormed spec initial ->
  RaceState.Settled spec initial result ->
  RaceRuns boundary spec initial tape (.settled result initial))

#check (@settled_cleanup_complete : forall {τ : Type u}
    {spec : RaceSpec} {state : RaceState τ} {result},
  RaceState.Settled spec state result ->
  exists winner,
    state.winner = some winner /\
    state.machine.terminal winner = some result /\
    (state.machine.fiber spec.left).map FiberState.status = some .done /\
    (state.machine.fiber spec.right).map FiberState.status = some .done /\
    state.machine.cleanupState spec.left = some .done /\
    state.machine.cleanupState spec.right = some .done)

#check (@settled_cleanup_once : forall {τ : Type u}
    {spec : RaceSpec} {state : RaceState τ} {result},
  RaceState.WellFormed spec state ->
  RaceState.Settled spec state result ->
  state.machine.cleanupCount spec.left = 1 /\
  state.machine.cleanupCount spec.right = 1 /\
  spec.left ∈ state.machine.cleanupEventIds /\
  spec.right ∈ state.machine.cleanupEventIds)

#check (@masked_loser_empty_tape_frontier : forall {τ : Type u}
    {boundary : InterruptBoundary τ}
    {spec state winner loserState},
  RaceState.WellFormed spec state ->
  state.winner = some winner ->
  state.machine.fiber (spec.loser winner) = some loserState ->
  FiberStatus.Active loserState.status ->
  loserState.mask = .masked ->
  loserState.interruptPending = true ->
  RaceRuns boundary spec state [] (.frontier state))

#check (@exists_representative_settled_run : forall {τ : Type u}
    (boundary : InterruptBoundary τ) (winnerResult : τ),
  exists spec initial tape final,
    RaceState.WellFormed spec initial /\
    tape ≠ [] /\
    RaceRuns boundary spec initial tape (.settled winnerResult final))

#check (@exists_tie_winner_choices : forall {τ : Type u}
    (boundary : InterruptBoundary τ),
  exists spec initial leftFinal rightFinal,
    RaceState.WellFormed spec initial /\
    RaceRuns boundary spec initial [.selectWinner spec.left]
      (.settled boundary.interrupted leftFinal) /\
    RaceRuns boundary spec initial [.selectWinner spec.right]
      (.settled boundary.interrupted rightFinal) /\
    leftFinal.winner ≠ rightFinal.winner)

end LawSpine

end Effect4Test.Concurrency.RaceRepresentativeContract
