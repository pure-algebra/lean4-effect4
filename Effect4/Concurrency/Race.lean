import Effect4.Concurrency.Scheduler

/-!
# Binary first-completion races

This module coordinates two existing fibers. Every lifecycle transition is
delegated to the scheduler; Race adds only the explicit winner choice needed
to retain tie resolution in a finite replay tape.
-/

namespace Effect4

universe u

/-- The coordinator and two contenders of one binary race. -/
structure RaceSpec where
  coordinator : FiberId
  left : FiberId
  right : FiberId
deriving DecidableEq, Repr

namespace RaceSpec

theorem ext_iff (left right : RaceSpec) :
    left = right <->
      left.coordinator = right.coordinator /\
      left.left = right.left /\
      left.right = right.right := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hcoordinator, hleft, hright⟩
    cases left
    cases right
    simp_all

/-- Membership in the bounded pair of contenders. -/
def IsContender (spec : RaceSpec) (id : FiberId) : Prop :=
  id = spec.left \/ id = spec.right

theorem isContender_iff (spec : RaceSpec) (id : FiberId) :
    IsContender spec id <-> id = spec.left \/ id = spec.right :=
  Iff.rfl

def isContenderDecidable (spec : RaceSpec) (id : FiberId) :
    Decidable (IsContender spec id) := by
  unfold IsContender
  infer_instance

theorem isContender_left (spec : RaceSpec) : IsContender spec spec.left :=
  Or.inl rfl

theorem isContender_right (spec : RaceSpec) : IsContender spec spec.right :=
  Or.inr rfl

/-- The opposite contender. Non-contender inputs take the left branch. -/
def loser (spec : RaceSpec) (winner : FiberId) : FiberId :=
  if winner = spec.left then spec.right else spec.left

theorem loser_left (spec : RaceSpec) : spec.loser spec.left = spec.right := by
  simp [loser]

theorem loser_right (spec : RaceSpec) : spec.loser spec.right = spec.left := by
  by_cases hsame : spec.right = spec.left
  · simp [loser, hsame]
  · simp [loser, hsame]

/-- Admission of the three race roles into an existing machine. -/
structure ValidIn (spec : RaceSpec) (machine : Machine τ) : Prop where
  coordinator_ne_left : spec.coordinator ≠ spec.left
  coordinator_ne_right : spec.coordinator ≠ spec.right
  left_ne_right : spec.left ≠ spec.right
  coordinator_active : exists fiber,
    machine.fiber spec.coordinator = some fiber /\
      FiberStatus.Active fiber.status
  left_present : exists fiber, machine.fiber spec.left = some fiber
  right_present : exists fiber, machine.fiber spec.right = some fiber

theorem validIn_iff (spec : RaceSpec) (machine : Machine τ) :
    ValidIn spec machine <->
      spec.coordinator ≠ spec.left /\
      spec.coordinator ≠ spec.right /\
      spec.left ≠ spec.right /\
      (exists fiber, machine.fiber spec.coordinator = some fiber /\
        FiberStatus.Active fiber.status) /\
      (exists fiber, machine.fiber spec.left = some fiber) /\
      (exists fiber, machine.fiber spec.right = some fiber) := by
  constructor
  · intro valid
    exact ⟨valid.coordinator_ne_left, valid.coordinator_ne_right,
      valid.left_ne_right, valid.coordinator_active, valid.left_present,
      valid.right_present⟩
  · rintro ⟨hcl, hcr, hlr, hc, hl, hr⟩
    exact ⟨hcl, hcr, hlr, hc, hl, hr⟩

end RaceSpec

/-- Existing scheduler state plus the explicit selected winner. -/
structure RaceState (τ : Type u) where
  machine : Machine τ
  winner : Option FiberId

namespace RaceState

theorem ext_iff (left right : RaceState τ) :
    left = right <->
      left.machine = right.machine /\ left.winner = right.winner := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hmachine, hwinner⟩
    cases left
    cases right
    simp_all

/-- A named contender has reached the scheduler's done phase. -/
def ContenderDone (spec : RaceSpec) (state : RaceState τ)
    (id : FiberId) : Prop :=
  RaceSpec.IsContender spec id /\
    (state.machine.fiber id).map FiberState.status = some .done

theorem contenderDone_iff (spec : RaceSpec) (state : RaceState τ)
    (id : FiberId) :
    ContenderDone spec state id <->
      RaceSpec.IsContender spec id /\
        (state.machine.fiber id).map FiberState.status = some .done :=
  Iff.rfl

/-- A completion is observable but no explicit winner has been selected. -/
def NeedsWinner (spec : RaceSpec) (state : RaceState τ) : Prop :=
  state.winner = none /\
    (ContenderDone spec state spec.left \/
      ContenderDone spec state spec.right)

theorem needsWinner_iff (spec : RaceSpec) (state : RaceState τ) :
    NeedsWinner spec state <->
      state.winner = none /\
        (ContenderDone spec state spec.left \/
          ContenderDone spec state spec.right) :=
  Iff.rfl

def needsWinnerDecidable (spec : RaceSpec) (state : RaceState τ) :
    Decidable (NeedsWinner spec state) := by
  unfold NeedsWinner ContenderDone RaceSpec.IsContender
  infer_instance

/-- Scheduler admission together with the race-specific winner invariant. -/
structure WellFormed (spec : RaceSpec) (state : RaceState τ) : Prop where
  machineWellFormed : Machine.WellFormed state.machine
  specValid : RaceSpec.ValidIn spec state.machine
  winnerDone : forall winner, state.winner = some winner ->
    ContenderDone spec state winner
  activeLoserInterrupted : forall winner loserState,
    state.winner = some winner ->
    state.machine.fiber (spec.loser winner) = some loserState ->
    FiberStatus.Active loserState.status ->
    loserState.mask = InterruptMask.masked /\
      loserState.interruptPending = true

theorem wellFormed_iff (spec : RaceSpec) (state : RaceState τ) :
    WellFormed spec state <->
      Machine.WellFormed state.machine /\
      RaceSpec.ValidIn spec state.machine /\
      (forall winner, state.winner = some winner ->
        ContenderDone spec state winner) /\
      (forall winner loserState, state.winner = some winner ->
        state.machine.fiber (spec.loser winner) = some loserState ->
        FiberStatus.Active loserState.status ->
        loserState.mask = InterruptMask.masked /\
          loserState.interruptPending = true) := by
  constructor
  · intro wf
    exact ⟨wf.machineWellFormed, wf.specValid, wf.winnerDone,
      wf.activeLoserInterrupted⟩
  · rintro ⟨hmachine, hspec, hwinner, hloser⟩
    exact ⟨hmachine, hspec, hwinner, hloser⟩

/-- The selected result is returnable only after both cleanups complete. -/
def Settled (spec : RaceSpec) (state : RaceState τ) (result : τ) : Prop :=
  exists winner,
    state.winner = some winner /\
    RaceSpec.IsContender spec winner /\
    state.machine.terminal winner = some result /\
    (state.machine.fiber spec.left).map FiberState.status = some .done /\
    (state.machine.fiber spec.right).map FiberState.status = some .done /\
    state.machine.cleanupState spec.left = some .done /\
    state.machine.cleanupState spec.right = some .done

theorem settled_iff (spec : RaceSpec) (state : RaceState τ) (result : τ) :
    Settled spec state result <->
      exists winner,
        state.winner = some winner /\
        RaceSpec.IsContender spec winner /\
        state.machine.terminal winner = some result /\
        (state.machine.fiber spec.left).map FiberState.status = some .done /\
        (state.machine.fiber spec.right).map FiberState.status = some .done /\
        state.machine.cleanupState spec.left = some .done /\
        state.machine.cleanupState spec.right = some .done :=
  Iff.rfl

/-- Compute the settled terminal observation without equality on it. -/
def settledResult? (spec : RaceSpec) (state : RaceState τ) : Option τ :=
  match state.winner with
  | none => none
  | some winner =>
      if _hcontender : RaceSpec.IsContender spec winner then
        match state.machine.terminal winner with
        | none => none
        | some result =>
            if (state.machine.fiber spec.left).map FiberState.status = some .done /\
                (state.machine.fiber spec.right).map FiberState.status = some .done /\
                state.machine.cleanupState spec.left = some .done /\
                state.machine.cleanupState spec.right = some .done then
              some result
            else
              none
      else
        none

theorem settledResult_eq_some {spec : RaceSpec} {state : RaceState τ}
    {result : τ} :
    settledResult? spec state = some result <-> Settled spec state result := by
  cases hwinner : state.winner with
  | none => simp [settledResult?, Settled, hwinner]
  | some winner =>
      by_cases hcontender : RaceSpec.IsContender spec winner
      · cases hterminal : state.machine.terminal winner with
        | none => simp [settledResult?, Settled, hwinner, hcontender, hterminal]
        | some terminal =>
            by_cases hcomplete :
                (state.machine.fiber spec.left).map FiberState.status = some .done /\
                (state.machine.fiber spec.right).map FiberState.status = some .done /\
                state.machine.cleanupState spec.left = some .done /\
                state.machine.cleanupState spec.right = some .done
            · simp [settledResult?, Settled, hwinner, hcontender, hterminal,
                hcomplete]
            · simp [settledResult?, Settled, hwinner, hcontender, hterminal,
                hcomplete]
      · simp [settledResult?, Settled, hwinner, hcontender]

end RaceState

/-- A race choice is either an existing scheduler choice or winner selection. -/
inductive RaceDecision (τ : Type u)
  | scheduler (decision : SchedulerDecision τ)
  | selectWinner (winner : FiberId)

abbrev RaceTape (τ : Type u) := List (RaceDecision τ)

namespace RaceDecision

/-- Scheduler choices admitted before winner selection. -/
def BeforeSelection (spec : RaceSpec) : SchedulerDecision τ -> Prop
  | .schedule id => RaceSpec.IsContender spec id
  | .enterMask id => RaceSpec.IsContender spec id
  | .exitMask id => RaceSpec.IsContender spec id
  | .complete id _ => RaceSpec.IsContender spec id
  | .cleanup id => RaceSpec.IsContender spec id
  | .join _ _ | .requestInterrupt _ _ => False

theorem beforeSelection_iff (spec : RaceSpec) (decision : SchedulerDecision τ) :
    BeforeSelection spec decision <->
      (exists id, decision = .schedule id /\ RaceSpec.IsContender spec id) \/
      (exists id, decision = .enterMask id /\ RaceSpec.IsContender spec id) \/
      (exists id, decision = .exitMask id /\ RaceSpec.IsContender spec id) \/
      (exists id result, decision = .complete id result /\
        RaceSpec.IsContender spec id) \/
      (exists id, decision = .cleanup id /\ RaceSpec.IsContender spec id) := by
  cases decision <;> simp [BeforeSelection]

def beforeSelectionDecidable (spec : RaceSpec)
    (decision : SchedulerDecision τ) : Decidable (BeforeSelection spec decision) := by
  cases decision <;> simp [BeforeSelection, RaceSpec.IsContender] <;>
    infer_instance

/-- Only loser unmasking and cleanup remain after selection. -/
def AfterSelection (spec : RaceSpec) (winner : FiberId) :
    SchedulerDecision τ -> Prop
  | .exitMask id => id = spec.loser winner
  | .cleanup id => id = spec.loser winner
  | _ => False

theorem afterSelection_iff (spec : RaceSpec) (winner : FiberId)
    (decision : SchedulerDecision τ) :
    AfterSelection spec winner decision <->
      decision = .exitMask (spec.loser winner) \/
        decision = .cleanup (spec.loser winner) := by
  cases decision <;> simp [AfterSelection]

def afterSelectionDecidable (spec : RaceSpec) (winner : FiberId)
    (decision : SchedulerDecision τ) :
    Decidable (AfterSelection spec winner decision) := by
  cases decision <;> simp [AfterSelection] <;> infer_instance

theorem beforeSelection_left_coverage (spec : RaceSpec) (result : τ) :
    BeforeSelection spec (.schedule spec.left : SchedulerDecision τ) /\
    BeforeSelection spec (.enterMask spec.left : SchedulerDecision τ) /\
    BeforeSelection spec (.exitMask spec.left : SchedulerDecision τ) /\
    BeforeSelection spec (.complete spec.left result) /\
    BeforeSelection spec (.cleanup spec.left : SchedulerDecision τ) := by
  simp [BeforeSelection, RaceSpec.IsContender]

theorem cases_receipt (decision : RaceDecision τ) :
    (exists schedulerDecision, decision = scheduler schedulerDecision) \/
      (exists winner, decision = selectWinner winner) := by
  cases decision with
  | scheduler decision => exact Or.inl ⟨decision, rfl⟩
  | selectWinner winner => exact Or.inr ⟨winner, rfl⟩

end RaceDecision

/-- Invalid race-level choices. Tape depletion is represented separately. -/
inductive RaceRefusal (τ : Type u)
  | scheduler (refusal : SchedulerRefusal)
  | schedulerOutsideRace (decision : SchedulerDecision τ)
  | winnerSelectionRequired
  | winnerNotContender (winner : FiberId)
  | winnerNotDone (winner : FiberId)
  | winnerAlreadySelected (winner : FiberId)
  | raceSettled (winner : FiberId)

namespace RaceRefusal

theorem cases_receipt (refusal : RaceRefusal τ) :
    (exists schedulerRefusal, refusal = scheduler schedulerRefusal) \/
    (exists decision, refusal = schedulerOutsideRace decision) \/
    refusal = winnerSelectionRequired \/
    (exists winner, refusal = winnerNotContender winner) \/
    (exists winner, refusal = winnerNotDone winner) \/
    (exists winner, refusal = winnerAlreadySelected winner) \/
    (exists winner, refusal = raceSettled winner) := by
  cases refusal with
  | scheduler refusal => exact Or.inl ⟨refusal, rfl⟩
  | schedulerOutsideRace decision => exact Or.inr (Or.inl ⟨decision, rfl⟩)
  | winnerSelectionRequired => exact Or.inr (Or.inr (Or.inl rfl))
  | winnerNotContender winner =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨winner, rfl⟩)))
  | winnerNotDone winner =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨winner, rfl⟩))))
  | winnerAlreadySelected winner =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨winner, rfl⟩)))))
  | raceSettled winner =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨winner, rfl⟩)))))

end RaceRefusal

/-- Result of one race decision. -/
inductive RaceStepResult (τ : Type u)
  | advanced (state : RaceState τ)
  | refused (refusal : RaceRefusal τ) (state : RaceState τ)

namespace RaceStepResult

def state : RaceStepResult τ -> RaceState τ
  | .advanced state | .refused _ state => state

theorem state_advanced (state : RaceState τ) : (advanced state).state = state := rfl

theorem state_refused (refusal : RaceRefusal τ) (state : RaceState τ) :
    (refused refusal state).state = state := rfl

def fromScheduler (before : RaceState τ) : StepResult τ -> RaceStepResult τ
  | .advanced machine => .advanced { before with machine := machine }
  | .refused refusal machine =>
      .refused (.scheduler refusal) { before with machine := machine }

def fromWinnerSelection (winner : FiberId) (before : RaceState τ) :
    StepResult τ -> RaceStepResult τ
  | .advanced machine =>
      .advanced { before with machine := machine, winner := some winner }
  | .refused refusal machine =>
      .refused (.scheduler refusal) { before with machine := machine }

theorem fromScheduler_advanced (before : RaceState τ) (machine : Machine τ) :
    fromScheduler before (.advanced machine) =
      .advanced { before with machine := machine } := rfl

theorem fromScheduler_refused (before : RaceState τ)
    (refusal : SchedulerRefusal) (machine : Machine τ) :
    fromScheduler before (.refused refusal machine) =
      .refused (.scheduler refusal) { before with machine := machine } := rfl

theorem fromWinnerSelection_advanced (winner : FiberId)
    (before : RaceState τ) (machine : Machine τ) :
    fromWinnerSelection winner before (.advanced machine) =
      .advanced { before with machine := machine, winner := some winner } := rfl

theorem fromWinnerSelection_refused (winner : FiberId)
    (before : RaceState τ) (refusal : SchedulerRefusal) (machine : Machine τ) :
    fromWinnerSelection winner before (.refused refusal machine) =
      .refused (.scheduler refusal) { before with machine := machine } := rfl

theorem cases_receipt (result : RaceStepResult τ) :
    (exists state, result = advanced state) \/
      (exists refusal state, result = refused refusal state) := by
  cases result with
  | advanced state => exact Or.inl ⟨state, rfl⟩
  | refused refusal state => exact Or.inr ⟨refusal, state, rfl⟩

end RaceStepResult

/-- Observation of replaying a finite race tape. -/
inductive RaceReplayResult (τ : Type u)
  | settled (result : τ) (state : RaceState τ)
  | refused (refusal : RaceRefusal τ) (state : RaceState τ)
  | frontier (state : RaceState τ)

namespace RaceReplayResult

def state : RaceReplayResult τ -> RaceState τ
  | .settled _ state | .refused _ state | .frontier state => state

theorem state_settled (result : τ) (state : RaceState τ) :
    (settled result state).state = state := rfl

theorem state_refused (refusal : RaceRefusal τ) (state : RaceState τ) :
    (refused refusal state).state = state := rfl

theorem state_frontier (state : RaceState τ) :
    (frontier state).state = state := rfl

theorem cases_receipt (result : RaceReplayResult τ) :
    (exists terminal state, result = settled terminal state) \/
    (exists refusal state, result = refused refusal state) \/
    (exists state, result = frontier state) := by
  cases result with
  | settled terminal state => exact Or.inl ⟨terminal, state, rfl⟩
  | refused refusal state => exact Or.inr (Or.inl ⟨refusal, state, rfl⟩)
  | frontier state => exact Or.inr (Or.inr ⟨state, rfl⟩)

end RaceReplayResult

local instance contenderDecision (spec : RaceSpec) (id : FiberId) :
    Decidable (RaceSpec.IsContender spec id) :=
  RaceSpec.isContenderDecidable spec id

local instance contenderDoneDecision (spec : RaceSpec) (state : RaceState τ)
    (id : FiberId) : Decidable (RaceState.ContenderDone spec state id) := by
  unfold RaceState.ContenderDone
  infer_instance

local instance needsWinnerDecision (spec : RaceSpec) (state : RaceState τ) :
    Decidable (RaceState.NeedsWinner spec state) :=
  RaceState.needsWinnerDecidable spec state

local instance beforeSelectionDecision (spec : RaceSpec)
    (decision : SchedulerDecision τ) :
    Decidable (RaceDecision.BeforeSelection spec decision) :=
  RaceDecision.beforeSelectionDecidable spec decision

local instance afterSelectionDecision (spec : RaceSpec) (winner : FiberId)
    (decision : SchedulerDecision τ) :
    Decidable (RaceDecision.AfterSelection spec winner decision) :=
  RaceDecision.afterSelectionDecidable spec winner decision

local instance raceActiveDecision (status : FiberStatus) :
    Decidable (FiberStatus.Active status) :=
  FiberStatus.activeDecidable status

/-- Pure interpretation of one explicit race decision. -/
def raceStepEval (boundary : InterruptBoundary τ) (spec : RaceSpec)
    (before : RaceState τ) : RaceDecision τ -> RaceStepResult τ
  | .scheduler decision =>
      match before.winner with
      | none =>
          if RaceState.NeedsWinner spec before then
            .refused .winnerSelectionRequired before
          else if RaceDecision.BeforeSelection spec decision then
            RaceStepResult.fromScheduler before
              (stepEval boundary before.machine decision)
          else
            .refused (.schedulerOutsideRace decision) before
      | some winner =>
          match RaceState.settledResult? spec before with
          | some _ => .refused (.raceSettled winner) before
          | none =>
              if RaceDecision.AfterSelection spec winner decision then
                RaceStepResult.fromScheduler before
                  (stepEval boundary before.machine decision)
              else
                .refused (.schedulerOutsideRace decision) before
  | .selectWinner attempted =>
      match before.winner with
      | some selected => .refused (.winnerAlreadySelected selected) before
      | none =>
          if RaceSpec.IsContender spec attempted then
            if RaceState.ContenderDone spec before attempted then
              match before.machine.fiber (spec.loser attempted) with
              | none =>
                  .refused (.scheduler (.unknownFiber (spec.loser attempted))) before
              | some loserState =>
                  if FiberStatus.Active loserState.status then
                    RaceStepResult.fromWinnerSelection attempted before
                      (stepEval boundary before.machine
                        (.requestInterrupt spec.coordinator
                          (spec.loser attempted)))
                  else
                    .advanced { before with winner := some attempted }
            else
              .refused (.winnerNotDone attempted) before
          else
            .refused (.winnerNotContender attempted) before

/-- The one-step race relation is exactly the evaluator graph. -/
def RaceStep (boundary : InterruptBoundary τ) (spec : RaceSpec)
    (before : RaceState τ) (decision : RaceDecision τ)
    (result : RaceStepResult τ) : Prop :=
  result = raceStepEval boundary spec before decision

/-- Replay checks settlement before consuming another recorded decision. -/
def raceReplayEval (boundary : InterruptBoundary τ) (spec : RaceSpec)
    (initial : RaceState τ) : RaceTape τ -> RaceReplayResult τ
  | [] =>
      match RaceState.settledResult? spec initial with
      | some result => .settled result initial
      | none => .frontier initial
  | decision :: rest =>
      match RaceState.settledResult? spec initial with
      | some result => .settled result initial
      | none =>
          match raceStepEval boundary spec initial decision with
          | .advanced middle => raceReplayEval boundary spec middle rest
          | .refused refusal stopped => .refused refusal stopped

/-- Race replay is admitted at the initial state and follows a fixed tape. -/
def RaceRuns (boundary : InterruptBoundary τ) (spec : RaceSpec)
    (initial : RaceState τ) (tape : RaceTape τ)
    (result : RaceReplayResult τ) : Prop :=
  RaceState.WellFormed spec initial /\
    result = raceReplayEval boundary spec initial tape

theorem raceStep_iff {boundary : InterruptBoundary τ} {spec before decision result} :
    RaceStep boundary spec before decision result <->
      result = raceStepEval boundary spec before decision :=
  Iff.rfl

theorem raceRuns_iff {boundary : InterruptBoundary τ} {spec initial tape result} :
    RaceRuns boundary spec initial tape result <->
      RaceState.WellFormed spec initial /\
        result = raceReplayEval boundary spec initial tape :=
  Iff.rfl

theorem raceStepEval_scheduler_before {boundary : InterruptBoundary τ}
    {spec before decision} (hwinner : before.winner = none)
    (hneeds : ¬ RaceState.NeedsWinner spec before)
    (hscope : RaceDecision.BeforeSelection spec decision) :
    raceStepEval boundary spec before (.scheduler decision) =
      RaceStepResult.fromScheduler before
        (stepEval boundary before.machine decision) := by
  simp [raceStepEval, hwinner, hneeds, hscope]

theorem raceStepEval_scheduler_needsWinner {boundary : InterruptBoundary τ}
    {spec before decision} (hwinner : before.winner = none)
    (hneeds : RaceState.NeedsWinner spec before) :
    raceStepEval boundary spec before (.scheduler decision) =
      .refused .winnerSelectionRequired before := by
  simp [raceStepEval, hwinner, hneeds]

theorem raceStepEval_scheduler_outside_before {boundary : InterruptBoundary τ}
    {spec before decision} (hwinner : before.winner = none)
    (hneeds : ¬ RaceState.NeedsWinner spec before)
    (hscope : ¬ RaceDecision.BeforeSelection spec decision) :
    raceStepEval boundary spec before (.scheduler decision) =
      .refused (.schedulerOutsideRace decision) before := by
  simp [raceStepEval, hwinner, hneeds, hscope]

theorem raceStepEval_scheduler_after {boundary : InterruptBoundary τ}
    {spec before winner decision} (hwinner : before.winner = some winner)
    (hsettled : RaceState.settledResult? spec before = none)
    (hscope : RaceDecision.AfterSelection spec winner decision) :
    raceStepEval boundary spec before (.scheduler decision) =
      RaceStepResult.fromScheduler before
        (stepEval boundary before.machine decision) := by
  simp [raceStepEval, hwinner, hsettled, hscope]

theorem raceStepEval_scheduler_outside_after {boundary : InterruptBoundary τ}
    {spec before winner decision} (hwinner : before.winner = some winner)
    (hsettled : RaceState.settledResult? spec before = none)
    (hscope : ¬ RaceDecision.AfterSelection spec winner decision) :
    raceStepEval boundary spec before (.scheduler decision) =
      .refused (.schedulerOutsideRace decision) before := by
  simp [raceStepEval, hwinner, hsettled, hscope]

theorem raceStepEval_scheduler_settled {boundary : InterruptBoundary τ}
    {spec before winner result decision} (hwinner : before.winner = some winner)
    (hsettled : RaceState.settledResult? spec before = some result) :
    raceStepEval boundary spec before (.scheduler decision) =
      .refused (.raceSettled winner) before := by
  simp [raceStepEval, hwinner, hsettled]

theorem raceStepEval_select_already {boundary : InterruptBoundary τ}
    {spec before selected attempted} (hwinner : before.winner = some selected) :
    raceStepEval boundary spec before (.selectWinner attempted) =
      .refused (.winnerAlreadySelected selected) before := by
  simp [raceStepEval, hwinner]

theorem raceStepEval_select_notContender {boundary : InterruptBoundary τ}
    {spec before attempted} (hwinner : before.winner = none)
    (hcontender : ¬ RaceSpec.IsContender spec attempted) :
    raceStepEval boundary spec before (.selectWinner attempted) =
      .refused (.winnerNotContender attempted) before := by
  simp [raceStepEval, hwinner, hcontender]

theorem raceStepEval_select_notDone {boundary : InterruptBoundary τ}
    {spec before attempted} (hwinner : before.winner = none)
    (hcontender : RaceSpec.IsContender spec attempted)
    (hdone : ¬ RaceState.ContenderDone spec before attempted) :
    raceStepEval boundary spec before (.selectWinner attempted) =
      .refused (.winnerNotDone attempted) before := by
  simp [raceStepEval, hwinner, hcontender, hdone]

theorem raceStepEval_select_missingLoser {boundary : InterruptBoundary τ}
    {spec before winner} (hwinner : before.winner = none)
    (hdone : RaceState.ContenderDone spec before winner)
    (hmissing : before.machine.fiber (spec.loser winner) = none) :
    raceStepEval boundary spec before (.selectWinner winner) =
      .refused (.scheduler (.unknownFiber (spec.loser winner))) before := by
  simp [raceStepEval, hwinner, hdone.1, hdone, hmissing]

theorem raceStepEval_select_active {boundary : InterruptBoundary τ}
    {spec before winner loserState} (hwinner : before.winner = none)
    (hdone : RaceState.ContenderDone spec before winner)
    (hfound : before.machine.fiber (spec.loser winner) = some loserState)
    (hactive : FiberStatus.Active loserState.status) :
    raceStepEval boundary spec before (.selectWinner winner) =
      RaceStepResult.fromWinnerSelection winner before
        (stepEval boundary before.machine
          (.requestInterrupt spec.coordinator (spec.loser winner))) := by
  simp [raceStepEval, hwinner, hdone.1, hdone, hfound, hactive]

theorem raceStepEval_select_inactive {boundary : InterruptBoundary τ}
    {spec before winner loserState} (hwinner : before.winner = none)
    (hdone : RaceState.ContenderDone spec before winner)
    (hfound : before.machine.fiber (spec.loser winner) = some loserState)
    (hinactive : ¬ FiberStatus.Active loserState.status) :
    raceStepEval boundary spec before (.selectWinner winner) =
      .advanced { before with winner := some winner } := by
  simp [raceStepEval, hwinner, hdone.1, hdone, hfound, hinactive]

theorem raceReplayEval_settled {boundary : InterruptBoundary τ}
    {spec initial result tape}
    (hsettled : RaceState.settledResult? spec initial = some result) :
    raceReplayEval boundary spec initial tape = .settled result initial := by
  simp [raceReplayEval, hsettled]

theorem raceReplayEval_nil_frontier {boundary : InterruptBoundary τ}
    {spec initial} (hsettled : RaceState.settledResult? spec initial = none) :
    raceReplayEval boundary spec initial [] = .frontier initial := by
  simp [raceReplayEval, hsettled]

theorem raceReplayEval_cons_advanced {boundary : InterruptBoundary τ}
    {spec initial decision tape middle}
    (hsettled : RaceState.settledResult? spec initial = none)
    (hstep : raceStepEval boundary spec initial decision = .advanced middle) :
    raceReplayEval boundary spec initial (decision :: tape) =
      raceReplayEval boundary spec middle tape := by
  simp [raceReplayEval, hsettled, hstep]

theorem raceReplayEval_cons_refused {boundary : InterruptBoundary τ}
    {spec initial decision tape refusal stopped}
    (hsettled : RaceState.settledResult? spec initial = none)
    (hstep : raceStepEval boundary spec initial decision =
      .refused refusal stopped) :
    raceReplayEval boundary spec initial (decision :: tape) =
      .refused refusal stopped := by
  simp [raceReplayEval, hsettled, hstep]

end Effect4
