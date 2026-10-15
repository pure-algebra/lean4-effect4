import Test.Dogfood.Scenario.Atomic.Writes
import Effect4.Laws.Machine.AnswerFlow

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the external world of `Atomic.Store.shop_stages` retains erased request stages.
Consumer: its native decision, deposit and cleanup producers and saved-answer family.
The world advances with the actual primitive answer; a waiting decision has no admitted answer.
These local producers establish no command or history invariant by themselves.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program
open Store (Stage)

/-- A request decides once, and an admitted request can deposit once. -/
inductive Advances : Stage → Stage → Prop
  | refl (stage : Stage) : Advances stage stage
  | waiting (stage : Stage) : Advances .waiting stage
  | deposit : Advances .admitted .deposited

theorem Advances.trans {first middle last : Stage}
    (one : Advances first middle) (two : Advances middle last) : Advances first last := by
  cases one with
  | refl => exact two
  | waiting => exact .waiting _
  | deposit => cases two; exact .deposit

/-- Cleanup evidence survives code erasure independently of the request's stage. -/
structure World where
  stages : Nat → Stage
  cleaned : Nat → Bool

/-- A future world retains every earlier stage transition and positive cleanup witness. -/
def Future (before after : World) : Prop :=
  (∀ id, Advances (before.stages id) (after.stages id)) ∧
    ∀ id, before.cleaned id = true → after.cleaned id = true

/-- The coupled driver orders the external stage world independently of machine stores. -/
def order : Effect4.Laws.Effects.WorldOrder World where
  le := Future
  refl _world := ⟨fun _id => .refl _, fun _ held => held⟩
  trans one two := ⟨fun id => (one.1 id).trans (two.1 id), fun id held => two.2 id (one.2 id held)⟩

/-- Only the acting request changes stage at its actual write. -/
def setStage (world : World) (id : Nat) (stage : Stage) : World :=
  {world with stages := fun selected => if selected = id then stage else world.stages selected}

/-- A real positive cleanup read appends evidence; it never erases earlier evidence. -/
def markCleaned (world : World) (id : Nat) (positive : Bool) : World :=
  {world with cleaned := fun selected =>
    if selected = id then world.cleaned selected || positive else world.cleaned selected}

theorem setStage_future (world : World) (id : Nat) (stage : Stage)
    (step : Advances (world.stages id) stage) : Future world (setStage world id stage) := by
  refine ⟨?_, fun _ held => held⟩
  intro selected
  by_cases same : selected = id
  · subst selected
    simpa only [setStage, ↓reduceIte] using step
  · simpa only [setStage, if_neg same] using Advances.refl (world.stages selected)

theorem markCleaned_future (world : World) (id : Nat) (positive : Bool) :
    Future world (markCleaned world id positive) := by
  refine ⟨fun selected => .refl _, ?_⟩
  intro selected held
  by_cases same : selected = id
  · simp only [markCleaned, if_pos same, held, Bool.true_or]
  · simpa only [markCleaned, if_neg same] using held

/-- The decision and deposit answers differ from the request's final Boolean answer. -/
inductive Kind
  | ordinary
  | decision (id : Nat)
  | deposit (id : Nat)
  | body (id : Nat)
  | finalized (id : Nat)
  | note (id : Nat)

/-- A returned decision is usable only between that decision and its deposit.
Consumer: the actual decision continuation's saved-answer contract. -/
def ValueAt (world : World) : Kind → Val → Prop
  | .ordinary, _ => True
  | .decision id, .bool admitted =>
    world.stages id = if admitted then .admitted else .rejected
  | .deposit id, .nat _ => world.stages id = .deposited
  | .body id, .bool admitted | .finalized id, .bool admitted =>
    world.stages id = if admitted then .deposited else .rejected
  | .note id, value => value = .unit ∧ (world.stages id = .deposited → world.cleaned id = true)
  | _, _ => False

/-- A typed body failure stands behind a deposit; finalization also retains its cleanup witness. -/
def CauseAt (world : World) : Kind → CauseV → Prop
  | .ordinary, _ => True
  | .body id, cause => ∀ reason ∈ cause.reasons, reason.tag = .fail → world.stages id = .deposited
  | .finalized id, cause => ∀ reason ∈ cause.reasons, reason.tag = .fail →
      world.stages id = .deposited ∧ world.cleaned id = true
  | .note id, cause => (∀ reason ∈ cause.reasons, reason.tag ≠ .fail) ∧
      (world.stages id = .deposited → world.cleaned id = true)
  | _, cause => ∀ reason ∈ cause.reasons, reason.tag ≠ .fail

/-- Finalizer restoration retains the body's Boolean stage certificate.
Consumer: the request's actual restore-name saved contract. -/
theorem restored_value (world : World) (id : Nat) (value : Val)
    (body : ValueAt world (.body id) value) : ValueAt world (.finalized id) value := by
  fun_cases ValueAt world (.body id) value
  all_goals aesop (add norm simp [ValueAt])

/-- A real cleanup completion supplies the evidence needed to restore a typed body failure.
Consumer: the finalizer's restore and merge saved contracts. -/
theorem restored_cause (world : World) (id : Nat) (cause : CauseV)
    (body : CauseAt world (.body id) cause) (note : ValueAt world (.note id) .unit) :
    CauseAt world (.finalized id) cause := by
  intro reason member typed
  have deposited := body reason member typed
  exact ⟨deposited, note.2 deposited⟩

/-- A finalizer failure supplies no new typed reason and retains cleanup evidence.
Consumer: the actual failure-merge name following an installed request finalizer. -/
theorem merged_cause (world : World) (id : Nat) (body finalizer : CauseV)
    (original : CauseAt world (.body id) body)
    (finished : CauseAt world (.note id) finalizer) :
    CauseAt world (.finalized id) (Cause.combine body finalizer) := by
  intro reason member typed
  rcases Cause.combine_no_new_reason reason body finalizer member with prior | cleanup
  · have deposited := original reason prior typed
    exact ⟨deposited, finished.2 deposited⟩
  · exact False.elim (finished.1 reason cleanup typed)

/-- A later outside interrupt cannot erase a finalized request's deposit or cleanup evidence.
Consumer: contextual interruption of a completed request role. -/
theorem interrupted_cause (world : World) (id : Nat) (body interruption : CauseV)
    (original : CauseAt world (.finalized id) body)
    (outside : ∀ reason ∈ interruption.reasons, reason.tag ≠ .fail) :
    CauseAt world (.finalized id) (Cause.combine body interruption) := by
  intro reason member typed
  rcases Cause.combine_no_new_reason reason body interruption member with prior | added
  · exact original reason prior typed
  · exact False.elim (outside reason added typed)

/-- The actual decision chooses its next stage and its answer in the same primitive step. -/
theorem decision (world : World) (id : Nat) (waiting : world.stages id = .waiting)
    (state : Stores) (env : List Val) (used admitted rejected : Nat)
    (stored : refPeek state.refs ⟨0⟩ = some (Test.Dogfood.P4RateLimiter.windowVal used admitted rejected)) :
    let selected := decide (used < 3)
    let next := setStage world id (if selected then .admitted else .rejected)
    ∃ after answer,
      syncOpStep (.refModify ⟨0⟩ (Store.decisionAt env.length) env) state = some (after, answer) ∧
      Future world next ∧ ValueAt next (.decision id) answer := by
  dsimp only
  have actual := Store.Writes.decision_step state ⟨0⟩ env used admitted rejected stored
  have advance (stage : Stage) : Advances (world.stages id) stage := by
    rw [waiting]
    exact .waiting stage
  cases selected : decide (used < 3) with
  | false =>
    rw [selected] at actual
    refine ⟨_, .bool false, actual, setStage_future world id .rejected (advance _), ?_⟩
    simp only [ValueAt, setStage, Bool.false_eq_true, ↓reduceIte]
  | true =>
    rw [selected] at actual
    refine ⟨_, .bool true, actual, setStage_future world id .admitted (advance _), ?_⟩
    simp only [ValueAt, setStage, ↓reduceIte]

/-- The real deposit advances precisely its acting request and certifies the returned balance. -/
theorem deposit (world : World) (id : Nat) (admitted : world.stages id = .admitted)
    (state : Stores) (env : List Val) (ids : List Nat)
    (stored : refPeek state.refs ⟨1⟩ = some (Store.Writes.account ids)) :
    ∃ after answer,
      syncOpStep (.refModify ⟨1⟩ (Store.depositAt id env.length) env) state = some (after, answer) ∧
      Future world (setStage world id .deposited) ∧
      ValueAt (setStage world id .deposited) (.deposit id) answer := by
  refine ⟨_, .nat (ids.sum + id), Store.Writes.deposit_step state ⟨1⟩ env ids id stored, ?_, ?_⟩
  · apply setStage_future
    rw [admitted]
    exact .deposit
  · simp only [ValueAt, setStage, ↓reduceIte]

/-- A real cleanup note retains the positive count required by a deposited failure's restoration. -/
theorem note (world : World) (id : Nat) (state : Stores) (env : List Val)
    (used admitted rejected : Nat) (log : List Val)
    (positive : world.stages id = .deposited → 1 ≤ admitted + rejected)
    (stored : refPeek state.refs ⟨2⟩ = some (.list log)) :
    let next := markCleaned world id (decide (1 ≤ admitted + rejected))
    ∃ after,
      syncOpStep (.refUpdate ⟨2⟩ (Store.noteAt id (env.length + 1))
        (env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected])) state = some (after, .unit) ∧
      Future world next ∧ ValueAt next (.note id) .unit := by
  dsimp only
  refine ⟨_, Store.Writes.note_step state ⟨2⟩ env used admitted rejected id log stored,
    markCleaned_future world id _, rfl, ?_⟩
  intro deposited
  have seen := positive deposited
  simp only [markCleaned, decide_eq_true seen, Bool.or_true, ↓reduceIte]
end Test.Dogfood.Scenario.Atomic.StageWorld
