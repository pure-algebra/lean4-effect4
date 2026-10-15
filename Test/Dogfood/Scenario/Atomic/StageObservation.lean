import Test.Dogfood.Scenario.Atomic.StageFrames

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the observation at every cut of `Atomic.Store.shop_stages`.
The actual published request exits carry their finalized answer classes.
The heap supplies the finite counts and actual positive cleanup entries.
These readout laws establish no producer over histories.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program
open Store (Stage)

/-- A published exit retains its own actual finalized request answer. -/
def FinalExitAt (world : World) (id : Nat) : Option ExitV → Prop
  | none => True
  | some (.success value) => ValueAt world (.finalized id) value
  | some (.failure cause) => CauseAt world (.finalized id) cause

/-- The planted typed failure's finalized class contains both deposit and cleanup evidence. -/
theorem downstream_finished (world : World) (id : Nat) (good : FinalExitAt world id (some downstream)) :
    world.stages id = .deposited ∧ world.cleaned id = true :=
  good downstream_needs

/-- Reading a finalized request exit reports only its certified deposited or rejected stage. -/
theorem outcome_stages (world : World) (id : Nat) (exit : Option ExitV) (good : FinalExitAt world id exit) :
    ((outcomeOf exit).isAdmitted = true → world.stages id = .deposited) ∧
    (outcomeOf exit = .rejected → world.stages id = .rejected) ∧
    (outcomeOf exit = .failedBehind → world.cleaned id = true) := by
  unfold outcomeOf
  split
  · rename_i selected
    have same : exit = some downstream := beq_iff_eq.mp selected
    subst exit
    obtain ⟨deposited, cleaned⟩ := downstream_finished world id good
    exact ⟨fun _ => deposited, (fun impossible => by cases impossible), fun _ => cleaned⟩
  · cases exit with
    | none => exact ⟨(fun impossible => by cases impossible), (fun impossible => by cases impossible), (fun impossible => by cases impossible)⟩
    | some exit =>
      cases exit with
      | success value =>
        change ValueAt world (.finalized id) value at good
        cases value with
        | bool admitted =>
          cases admitted with
          | false => exact ⟨(fun impossible => by cases impossible), (fun _ => good), (fun impossible => by cases impossible)⟩
          | true => exact ⟨(fun _ => good), (fun impossible => by cases impossible), (fun impossible => by cases impossible)⟩
        | _ => exact good.elim
      | failure cause =>
        dsimp only
        split
        all_goals exact ⟨(fun impossible => by cases impossible), (fun impossible => by cases impossible), (fun impossible => by cases impossible)⟩
/-- Every actual published request exit carries its own finalized answer class. -/
def Published (world : World) (machine : NativeMachine) : Prop :=
  ∀ id ∈ requests, FinalExitAt world id ((machine.fiber? ⟨id + 1⟩).bind RunFiber.exit)

/-- An actual positive cleanup entry is visible in the scenario's cleanup observation. -/
theorem positive_observed (id : Nat) (log : List Val) (held : PositiveLog id log) (observation : Observation)
    (cleanups : observation.cleanups = log) :
    (observation.sawAt id).any (fun seen => decide (1 ≤ seen)) = true := by
  obtain ⟨seen, member, positive⟩ := held
  apply List.any_eq_true.mpr
  refine ⟨seen, ?_, decide_eq_true positive⟩
  change seen ∈ observation.cleanups.filterMap _
  rw [cleanups]
  apply List.mem_filterMap.mpr
  refine ⟨.list [.nat id, .nat seen], member, ?_⟩
  have self : (id == id) = true := @beq_self_eq_true Nat _ Nat.instLawfulBEq.toReflBEq id
  simp only [self, ↓reduceIte]

/-- A mapped list paired with its source retains each element's actual identity. -/
theorem zip_map_diagonal {A B : Type} (f : A → B) (values : List A) :
    (values.map f).zip values = values.map (fun value => (f value, value)) := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The actual heap and published exits determine the complete requested stage observation. -/
theorem observation_fit (world : World) (machine : NativeMachine)
    (heap : HeapAt world machine.state) (published : Published world machine) :
    Store.StagesFit world.stages (Store.observeM machine) := by
  obtain ⟨used, ids, log, refs, counts, length, owned, cleaned⟩ := heap.witness
  have account : (Store.observeM machine).account = some (Store.Writes.account ids) := by
    change machine.state.refs[1]? = _
    rw [refs]
    rfl
  have deposits : (Store.observeM machine).deposits = ids := by
    simpa only [Observation.deposits, account] using Store.Writes.deposits_account (Store.observeM machine) ids
  have cleanups : (Store.observeM machine).cleanups = log := by
    change entries machine.state.refs[2]? = log
    rw [refs]
    rfl
  have decisions : (Store.observeM machine).decisions = requests.map
      (fun id => outcomeOf ((machine.fiber? ⟨id + 1⟩).bind RunFiber.exit)) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · change natField machine.state.refs[0]? "admitted" = admittedCount world
    rw [refs]
    rfl
  · change natField machine.state.refs[0]? "rejected" = rejectedCount world
    rw [refs]
    rfl
  · intro id member
    rw [deposits]
    exact counts id member
  · rw [deposits]
    exact length
  · rw [deposits]
    apply List.all_eq_true.mpr
    intro id member
    exact List.contains_iff_mem.mpr (owned id member)
  · intro pair member
    rw [decisions, zip_map_diagonal] at member
    obtain ⟨id, present, same⟩ := List.mem_map.mp member
    cases same
    have observed := outcome_stages world id _ (published id present)
    exact ⟨observed.1, observed.2.1⟩
  · intro failed
    have actual : outcomeOf ((machine.fiber? ⟨3⟩).bind RunFiber.exit) = .failedBehind := Option.some.inj failed
    have finished := (outcome_stages world 2 _ (published 2 (by decide))).2.2 actual
    exact positive_observed 2 log (cleaned 2 finished) (Store.observeM machine) cleanups
end Test.Dogfood.Scenario.Atomic.StageWorld
