import Test.Dogfood.Scenario.Atomic.StageWorld

/-!
Concept: store-typing R4.
Consumer: the actual decision and deposit heap transitions of `Atomic.Store.shop_stages`.
Changing one request stage changes exactly its one contribution to the finite stage counts.
This arithmetic establishes no history invariant.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program
open Store (Stage)

/-- A request outside a list leaves every count in that list unchanged. -/
theorem filter_setStage_away (world : World) (id : Nat) (next : Stage) (test : Stage → Bool)
    (ids : List Nat) (absent : id ∉ ids) :
    (ids.filter fun key => test ((setStage world id next).stages key)) =
      ids.filter (fun key => test (world.stages key)) := by
  apply List.filter_congr
  intro key member
  have different : key ≠ id := by
    intro same
    exact absent (same ▸ member)
  simp only [setStage, if_neg different]

/-- A single stage replacement changes precisely one summand of a count. -/
theorem filter_setStage_count (world : World) (id : Nat) (next : Stage) (test : Stage → Bool)
    (ids : List Nat) (distinct : ids.Nodup) (present : id ∈ ids) :
    (ids.filter fun key => test ((setStage world id next).stages key)).length +
        (if test (world.stages id) then 1 else 0) =
      (ids.filter fun key => test (world.stages key)).length + (if test next then 1 else 0) := by
  induction ids with
  | nil => cases present
  | cons key rest ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp distinct
    by_cases same : key = id
    · subst key
      rw [List.filter_cons, List.filter_cons, filter_setStage_away world id next test rest absent]
      simp only [setStage, ↓reduceIte]
      cases test next <;> cases test (world.stages id) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · have member : id ∈ rest := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      have smaller := ih unique member
      dsimp only [setStage] at smaller
      simp only [List.filter_cons, setStage, if_neg same]
      cases test (world.stages key) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
/-- The window admission count includes both admitted and deposited requests. -/
def admittedCount (world : World) : Nat := (requests.filter fun id => (world.stages id).counts).length

/-- The window rejection count includes precisely the rejected requests. -/
def rejectedCount (world : World) : Nat := (requests.filter fun id => decide (world.stages id = .rejected)).length

/-- The account length includes precisely the deposited requests. -/
def depositedCount (world : World) : Nat := (requests.filter fun id => decide (world.stages id = .deposited)).length

/-- Each real request appears once in the source census. -/
theorem requests_distinct : requests.Nodup := by decide

/-- An admitted decision increments only the admission count. -/
theorem count_admit (world : World) (id : Nat) (member : id ∈ requests)
    (waiting : world.stages id = .waiting) :
    admittedCount (setStage world id .admitted) = admittedCount world + 1 ∧
    rejectedCount (setStage world id .admitted) = rejectedCount world ∧
    depositedCount (setStage world id .admitted) = depositedCount world := by
  have admitted := filter_setStage_count world id .admitted Stage.counts requests requests_distinct member
  have rejected := filter_setStage_count world id .admitted (fun stage => decide (stage = .rejected)) requests requests_distinct member
  have deposited := filter_setStage_count world id .admitted (fun stage => decide (stage = .deposited)) requests requests_distinct member
  simp only [waiting, Stage.counts, Bool.false_eq_true, ↓reduceIte] at admitted
  simp only [waiting, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at rejected deposited
  exact ⟨admitted, rejected, deposited⟩

/-- A rejected decision increments only the rejection count. -/
theorem count_reject (world : World) (id : Nat) (member : id ∈ requests)
    (waiting : world.stages id = .waiting) :
    admittedCount (setStage world id .rejected) = admittedCount world ∧
    rejectedCount (setStage world id .rejected) = rejectedCount world + 1 ∧
    depositedCount (setStage world id .rejected) = depositedCount world := by
  have admitted := filter_setStage_count world id .rejected Stage.counts requests requests_distinct member
  have rejected := filter_setStage_count world id .rejected (fun stage => decide (stage = .rejected)) requests requests_distinct member
  have deposited := filter_setStage_count world id .rejected (fun stage => decide (stage = .deposited)) requests requests_distinct member
  simp only [waiting, Stage.counts, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at admitted
  simp only [waiting, reduceCtorEq, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at rejected
  simp only [waiting, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at deposited
  exact ⟨admitted, rejected, deposited⟩

/-- A deposit retains both decision counts and increments only the account length. -/
theorem count_deposit (world : World) (id : Nat) (member : id ∈ requests)
    (selected : world.stages id = .admitted) :
    admittedCount (setStage world id .deposited) = admittedCount world ∧
    rejectedCount (setStage world id .deposited) = rejectedCount world ∧
    depositedCount (setStage world id .deposited) = depositedCount world + 1 := by
  have admitted := filter_setStage_count world id .deposited Stage.counts requests requests_distinct member
  have rejected := filter_setStage_count world id .deposited (fun stage => decide (stage = .rejected)) requests requests_distinct member
  have deposited := filter_setStage_count world id .deposited (fun stage => decide (stage = .deposited)) requests requests_distinct member
  simp only [selected, Stage.counts, ↓reduceIte] at admitted
  simp only [selected, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at rejected
  simp only [selected, reduceCtorEq, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at deposited
  exact ⟨Nat.add_right_cancel admitted, rejected, deposited⟩
end Test.Dogfood.Scenario.Atomic.StageWorld
