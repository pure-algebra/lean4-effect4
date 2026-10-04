import Effect4.Laws.Program.Typed.Adequacy

set_option autoImplicit false
namespace KripkeWriteResearch
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed

abbrev W := Effect4.Program.Typed.World

def refTypes (key : RefKey) : Option Ty :=
  match key.index with
  | 0 => some (.refOf .nat)
  | 1 => some .nat
  | _ => none

def oldStore : Stores := { Stores.empty with refs := [Val.cell ⟨1⟩, Val.nat 0] }
def newStore : Stores := { oldStore with refs := [Val.cell ⟨0⟩, Val.nat 0] }
def before : W := { initialWorld (EffTy.pure .unit) with state := oldStore, Ρ := refTypes }
def after : W := { before with state := newStore }

theorem old_wf : oldStore.WF := by decide
theorem new_wf : newStore.WF := by decide

theorem original_fits : Fits before (Val.cell ⟨1⟩) (.refOf .nat) :=
  ⟨.nat, rfl, Ty.subN_refl _, Ty.subN_refl _⟩

theorem replacement_rejected : ¬ Fits before (Val.cell ⟨0⟩) (.refOf .nat) := by
  rintro ⟨ty, declared, compatible⟩
  change some (Ty.refOf .nat) = some ty at declared
  cases declared
  have incompatible : Ty.subN (.refOf .nat) .nat = false := by
    simp only [Ty.subN, Ty.normalize, Ty.sub, reduceCtorEq, if_false]
  have bad := compatible.1
  rw [incompatible] at bad
  cases bad

theorem replacement_coarsely_accepted : ValueOk before (.refOf .nat) (Val.cell ⟨0⟩) := rfl

theorem old_store_typed : StoreTyped before := by
  constructor
  · intro key
    rcases key with ⟨i⟩
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ i =>
        change (false = true) ↔ i + 2 < 2
        constructor
        · intro h; cases h
        · intro h; omega
  · intro key
    change (false = true) ↔ key.index < 0
    constructor
    · intro h; cases h
    · intro h; omega
  · intro i v hv ty hty
    cases i with
    | zero =>
      change some (Val.cell ⟨1⟩) = some v at hv
      cases hv
      change some (Ty.refOf .nat) = some ty at hty
      cases hty
      exact original_fits
    | succ i =>
      cases i with
      | zero =>
        change some (Val.nat 0) = some v at hv
        cases hv
        change some Ty.nat = some ty at hty
        cases hty
        trivial
      | succ i =>
        change ([] : List Val)[i]? = some v at hv
        simp only [List.getElem?_nil] at hv
        cases hv
  · intro e he
    cases he
  · intro m hm
    cases hm

theorem actual_write :
    syncOpStep (.refSet ⟨0⟩ (Val.cell ⟨0⟩)) before.state =
      some (after.state, Val.cell ⟨0⟩) := rfl

theorem coarse_cells_preserved : CellCompatible before after := by
  constructor
  · intro key ty h
    rcases key with ⟨i⟩
    cases i with
    | zero =>
      have declared := h.1
      change some (Ty.refOf .nat) = some ty at declared
      cases declared
      refine ⟨rfl, ?_⟩
      intro v hv
      change some (Val.cell ⟨0⟩) = some v at hv
      cases hv
      rfl
    | succ i =>
      cases i with
      | zero =>
        have declared := h.1
        change some Ty.nat = some ty at declared
        cases declared
        refine ⟨rfl, ?_⟩
        intro v hv
        change some (Val.nat 0) = some v at hv
        cases hv
        rfl
      | succ i => cases h.1
  · intro key types h
    cases h.1

theorem actual_order : before.leHost after :=
  ⟨⟨⟨fun _ h => h, syncOpStep_le _ _ _ _ actual_write⟩,
    fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, coarse_cells_preserved,
    fun _ _ _ h => h, rfl⟩, fun _ _ h => h⟩

theorem new_store_not_typed : ¬ StoreTyped after := by
  intro typed
  have h := typed.values 0 (Val.cell ⟨0⟩) rfl (.refOf .nat) rfl
  exact replacement_rejected h

theorem real_protocol_refuses (root : ProgramSource) :
    ¬ storePre root before (.refSet ⟨0⟩ (Val.cell ⟨0⟩)) () := by
  rintro ⟨ty, declared, fits⟩
  change some (Ty.refOf .nat) = some ty at declared
  cases declared
  exact replacement_rejected fits

theorem real_protocol_accepts_control (root : ProgramSource) :
    storePre root before (.refSet ⟨0⟩ (Val.cell ⟨1⟩)) () :=
  ⟨.refOf .nat, rfl, original_fits⟩

theorem real_handler_preserves_control (root : ProgramSource) :
    ∃ st' ans, syncOpStep (.refSet ⟨0⟩ (Val.cell ⟨1⟩)) before.state = some (st', ans) ∧
      ∃ w', before.leHost w' ∧ w'.state = st' ∧ StoreTyped w' ∧
        storePost w' (.refSet ⟨0⟩ (Val.cell ⟨1⟩)) () ans :=
  refSet_implements root ⟨0⟩ (Val.cell ⟨1⟩) before () old_store_typed
    (real_protocol_accepts_control root)

#print axioms old_wf
#print axioms new_wf
#print axioms original_fits
#print axioms replacement_rejected
#print axioms replacement_coarsely_accepted
#print axioms old_store_typed
#print axioms actual_write
#print axioms coarse_cells_preserved
#print axioms actual_order
#print axioms new_store_not_typed
#print axioms real_protocol_refuses
#print axioms real_protocol_accepts_control
#print axioms real_handler_preserves_control
end KripkeWriteResearch
