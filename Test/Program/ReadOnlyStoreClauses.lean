import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
Concept4 controls for the exact read-only StoreClauseKeeps interface.
Consumers: configTyped_cons_drainDue / Evaluating.store_same / clause_refGet.
The queue statements inspect actual preparation and settlement. The reference
fixtures test the precise row pre/post and actual read; they are deliberately
not claimed ConfigTyped or reachable. No premise of the production goal changes.
Source-only draft against frozen f4d8be8f; the coordinator owns compilation.
Append after ReadOnlyStoreClauses.lean; no extra imports or runtime definitions.
-/
namespace Effect4.Program.Typed.ReadOnlyStoreControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed

/-- Answered store work drains before delivery, for every tail and machine. -/
theorem answered_queue (m : RState) (f : RFiber) (y : Bool) (rest : List RCmd) :
    (settle f.id rest (prepareIterR
      (⟨m, f, y, .answered, [.drainDue]⟩ : RIter))).2 =
      .drainDue :: .deliver f.id y :: rest := rfl

theorem answered_queue_nonempty (m : RState) (f : RFiber) (y : Bool) (rest : List RCmd) :
    (settle f.id rest (prepareIterR
      (⟨m, f, y, .answered, [.drainDue]⟩ : RIter))).2 ≠ [] := by
  rw [answered_queue]
  intro h
  cases h

theorem drain_elision_refused (m : RState) (f : RFiber) (y : Bool) (rest : List RCmd) :
    (settle f.id rest (prepareIterR
      (⟨m, f, y, .answered, [.drainDue]⟩ : RIter))).2 ≠
      .deliver f.id y :: rest := by
  rw [answered_queue]
  intro h
  cases h

abbrev W := Effect4.Program.Typed.World
def key : RefKey := ⟨0⟩

/-- A one-slot physical heap and precisely its nat declaration; the value is varied. -/
def natSlot (value : Val) : W :=
  { initialWorld (EffTy.pure Ty.unit) with
    state := { Stores.empty with refs := [value] }
    Ρ := fun k => if k.index = 0 then some Ty.nat else none }

def badWorld : W := natSlot (Val.str "bad")
def goodWorld : W := natSlot (Val.nat 7)
def undeclaredWorld : W := { goodWorld with Ρ := fun _ => none }

/-- Declaration alone admits the request. -/
theorem bad_pre (root : ProgramSource) :
    storePre root badWorld (.refGet key) PUnit.unit := ⟨Ty.nat, rfl⟩

/-- The actual read succeeds, but returns the mismatched stored value. -/
theorem bad_read : syncOpStep (.refGet key) badWorld.state =
    some (badWorld.state, Val.str "bad") := rfl

theorem bad_post_refused :
    ¬ storePost badWorld (.refGet key) PUnit.unit (Val.str "bad") := by
  intro ⟨ty, declared, fit⟩
  have same : Ty.nat = ty := Option.some.inj declared
  cases same
  exact fit

/-- Matching the declared type admits both the request and the actual result. -/
theorem good_pre (root : ProgramSource) :
    storePre root goodWorld (.refGet key) PUnit.unit := ⟨Ty.nat, rfl⟩

theorem good_read : syncOpStep (.refGet key) goodWorld.state =
    some (goodWorld.state, Val.nat 7) := rfl

theorem good_post : storePost goodWorld (.refGet key) PUnit.unit (Val.nat 7) :=
  ⟨Ty.nat, rfl, True.intro⟩

/-- Physical allocation does not supply the ghost declaration demanded by the contract. -/
theorem undeclared_read : syncOpStep (.refGet key) undeclaredWorld.state =
    some (undeclaredWorld.state, Val.nat 7) := rfl

theorem undeclared_pre_refused (root : ProgramSource) :
    ¬ storePre root undeclaredWorld (.refGet key) PUnit.unit := by
  intro ⟨ty, declared⟩
  cases declared

theorem undeclared_post_refused :
    ¬ storePost undeclaredWorld (.refGet key) PUnit.unit (Val.nat 7) := by
  intro ⟨ty, declared, _⟩
  cases declared

