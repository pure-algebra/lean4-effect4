import Effect4.Laws.Program.StoreComodel

/-!
# The store handler as a comodel of state: controls

Controls for `src/Effect4/Laws/Program/StoreComodel.lean` (formal pass, algebra note A9, probe
`P4ComodelIteration.lean`). Positive: put-get and put-put on a store holding one cell. Red: on a
cell the store never allocated (a "dead" cell), the handler's fallback answers `Val.unit`
whatever was written, so put-get fails (`put_get_dead_fails`, `E4-DEN-CE-002` read in comodel
terms), and the law refuses that cell at its premise (pinned below).
-/

set_option autoImplicit false
namespace Test.Program.StoreComodel
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A store holding one cell, at index 0. -/
def oneCell : Stores := { Stores.empty with refs := [Val.nat 0] }

theorem put_get_one_cell :
    runP (storeOp (.refSet ⟨0⟩ (Val.nat 7)) >>= fun _ => storeOp (.refGet ⟨0⟩)) oneCell =
      (Val.nat 7, { oneCell with refs := [Val.nat 7] }) :=
  put_get (s := oneCell) (c := ⟨0⟩) (by decide) (Val.nat 7)

theorem put_put_one_cell :
    runP (storeOp (.refSet ⟨0⟩ (Val.nat 7)) >>= fun _ => storeOp (.refSet ⟨0⟩ (Val.nat 8))) oneCell =
      runP (storeOp (.refSet ⟨0⟩ (Val.nat 8))) oneCell :=
  put_put (s := oneCell) (c := ⟨0⟩) (by decide) (Val.nat 7) (Val.nat 8)

/-- **Red control: put-get fails on a cell the store never allocated.** The fallback answers
`Val.unit` whatever was written, so the store is a lawful comodel of state on its allocated
cells only. -/
theorem put_get_dead_fails :
    runP (storeOp (.refSet ⟨0⟩ (Val.nat 7)) >>= fun _ => storeOp (.refGet ⟨0⟩)) Stores.empty ≠
      (Val.nat 7, Stores.empty) := by
  have hd : ¬ (⟨0⟩ : RefKey).index < Stores.empty.refs.length := Nat.lt_irrefl 0
  have h1 : runP (storeOp (.refSet ⟨0⟩ (Val.nat 7))) Stores.empty = (Val.unit, Stores.empty) := by
    rw [runP_storeOp, (syncOpStep_ref_unallocated hd (Val.nat 7)).1]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_storeOp, (syncOpStep_ref_unallocated hd (Val.nat 7)).2]
  intro heq
  injection heq with hv
  cases hv

/-! The law refuses the dead cell at its premise. -/

/--
error: Tactic `decide` proved that the proposition
  { index := 0 }.index < List.length Stores.empty.refs
is false
-/
#guard_msgs (error) in
example :
    runP (storeOp (.refSet ⟨0⟩ (Val.nat 7)) >>= fun _ => storeOp (.refGet ⟨0⟩)) Stores.empty =
      (Val.nat 7, { Stores.empty with refs := Stores.empty.refs.set 0 (Val.nat 7) }) :=
  put_get (s := Stores.empty) (c := ⟨0⟩) (by decide) (Val.nat 7)

#print axioms put_get_one_cell
#print axioms put_put_one_cell
#print axioms put_get_dead_fails
end Test.Program.StoreComodel
