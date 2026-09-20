import Effect4.Laws.Program.Typed.State
open Lean Meta Elab Command Effect4.Laws.Auto.Positions
run_cmd liftTermElabM do
  let env ← getEnv
  for root in [``Effect4.Program.Sched.RState, ``Effect4.Program.Sched.RCmd] do
    let w ← walkOf root
    let mut overlap := #[]
    let mut single := #[]
    for p in w.positions do
      if w.edges.any (fun e => e.parent == p.owner && e.field == p.field) then
        overlap := overlap.push p.key
      let info ← getConstInfoInduct p.owner
      if info.ctors.length == 1 && !isStructure env p.owner then
        single := single.push p.key
    logInfo m!"{root}: mixed fields {overlap.toList.eraseDups}; single non-structure fields {single.toList.eraseDups}"

namespace Review.ColumnOnly
open Effect4.Program.Typed
inductive Expect | root
structure Store where
  payload : Effect4.Store.Val
structure Parent where
  store : Store
def sources : List Row := [("Review.ColumnOnly.Store.payload", .column "Heap")]
#typed_state Review.ColumnOnly.Parent using sources columns Review.ColumnOnly.Store
-- If accepted, the selected store's column contributes no clause.
theorem everyParent {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent) : ParentOk P w e x := ⟨True.intro⟩
#print ParentOk
#print axioms everyParent
end Review.ColumnOnly
