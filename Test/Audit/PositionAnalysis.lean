import Effect4.Laws.Auto.Positions
import Effect4.Store.Val

open Lean Meta Elab Command Effect4.Laws.Auto.Positions

namespace Test.PositionAnalysis

structure Cell where
  tracked : Nat
  other : Nat

def copyTracked (s t : Cell) : Cell := {s with tracked := t.tracked}
def readMatched (s : Cell) : Nat := match s with | .mk tracked _ => tracked
def readProjected (s : Cell) : Nat := s.tracked
def readWhole (p : Cell → Prop) (s : Cell) : Prop := p s

structure Box (α : Type) where
  value : α
structure Mixed where
  plain : Box Nat
  typed : Box Effect4.Store.Val
inductive Deep (α : Type) where
  | leaf : α → Deep α
  | next : Deep α → Deep α
structure Recursive where
  tree : Deep Effect4.Store.Val

run_cmd liftTermElabM do
  let w ← walkOf ``Mixed
  unless w.positions.any (fun p => p.owner == ``Box && p.carrier == ``Effect4.Store.Val) do
    throwError "the second container instance was skipped"

run_cmd liftTermElabM do
  let env ← getEnv
  for n in [``readMatched, ``readProjected, ``readWhole] do
    let some v := (← getConstInfo n).value? | throwError "missing body"
    let reads ← readSites env [``Cell] 1000 v #[]
    unless reads.contains (``Cell, "tracked") do throwError "missed dependency in {n}"

run_cmd liftTermElabM do
  let env ← getEnv
  let some v := (← getConstInfo ``copyTracked).value? | throwError "missing body"
  let writes ← writeSites env [``Cell] ``copyTracked 1000 v #[]
  unless writes.any (·.fields.contains "tracked") do throwError "cross-record copy was omitted"

run_cmd liftTermElabM do
  let env ← getEnv
  let some v := (← getConstInfo ``copyTracked).value? | throwError "missing body"
  lambdaTelescope v fun xs body => do
    let writes ← writeSites env [``Cell] ``copyTracked 1000 body #[] (some xs[0]!)
    unless writes.any (·.fields.contains "tracked") do throwError "cross-record copy was omitted"
    if writes.any (·.fields.contains "other") then throwError "unchanged source field was counted"
  let some v := (← getConstInfo ``readProjected).value? | throwError "missing body"
  let reads ← readSites env [``Cell] 1000 v #[]
  unless reads == #[( ``Cell, "tracked")] do throwError "projection lost its precision"

/-- error: position analysis: closure scan ran out of work at Test.PositionAnalysis.copyTracked -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| closure (← getEnv) ``copyTracked #[] `Test 0

/-- error: position analysis: write scan ran out of depth -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| writeSites (← getEnv) [``Cell] ``copyTracked 0 (mkConst ``copyTracked) #[]

/-- error: position analysis: read scan ran out of depth -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| readSites (← getEnv) [``Cell] 0 (mkConst ``readWhole) #[]

/-- error: REFUSED Test.PositionAnalysis.Recursive.tree: recursive type Test.PositionAnalysis.Deep needs an explicit carrier or wrapper -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| walkOf ``Recursive

end Test.PositionAnalysis
