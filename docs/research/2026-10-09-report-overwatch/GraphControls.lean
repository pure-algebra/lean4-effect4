import Tools.Semantics

/-! Finite cache controls for proof-report dependency selection.
These computational fixtures test the tooling walk, not a new semantic theorem. -/
namespace ReviewGraph

def leaf (n : Nat) : Nat := n + 1
def shared (n : Nat) : Nat := leaf n + leaf n
def left (n : Nat) : Nat := shared n
def right (n : Nat) : Nat := shared (n + 1)

open Lean Meta ProofGraph in
run_meta do
  let env ← getEnv
  let tree := treeModules env [env.mainModule]
  let atLeaf := fun n => n == ``leaf
  let atShared := fun n => n == ``shared
  let (first, warm) := (walkMemo env 100 tree true atLeaf ``left).run {}
  unless first.map (·.1) == some #[``leaf] do throwError "fixture did not reach leaf: {first}"
  for (name, stops) in [(``left, atLeaf), (``right, atLeaf), (``left, atShared), (``right, atShared)] do
    let cold := ((walkMemo env 100 tree true stops name).run {}).1
    let hot := ((walkMemo env 100 tree true stops name).run warm).1
    unless cold.isSome && hot == cold do throwError "warm/cold disagreement at {name}"
  let moved := ((walkMemo env 100 tree true atShared ``left).run warm).1
  unless moved.map (·.1) == some #[``shared] do throwError "cached stopping boundary"
  for state in [{}, warm] do
    unless ((walkMemo env 0 tree true atLeaf ``left).run state).1.isNone do
      throwError "exhausted walk accepted"
  logInfo "PASS: cold/warm caches, selected-node change, exhausted budget"

open Tools.Semantics

def cycleEdges : String → List String
  | "A" => ["B", "B"]
  | "B" => ["A"]
  | _ => []

#guard reachThrough cycleEdges 2 ["A", "A"] == (["A", "B"], [])
#guard reachThrough cycleEdges 1 ["A", "A"] == (["A"], ["B"])
#guard reachThrough cycleEdges 0 ["A", "A"] == ([], ["A"])

end ReviewGraph
