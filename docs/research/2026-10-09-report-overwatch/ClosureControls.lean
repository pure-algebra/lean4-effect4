import ProofGraph.ClosureAudit

/-! Finite controls for the runtime-definition population of the closure audit.
The consumer is the new authoring policy in AGENTS; no program or semantic claim changes. -/
namespace ReviewClosure

-- These three bodies have identical executable work.
def rebuilt (n : Nat) : Nat → Bool :=
  let table := List.range n
  fun k => table.contains k

def instSizeOfRebuilt (n : Nat) : Nat → Bool :=
  let table := List.range n
  fun k => table.contains k

private def privateRebuilt (n : Nat) : Nat → Bool :=
  let table := List.range n
  fun k => table.contains k

-- This binding has no runtime value to rebuild.
def proofOnly (n : Nat) : Nat → Nat :=
  let h : n = n := rfl
  fun k => Eq.mp (congrArg (fun _ : Nat => Nat) h) k

def asData (table : List Nat) (k : Nat) : Bool := table.contains k

#guard rebuilt 5 3
#guard instSizeOfRebuilt 5 3
#guard privateRebuilt 5 3
#guard proofOnly 5 3 == 3
#guard asData (List.range 5) 3

open Lean Meta in
run_meta do
  let env ← getEnv
  for name in [``rebuilt, ``instSizeOfRebuilt, ``privateRebuilt, ``proofOnly, ``asData] do
    let some (.defnInfo d) := env.find? name | throwError "missing fixture {name}"
    let lets := ProofGraph.letsBeforeClosure d.value
    logInfo m!"fixture {name}: lets={lets.toList}, excluded={ProofGraph.isAuxiliary env name}"
  let some (.defnInfo proof) := env.find? ``proofOnly | throwError "missing proof fixture"
  let .lam _ _ (.letE _ type _ _ _) _ := proof.value | throwError "proof let shape changed"
  -- Instantiate the ordinary argument before asking the same erasure question as ToLCNF.
  let proofType := type.instantiate1 (mkNatLit 5)
  unless ← isProp proofType do throwError "the retained let is not a proposition"

end ReviewClosure

-- The actual public audit command runs on this module's authored definitions.
/--
error: #closure_audit: 2 definitions bind a table before the closure they return; pass the table as data:
  ReviewClosure.proofOnly binds [h] before the closure it returns
  ReviewClosure.rebuilt binds [table] before the closure it returns
-/
#guard_msgs in
#closure_audit ClosureControls
