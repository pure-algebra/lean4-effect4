import Test.Audit.ProofGraphSearch
import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.RuleSets
import ProofGraph.Search

namespace Test.ProofGraph
open Lean Meta Elab Command
open _root_.ProofGraph

theorem reflexive (n : Nat) : n = n := by aesop
theorem another (n : Nat) : n ≤ n := by aesop
def ordinary : Nat := 3

run_cmd liftTermElabM do
  let info ← getConstInfo ``Classical.em
  let reference : ProofRef := ⟨``Classical.em, info.levelParams, info.type⟩
  if (← reference.validate).isOk then throwError "extra axioms accepted"
  let proposition ← Term.elabType (← `(∀ n : Nat, n = 0 → n = n))
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let .ok proof ← search proposition (← `(tactic| intros; exact Eq.refl _)) 20000
    | throwError "a weaker reflexivity witness was not found"
  discard <| addTheorem `Test.ProofGraph.searched [] proposition proof
  let reference : ProofRef := ⟨`Test.ProofGraph.searched, [], proposition⟩
  if let .error why ← reference.validate then throwError why

/-- info: 'Test.ProofGraph.searched' does not depend on any axioms -/
#guard_msgs in
#print axioms Test.ProofGraph.searched

/-- info: Effect4.Laws.Auto.RuleSets: 0 of 0 theorems closed from their statements; 0 source lines they now take -/
#guard_msgs in
#auto_census Effect4.Laws.Auto.RuleSets using aesop


-- The ceiling admits its named axioms.
#guard_msgs in
run_cmd liftTermElabM do
  unless disallowedAxioms #[``propext, ``Classical.choice, ``Quot.sound] == #[``Classical.choice] do
    throwError "semantic ceiling changed"
  let proposition := (← getConstInfo ``propext).type
  let reference ← addTheorem `Test.ProofGraph.allowedPropext [] proposition (mkConst ``propext)
  if let .error why ← reference.validate then throwError why

/-! ## The memoized walk across a cycle

An inductive type names its constructors and each constructor names its type, so the walk meets
cycles. `quiet` closes inside the open component of `MemoCycle`, before `loud` reaches the leaf.
The memo must still store what `quiet` reaches, as Lean's collector reads it: the leaf, through
`MemoCycle` and `loud` (`tools/ProofGraph/Axioms.lean`, section Cycles). -/

/-- A leaf of the walk, selected by `stop`, as a planned goal is. -/
def memoLeaf : Nat := 0

inductive MemoCycle where
  | quiet : MemoCycle
  | loud : Fin (memoLeaf + 1) → MemoCycle

def memoEntry : Type := MemoCycle

-- control: entered from `memoEntry`, the component stores `quiet`'s full answer
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let (outs, _) := reachedAxiomsMany env #[``memoEntry, ``MemoCycle.quiet] {} (· == ``memoLeaf)
  unless outs[1]! == some #[``memoLeaf] do throwError "a component member was stored short"

end Test.ProofGraph
