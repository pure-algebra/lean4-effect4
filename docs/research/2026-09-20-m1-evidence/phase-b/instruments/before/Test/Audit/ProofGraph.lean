import ProofGraph.Ledger
import ProofGraph.Search

namespace Test.ProofGraph
open Lean Meta Elab Command
open _root_.ProofGraph

theorem reflexive (n : Nat) : n = n := rfl
theorem another (n : Nat) : n ≤ n := Nat.le_refl n
def pending : ProofWanted (∀ n : Nat, n = n + 1) := ⟨⟩
def ordinary : Nat := 3

run_cmd liftTermElabM do
  let goal : Goal := {id := `closed, proposition := (← getConstInfo ``reflexive).type}
  let waiting : Goal := {id := `open, proposition := (← getConstInfo ``pending).type.appArg!}
  let result ← check #[goal, waiting] #[⟨`closed, .proved ``reflexive⟩, ⟨`open, .wanted ``pending⟩] 1
  unless result.proved == 1 && result.wanted == 1 do throwError "incorrect ledger counts"

/-- error: proof graph: missing evidence or placeholder for closed -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[{id := `closed, proposition := (← getConstInfo ``reflexive).type}] #[] 0

/-- error: proof graph: stale entry gone -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[] #[⟨`gone, .wanted ``pending⟩] 1

/-- error: proof graph: 1 open obligations exceed ceiling 0 -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[{id := `open, proposition := (← getConstInfo ``pending).type.appArg!}]
    #[⟨`open, .wanted ``pending⟩] 0

/-- error: proof graph: Test.ProofGraph.another: proposition changed -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[{id := `closed, proposition := (← getConstInfo ``reflexive).type}]
    #[⟨`closed, .proved ``another⟩] 0

/-- error: proof graph: Test.ProofGraph.ordinary: missing or not a theorem -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[{id := `closed, proposition := (← getConstInfo ``reflexive).type}]
    #[⟨`closed, .proved ``ordinary⟩] 0

/-- error: proof graph: placeholder proposition changed for closed -/
#guard_msgs in
run_cmd liftTermElabM do
  discard <| check #[{id := `closed, proposition := (← getConstInfo ``reflexive).type}]
    #[⟨`closed, .wanted ``pending⟩] 1

/-- error: proof graph: dependency cycle through [one, two] -/
#guard_msgs in
run_cmd liftTermElabM do
  let ty := (← getConstInfo ``reflexive).type
  discard <| check #[⟨`one, [], ty, #[`two]⟩, ⟨`two, [], ty, #[`one]⟩]
    #[⟨`one, .proved ``reflexive⟩, ⟨`two, .proved ``reflexive⟩] 0

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

#print axioms Test.ProofGraph.searched
end Test.ProofGraph
