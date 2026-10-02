import Test.Audit.ProofGraphSearch
import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.RuleSets
import ProofGraph.Ledger
import ProofGraph.Search

namespace Test.ProofGraph
open Lean Meta Elab Command
open _root_.ProofGraph

theorem reflexive (n : Nat) : n = n := by aesop
theorem another (n : Nat) : n ≤ n := by aesop
def pending : ProofWanted (∀ n : Nat, n = n + 1) := ⟨⟩
def ordinary : Nat := 3

theorem declared : Obligation True := ⟨⟩

run_cmd liftTermElabM do
  let info ← getConstInfo ``declared
  let reference : ProofRef := ⟨``declared, info.levelParams, info.type⟩
  if let .error why ← reference.validate then throwError why

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

/-- info: Effect4.Laws.Auto.RuleSets: 0 of 0 theorems closed from their statements; 0 source lines they now take -/
#guard_msgs in
#auto_census Effect4.Laws.Auto.RuleSets using aesop


-- The shared reader retains the proposition's telescope, not the marker's type.
theorem polymorphicGoal.{u} (α : Sort u) (x : α) : Obligation (x = x) := ⟨⟩
theorem polymorphicWitness.{u} (α : Sort u) (x : α) : x = x := rfl
-- Deliberately malformed marker, matching the existing legacy-definition control.
set_option linter.defProp false in
def notATheorem : Obligation True := ⟨⟩
theorem nestedMarker : True ∧ Obligation True := ⟨True.intro, ⟨⟩⟩

#guard_msgs in
run_cmd liftTermElabM do
  let some goal ← readGoal ``polymorphicGoal | throwError "goal was not read"
  let info ← getConstInfo ``polymorphicWitness
  unless goal.id == ``polymorphicGoal && goal.levels == info.levelParams &&
      goal.dependencies.isEmpty && !goal.proposition.hasFVar && !goal.proposition.hasMVar do
    throwError "goal's identity, universes or closedness changed"
  unless ← isDefEq goal.proposition info.type do throwError "goal proposition changed"
  let report ← check #[goal] #[⟨goal.id, .proved ``polymorphicWitness⟩] 0
  unless report.proved == 1 do throwError "goal evidence did not validate"
  unless (← readGoal ``reflexive).isNone do throwError "ordinary theorem became a goal"
  unless (← readGoal ``ordinary).isNone do throwError "ordinary definition became a goal"

/-- error: obligation ledger: Test.ProofGraph.notATheorem must be declared as a theorem -/
#guard_msgs (error) in
run_cmd liftTermElabM do
  discard <| readGoal ``notATheorem

/-- error: obligation ledger: unsupported declaration shape at Test.ProofGraph.nestedMarker -/
#guard_msgs (error) in
run_cmd liftTermElabM do
  discard <| readGoal ``nestedMarker

-- The same ceiling admits its named axioms in both evidence paths.
#guard_msgs in
run_cmd liftTermElabM do
  unless disallowedAxioms #[``propext, ``Classical.choice, ``Quot.sound] == #[``Classical.choice] do
    throwError "semantic ceiling changed"
  let proposition := (← getConstInfo ``propext).type
  let reference ← addTheorem `Test.ProofGraph.allowedPropext [] proposition (mkConst ``propext)
  if let .error why ← reference.validate then throwError why

-- A placeholder cannot hide a forbidden axiom in its proposition, even in an unused let.
-- Keep this temporary declaration out of the module's exported constants.
/-- error: proof graph: placeholder Test.ProofGraph.forbiddenPlaceholder reaches [Classical.choice] -/
#guard_msgs (error) in
run_cmd liftTermElabM do
  withoutModifyingState do
    let proposition := mkLet `hidden (← inferType (mkConst ``Classical.em))
      (mkConst ``Classical.em) (mkConst ``True)
    addWanted `Test.ProofGraph.forbiddenPlaceholder [] proposition
    discard <| check #[{ id := `forbidden, proposition }]
      #[⟨`forbidden, .wanted `Test.ProofGraph.forbiddenPlaceholder⟩] 1

end Test.ProofGraph
