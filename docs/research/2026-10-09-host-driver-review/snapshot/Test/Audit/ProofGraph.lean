import Test.Audit.ProofGraphSearch
import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.RuleSets
import ProofGraph.Search
import ProofGraph.AxiomAudit

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

/-! ## An axiom's type

Lean's collector reads an axiom's type, so an axiom whose type names another axiom reaches both.
The control adds two axioms to a local copy of the environment, `A : Type` and `a : A`, and
compares the walk with `Lean.collectAxioms` there; nothing enters this file's environment. Found
by Codex's review of the cycle repair (2026-10-09): the walk read no dependency of an axiom. -/

-- control: the walk reaches the axiom in an axiom's type, as Lean's collector does
#guard_msgs in
run_cmd do
  let base ← getEnv
  let addAxiom (env : Environment) (n : Name) (ty : Expr) : CommandElabM Environment :=
    let decl : AxiomVal := { name := n, levelParams := [], type := ty, isUnsafe := false }
    match env.addDeclCore 0 1000 (.axiomDecl decl) none with
    | .ok env => pure env
    | .error _ => throwError "the local axiom {n} was refused"
  let env ← addAxiom base `AxiomTypeControl.A (mkSort (.succ .zero))
  let env ← addAxiom env `AxiomTypeControl.a (mkConst `AxiomTypeControl.A)
  let some got := exactAxioms env `AxiomTypeControl.a | throwError "the walk ran out of budget"
  let expected ← withEnv env <| Lean.collectAxioms `AxiomTypeControl.a
  unless got.qsort Name.lt == expected do throwError "an axiom's type: {got} versus {expected}"
  unless ((← getEnv).find? `AxiomTypeControl.A).isNone do throwError "a local axiom escaped"

/-! ## `#axiom_audit`

The seat's audit of named modules applies no admission: the walk module's own metaprograms reach
`Classical.choice`, which the gate admits for that module, and the command names each of them. -/

/--
error: #axiom_audit: 5 of 43 declarations reach axioms outside [propext, Quot.sound]:
  ProofGraph.reachedAxioms reaches [Classical.choice]
  ProofGraph.exactAxioms reaches [Classical.choice]
  ProofGraph.reachedAxiomsMany reaches [Classical.choice]
  _private.ProofGraph.Axioms.0.ProofGraph.deps reaches [Classical.choice]
  _private.ProofGraph.Axioms.0.ProofGraph.selfAxiom reaches [Classical.choice]
-/
#guard_msgs in
#axiom_audit ProofGraph.Axioms

end Test.ProofGraph
