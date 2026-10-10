import Effect4.Api
import Effect4.Program.Fold
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Typed.Scope

/-!
Finite controls for parameterized layer identity at f00008ee.
Placement precedes this probe in PLAN.md. No general preservation claim is made.
-/
set_option autoImplicit false
namespace Test.CXLayerContextReview
open Effect4 Effect4.Program Effect4.Machine

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def u : Term := .lit .unit
def slot : ParamDecl := { name := "p", request := .unit, answer := .nat }
def decl (name : String) : DefDecl :=
  { name, request := .unit, answer := .nat, params := [slot] }
def arg (n : Nat) : Effs NativeOp := .cons (.succeed (.lit (.nat n))) .nil

def makeProgram (fresh : Bool) : NativeEff :=
  .defs [decl "outer", decl "inner"]
    (.cons
      (.provideLayer (.effect key (.perform (.param 0) u)) false
        (.invoke 1 u (arg 2)))
      (.cons
        (.provideLayer (if fresh then .fresh (.ref [0, 0, 0]) else .ref [0, 0, 0]) false
          (.service key))
        .nil))
    (.invoke 0 u (arg 1))

#guard Api.typeOf (makeProgram false) == some (EffTy.pure .nat)
#guard Api.typeOf (makeProgram true) == some (EffTy.pure .nat)
#guard (Api.run (makeProgram false) 500).exit == some (.success (.nat 1))
#guard (Api.run (makeProgram true) 500).exit == some (.success (.nat 2))

def unitEff : NativeEff := .succeed u
def errSlot (err : Ty) : ParamDecl :=
  { name := "p", request := .unit, answer := .unit, error := err }
def errDecl (name : String) (err : Ty) : DefDecl :=
  { name, request := .unit, answer := .unit, error := err, params := [errSlot err] }
def delayFail : Nat → NativeEff
  | 0 => .fail (.lit (.nat 7))
  | n + 1 => .bind (.yieldNow 0) (delayFail n)
def failureProgram (fresh : Bool) (yields : Nat) : NativeEff :=
  .defs [errDecl "outer" .nat, errDecl "inner" .never]
    (.cons
      (.provideLayer (.effectDiscard (.perform (.param 0) u)) false unitEff)
      (.cons
        (.provideLayer (if fresh then .fresh (.ref [0, 0, 0]) else .ref [0, 0, 0]) false
          unitEff)
        .nil))
    (.invoke 0 u (.cons
      (.bind (.withFiber (.fork (.invoke 1 u (.cons unitEff .nil)) ⟨true, true, .inherit⟩))
        (delayFail yields))
      .nil))

-- Execution admission succeeds, and the checked execution face reproduces the failure.
def admittedRun (p : NativeEff) (budget : Nat := 1000) : Option Api.Inspection :=
  match admitProgram p with
  | .ok admitted => some (Api.runAdmitted admitted budget)
  | .error _ => none

def childExit (r : Api.Inspection) : Option ExitV :=
  (r.machine.fiber? ⟨1⟩).bind RunFiber.exit

def errorExit : ExitV := .failure (Cause.fail (Err.tag 7))
def forkBody : NativeEff := .invoke 1 u (.cons unitEff .nil)
def forkNode : NativeEff := .withFiber (.fork forkBody ⟨true, true, .inherit⟩)
def forkPath : List Nat := [1, 0, 0, 0]
def appSig : Signature NativeOp :=
  ({} : SigApp).signature.withDefs (failureProgram false 2).defsOf

#guard Api.typeOf (failureProgram false 2) == some ⟨.unit, .nat, Env.Requirement.empty⟩
#guard Api.typeOf (failureProgram true 2) == some ⟨.unit, .nat, Env.Requirement.empty⟩
#guard (admitProgram (failureProgram false 2)).toOption.isSome
#guard (admitProgram (failureProgram true 2)).toOption.isSome
#guard (admittedRun (failureProgram false 2)).isSome
#guard (admittedRun (failureProgram false 2)).map Api.Inspection.exit == some (some errorExit)
#guard (admittedRun (failureProgram false 2)).map childExit == some (some errorExit)
#guard (admittedRun (failureProgram true 2)).map childExit == some (some (.success .unit))
#guard (admittedRun (failureProgram false 2)).map (·.outcome) == some .finished

-- The retained creation record identifies the child whose checked error column is never.
#guard Node.at_ (.eff (failureProgram false 2)) forkPath == some (.eff forkNode)
#guard Checker.check appSig [.unit] forkPath forkNode ==
  .ok (EffTy.pure (.fiberOf .unit .never))
#guard Checker.check appSig [.unit] (forkPath ++ [0, 0]) forkBody ==
  .ok (EffTy.pure .unit)
#guard (admittedRun (failureProgram false 2)).map (·.machine.forks) ==
  some [⟨⟨1⟩, ⟨0⟩, true, forkPath ++ [0]⟩]
#guard !(Val.hasTy (reifyExitVal errorExit) (.exitOf .unit .never))
#guard Val.hasTy (reifyExitVal errorExit) (.exitOf .unit .nat)

-- The identical layer has different inferred errors under the two parameter contexts.
def memoLayer : LayerTerm NativeOp := .effectDiscard (.perform (.param 0) u)
def checkedLayer (err : Ty) : Except TypeRefusal LayerTy :=
  Checker.checkLayer (appSig.withParams [errSlot err]) [0, 0, 0] memoLayer
#guard checkedLayer .nat == .ok ⟨Env.Requirement.empty, .nat, Env.Requirement.empty⟩
#guard checkedLayer .never == .ok ⟨Env.Requirement.empty, .never, Env.Requirement.empty⟩
#guard Checker.checkLayer (appSig.withParams [errSlot .nat]) [0, 0, 0]
    (.effectDiscard unitEff) ==
  Checker.checkLayer (appSig.withParams [errSlot .never]) [0, 0, 0] (.effectDiscard unitEff)

-- Exhaustion stays a live frontier, not the error used by the counterexample.
#guard (admittedRun (failureProgram false 2) 0).map (·.outcome) == some .frontier
#guard (admittedRun (failureProgram false 2) 0).map Api.Inspection.exit == some none

-- Copy of the inspected working predicate; production files remain pinned to f00008ee.
def ProposedLayerRefsScoped (root : NativeEff) : Prop :=
  ∀ site target : List Nat, Node.at_ (.eff root) site = some (.layer (.ref target)) →
    scopeParams root target = scopeParams root site

example : ¬ ProposedLayerRefsScoped (failureProgram false 2) := by
  intro h
  have heq := h [0, 1, 0, 0] [0, 0, 0] rfl
  have hne : scopeParams (failureProgram false 2) [0, 0, 0] ≠
      scopeParams (failureProgram false 2) [0, 1, 0, 0] := by decide
  exact hne heq

-- The same context restriction also excludes a harmless closed layer shared from the main.
def closedCrossScope : NativeEff :=
  .defs [errDecl "unused" .never]
    (.cons (.provideLayer (.effectDiscard unitEff) false unitEff) .nil)
    (.provideLayer (.ref [0, 0, 0]) false unitEff)

#guard (admitProgram closedCrossScope).toOption.isSome
#guard Api.typeOf closedCrossScope == some (EffTy.pure .unit)
#guard (admittedRun closedCrossScope).map Api.Inspection.exit == some (some (.success .unit))

example : ¬ ProposedLayerRefsScoped closedCrossScope := by
  intro h
  have heq := h [1, 0] [0, 0, 0] rfl
  have hne : scopeParams closedCrossScope [0, 0, 0] ≠ scopeParams closedCrossScope [1, 0] := by decide
  exact hne heq

-- A generated traversal supplies the proposed repair's parameter-use inventory.
-- Expand references first; a raw reference contains no parameter node.
def usedParams (l : LayerTerm NativeOp) : List Nat :=
  foldMap_layer [] List.append l (f_eff := fun e =>
    match e with
    | .perform (.param i) _ => [i]
    | _ => [])

def argumentLayer : LayerTerm NativeOp :=
  .effectDiscard (.invoke 0 u (.cons (.perform (.param 1) u) .nil))

#guard usedParams memoLayer == [0]
#guard usedParams (.effectDiscard unitEff) == []
#guard usedParams argumentLayer == [1]
#guard usedParams (.ref [0, 0, 0]) == []
#guard usedParams (LayerTerm.expandIn (failureProgram false 2) (.ref [0, 0, 0])) == [0]
#guard usedParams (LayerTerm.expandIn closedCrossScope (.ref [0, 0, 0])) == []

end Test.CXLayerContextReview
