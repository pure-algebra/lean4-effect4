import Effect4.Api.Author
import Effect4.Store.Domain.ProgramWire
import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Api.Codegen

/-!
# First-exit source readers

Placement: translation-simulation R10, serving the frozen first-exit timeout repair plan.
These controls read admission, the generated source codec, compilation, printing and reading.
They preserve a separate first-success source control.
They establish no machine selection, cleanup, host execution or target typing claim.
-/

set_option autoImplicit false

namespace Test.Program.FirstExitSource

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Store

/-- A source fixture with a declared failure and a successful second entrant. -/
def source : Src NativeOp := withFiber
  (Action.raceAllFirst [fail (str "first"), succeed (nat 2)])

/-- Its actual closed tree, through the existing source elaborator. -/
def tree : NativeEff := .withFiber (.raceAllFirst
  (.cons (.fail (.lit (.str "first"))) (.cons (.succeed (.lit (.nat 2))) .nil)))

#guard elaborate source = .ok tree
#guard Eff.scopedAt 0 tree = true
#guard Api.typeOf tree = some ⟨.nat, .string, .empty⟩

-- The existing first-success constructor and codec tag retain their values.
#guard Canonical.toVal (.raceAll (.nil : Effs NativeOp) : ActionTerm NativeOp) = .ctor 11 [Canonical.toVal (Effs.nil : Effs NativeOp)]
#guard Canonical.toVal (.raceAllFirst (.nil : Effs NativeOp) : ActionTerm NativeOp) = .ctor 17 [Canonical.toVal (Effs.nil : Effs NativeOp)]
#guard Canonical.decode (Canonical.encode tree) = some tree

/-- The actual source compilation point. -/
def point : Point := { path := [], env := [], fuel := 10, tape := [] }

#guard compileEff tree point = .withFiber (.act point)
#guard (actionAt tree point).map (fun | .raceAllFirst _ _ => true | _ => false) = some true
#guard (actionAt (.withFiber (.raceAll (.nil : Effs NativeOp))) point).map
  (fun | .raceAllFirst _ _ => true | _ => false) = some false
#guard Canonical.ofVal (α := ActionTerm NativeOp) (.ctor 17 []) = none

#guard ((Api.print tree).toOption.bind fun text => (Api.read text).toOption) = some tree

end Test.Program.FirstExitSource
