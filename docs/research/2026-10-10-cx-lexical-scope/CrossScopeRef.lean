import Effect4.Api
import Effect4.Laws.Program.Typed.Scope

/-!
Finite probe for the CX note's §10: the checker admits a program whose main program names, by a
layer reference, a layer that a definition's body holds. The two paths have different scopes
(`scopeParams`), so the reference's hop is the case of the goal `crossScopeRef_builds`.
-/

open Effect4 Effect4.Program Effect4.Machine
open Effect4.Machine.Env (Requirement)

/-- The native service key `⟨4, 4⟩`, whose carrier is `nat` (`nativeServiceTy`). -/
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def unitE : NativeEff := .succeed (.lit .unit)

/-- `f : unit ⇒ unit`. -/
def fParam : ParamDecl := { name := "f", request := .unit, answer := .unit }

/-- `d : unit → unit`, with the parameter `f`. -/
def dDecl : DefDecl := { name := "d", request := .unit, answer := .unit, params := [fParam] }

/-- The layer the body provides: `key` bound to `7`. It runs no parameter. -/
def leaf : LayerTerm NativeOp := .effect key (.succeed (.lit (.nat 7)))

/-- `d`'s body: the leaf provided over a run of `f`. The leaf stands at `[0, 0, 0]`. -/
def dBody : NativeEff := .provideLayer leaf false (.perform (.param 0) (.lit .unit))

/-- The main program names the body's leaf by reference, from the main program's scope. -/
def mainProg : NativeEff := .provideLayer (.ref [0, 0, 0]) false unitE

def prog : NativeEff := .defs [dDecl] (.cons dBody .nil) mainProg

-- the reference is well formed: the target precedes it, and is a layer that is no reference
#guard prog.layerRefsWF
-- the checker admits the program
#guard Api.typeOf prog == some (EffTy.pure .unit)
-- the reference stands in the main program's scope, its target in `d`'s
#guard scopeParams prog [1, 0] == []
#guard scopeParams prog [0, 0, 0] == [fParam]
