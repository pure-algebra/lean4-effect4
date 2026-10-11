import Effect4.Laws.Program.Typed.Admission
import Effect4.Api

/-!
Finite controls for CX1 at 71799e47.
Placement: residual-program-typing; helpers of denote-typed (R4).
Consumer: lexical point admission and layerPointTyped_redirect before invoke_arm/param_arm.
Reach: finite admitted roots, addressed layer references, and the proposed stack predicate.
Limits: these controls prove no general preservation, progress, or host correspondence.
Unlock: choose a closure invariant compatible with existing layer sharing before CX1.
-/
set_option autoImplicit false
namespace Test.CXLexicalReview
open Effect4 Effect4.Program Effect4.Machine Effect4.Program.Typed

def lexical (sig : Signature NativeOp) (ps : List ParamDecl) : Signature NativeOp :=
  { sig with
    rowOf := fun op => match sig.paramOf op with
      | some i => match ps[i]? with
        | some d => d.row.normalizeTypes
        | none => sig.rowOf op
      | none => sig.rowOf op
    dom := fun op => match sig.paramOf op with
      | some i => decide (i < ps.length)
      | none => sig.dom op }

def bodyParams : List DefDecl → List Nat → List ParamDecl
  | d :: _, 0 :: _ => d.params
  | _ :: ds, 1 :: rest => bodyParams ds rest
  | _, _ => []

def scopeParams (root : NativeEff) (path : List Nat) : List ParamDecl :=
  match root, path with
  | .defs ds _ _, 0 :: rest => bodyParams ds rest
  | _, _ => []

def scopeSig (src : ProgramSource) (path : List Nat) : Signature NativeOp :=
  lexical src.signature (scopeParams src.program path)

/-- The note's stack predicate, with normalized requests and expanded site programs. -/
def StackTyped (src : ProgramSource) (w : Effect4.Program.Typed.World)
    (ps : List ParamDecl) : List (List ArgSite) → Prop
  | [] => ps = []
  | sites :: rest => ∀ (i : Nat) (d : ParamDecl), ps[i]? = some d →
      ∃ (site : ArgSite) (arg : NativeEff) (env : List Ty) (ty : EffTy), sites[i]? = some site ∧
        Node.at_ (.eff src.program) site.path = some (.eff arg) ∧
        Checker.check (scopeSig src site.path) (env ++ [d.request.normalize]) site.path
          (Eff.expandIn src.program arg) = .ok ty ∧
        d.admits ty = true ∧ EnvTyped w env site.env ∧
        StackTyped src w (scopeParams src.program site.path) rest

def q : ParamDecl := { name := "q", request := .unit, answer := .unit }
def d : DefDecl := { name := "d", request := .unit, answer := .unit, params := [q] }
def u : NativeEff := .succeed (.lit .unit)
def sharedLayer : LayerTerm NativeOp := .effectDiscard u

def crossRoot : NativeEff := .defs [d]
  (.cons (.provideLayer sharedLayer false u) .nil)
  (.provideLayer (.ref [0, 0, 0]) false u)
def crossSource : ProgramSource := { program := crossRoot }
def caller : Point := { path := [1, 0], env := [], fuel := 20, tape := [] }

-- The current language admits this reference between different parameter scopes.
#guard crossRoot.layerRefsWF
#guard Api.typeOf crossRoot == some (EffTy.pure .unit)
#guard Node.at_ (.eff crossRoot) caller.path == some (.layer (.ref [0, 0, 0]))
#guard Node.at_ (.eff crossRoot) [0, 0, 0] == some (.layer sharedLayer)
#guard scopeParams crossRoot caller.path == []
#guard scopeParams crossRoot [0, 0, 0] == [q]
#guard (caller.redirect [0, 0, 0]).params == caller.params
#guard (Api.run crossRoot 200).exit == some (.success .unit)

-- The proposed invariant admits the caller's empty scope but cannot admit its target.
example (w : Effect4.Program.Typed.World) :
    StackTyped crossSource w (scopeParams crossRoot caller.path) caller.params := rfl
example (w : Effect4.Program.Typed.World) :
    ¬ StackTyped crossSource w (scopeParams crossRoot [0, 0, 0])
      (caller.redirect [0, 0, 0]).params := by
  intro h
  cases h

-- Arguments are checked after expansion. Raw reference syntax is refused.
def referenceArg : NativeEff := .provideLayer (.ref [0, 0, 0]) false u
def referenceArgRoot : NativeEff := .defs [d]
  (.cons (.provideLayer sharedLayer false u) .nil)
  (.invoke 0 (.lit .unit) (.cons referenceArg .nil))
def referenceSource : ProgramSource := { program := referenceArgRoot }
#guard Api.typeOf referenceArgRoot == some (EffTy.pure .unit)
#guard (Checker.check referenceSource.signature [.unit] [1, 0, 0] referenceArg).toOption == none
#guard (Checker.check referenceSource.signature [.unit] [1, 0, 0]
  (Eff.expandIn referenceArgRoot referenceArg)).toOption == some (EffTy.pure .unit)

-- A reference inside an argument can stay wholly within the main program's scope.
def localReferenceArg : NativeEff := .bind (.provideLayer sharedLayer false u)
  (.provideLayer (.ref [1, 0, 0, 0, 0]) false u)
def localReferenceRoot : NativeEff := .defs [d] (.cons u .nil)
  (.invoke 0 (.lit .unit) (.cons localReferenceArg .nil))
def localReferenceSource : ProgramSource := { program := localReferenceRoot }
#guard Api.typeOf localReferenceRoot == some (EffTy.pure .unit)
#guard scopeParams localReferenceRoot [1, 0, 0, 0, 0] == []
#guard scopeParams localReferenceRoot [1, 0, 0, 1, 0] == []
#guard (Checker.check localReferenceSource.signature [.unit] [1, 0, 0]
  localReferenceArg).toOption == none
#guard (Checker.check localReferenceSource.signature [.unit] [1, 0, 0]
  (Eff.expandIn localReferenceRoot localReferenceArg)).toOption == some (EffTy.pure .unit)

-- Requests may be closed without being in normal form.
def unionParam : ParamDecl := { name := "n", request := .union .nat .never, answer := .nat }
#guard unionParam.formed
#guard unionParam.request.normalize == Ty.nat
#guard (Checker.check (nativeSignature []) [unionParam.request] [] (.succeed (.var 0))).toOption == some (EffTy.pure unionParam.request)
#guard (Checker.check (nativeSignature []) [unionParam.request.normalize] [] (.succeed (.var 0))).toOption == some (EffTy.pure .nat)

-- A declaration is insufficient evidence that its body respects the declared row.
def natParam : ParamDecl := { name := "n", request := .unit, answer := .nat }
def badDecl : DefDecl := { name := "bad", request := .unit, answer := .nat }
def useDecl : DefDecl :=
  { name := "use", request := .unit, answer := .nat, params := [natParam] }
def useBody : NativeEff := .perform (.param 0) (.lit .unit)
def passedCall : NativeEff := .perform (.call 0) (.lit .unit)
def badRoot : NativeEff := .defs [badDecl, useDecl]
  (.cons (.succeed (.lit (.bool true))) (.cons useBody .nil))
  (.invoke 1 (.lit .unit) (.cons passedCall .nil))
def badSource : ProgramSource := { program := badRoot }
#guard (Checker.check (lexical badSource.signature [natParam]) [.unit]
  [0, 1, 0] useBody).toOption == some (EffTy.pure .nat)
#guard (Checker.check badSource.signature [.unit]
  [1, 0, 0] passedCall).toOption == some (EffTy.pure .nat)
#guard natParam.admits (EffTy.pure .nat)
#guard Api.typeOf badRoot == none
#guard (Api.run badRoot 200).exit == some (.success (.bool true))

/-- The candidate repair witnesses each site's active context in the proof. -/
def ActiveStackTyped (src : ProgramSource) (w : Effect4.Program.Typed.World)
    (ps : List ParamDecl) : List (List ArgSite) → Prop
  | [] => ps.all ParamDecl.formed = true ∧ ps = []
  | sites :: rest => ps.all ParamDecl.formed = true ∧
      ∀ (i : Nat) (d : ParamDecl), ps[i]? = some d →
        ∃ (site : ArgSite) (arg : NativeEff) (env : List Ty)
          (callerPs : List ParamDecl) (ty : EffTy),
          sites[i]? = some site ∧
          Node.at_ (.eff src.program) site.path = some (.eff arg) ∧
          Checker.check (src.signature.withParams callerPs) (env ++ [d.request.normalize])
            site.path (Eff.expandIn src.program arg) = .ok ty ∧
          d.admits ty = true ∧ EnvTyped w env site.env ∧
          ActiveStackTyped src w callerPs rest

-- The same empty active context works on both sides of the admitted reference.
example (w : Effect4.Program.Typed.World) : ActiveStackTyped crossSource w [] caller.params :=
  ⟨rfl, rfl⟩
example (w : Effect4.Program.Typed.World) :
    ActiveStackTyped crossSource w [] (caller.redirect [0, 0, 0]).params := ⟨rfl, rfl⟩
#guard Checker.checkLayer (lexical crossSource.signature []) caller.path
  (LayerTerm.expandIn crossRoot (.ref [0, 0, 0])) ==
    Checker.checkLayer (lexical crossSource.signature []) [0, 0, 0]
      (LayerTerm.expandIn crossRoot sharedLayer)

-- One code body can check under distinct active parameter declarations.
def boolParam : ParamDecl := { name := "b", request := .unit, answer := .bool }
#guard (Checker.check (lexical crossSource.signature [natParam]) [] [] useBody).toOption ==
  some (EffTy.pure .nat)
#guard (Checker.check (lexical crossSource.signature [boolParam]) [] [] useBody).toOption ==
  some (EffTy.pure .bool)

-- Inactive frames are allowed in a context with no parameter operation.
example (src : ProgramSource) (w : Effect4.Program.Typed.World) (sites : List ArgSite)
    (rest : List (List ArgSite)) : ActiveStackTyped src w [] (sites :: rest) := by
  refine ⟨rfl, ?_⟩
  intro i d h
  cases h

-- The new generic withParams_param goal needs an outer-domain premise.
def alreadyParamSig : Signature NativeOp := (nativeSignature []).withParams [q]
#guard (alreadyParamSig.withParams []).dom (.param 0)
#guard (([] : List ParamDecl)[0]?).isNone

/-- Finite instantiation refuting the unqualified statement in the live Scope draft. -/
example : ¬ (∀ (sig : Signature NativeOp) (ps : List ParamDecl) (op : NativeOp) (i : Nat),
    sig.paramOf op = some i → (sig.withParams ps).dom op = true →
    ∃ slot, ps[i]? = some slot ∧ (sig.withParams ps).rowOf op = slot.row.normalizeTypes) := by
  intro h
  obtain ⟨slot, hslot, _⟩ := h alreadyParamSig [] (.param 0) 0 rfl (by decide)
  cases hslot

end Test.CXLexicalReview
