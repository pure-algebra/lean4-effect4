import Effect4.Api.Codegen

/-! Closed counted-layer instance: one actual reference site versus two nested
reference sites, with the same table and ordinary run tape. The two programs and their
well-formedness live here, where the authoring contracts read them; the kernel-checked run
certificate over them is in the slow lane (`Test/Program/LayerSharingCertificate.lean`,
`Test/Slow.lean`). -/
set_option autoImplicit false

namespace Test.Program.LayerSharingContract
open Effect4 Effect4.Machine Effect4.Program
def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩
def layerCount : LayerTerm NativeOp :=
  .effect kA (.bind (.service kRef)
    (.bind (.perform (.refUpdateWith (FnName.image .update 1 .incr)) (.var 0)) (.succeed (.lit (.nat 5)))))
def refTarget : List Nat := [1, 0, 0, 0]
def once : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false (.service kA)))
        (.perform .refGet (.var 0))))
def twice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer layerCount false
        (.provideLayer (.ref refTarget) false
          (.provideLayer (.ref refTarget) false (.service kA))))
        (.perform .refGet (.var 0))))

#guard once.layerRefsWF
#guard twice.layerRefsWF
#guard Api.wellTyped once
#guard Api.wellTyped twice

/-! ## A body's layer, once per call (decisions row 341, step 3)

`withL : number → number`, with `f : number ⇒ number`, provides the counted layer in its body and
again by a reference, then runs `f`. A build is keyed by the layer's path and the running call
(`Point.layerKey`, `src/Effect4/Program/Compile.lean`): one call builds once, and a call nested
in another, through the program that the outer one passed, builds again, as rc.112 builds one
layer object per evaluation of the body. -/

/-- `f : number ⇒ number`. -/
def fParam : ParamDecl := { name := "f", request := .nat, answer := .nat }

/-- `withL`, which reads the counter's service in its layer's build. -/
def withLDecl : DefDecl :=
  { name := "withL", request := .nat, answer := .nat, requires := [kRef], params := [fParam] }

/-- The body of `withL`, at `[0, 0]`: its layer at `[0, 0, 0]`, provided twice. -/
def withLBody : NativeEff :=
  .provideLayer layerCount false
    (.provideLayer (.ref [0, 0, 0]) false (.bind (.service kA) (.perform (.param 0) (.var 0))))

/-- The counter made, `call` under it, then the count read. -/
def counted (call : NativeEff) : Api.Program :=
  .defs [withLDecl] (.cons withLBody .nil)
    (.bind (.perform .refMake (.lit (.nat 0)))
      (.provideService kRef (.var 0) (.bind call (.perform .refGet (.var 0)))))
    .nil

/-- `withL(1, (a) => succeed(3))`. -/
def oneCall : Api.Program :=
  counted (.invoke 0 (.lit (.nat 1)) (.cons (.succeed (.lit (.nat 3))) .nil))

/-- `withL(1, (a) => withL(2, (b) => succeed(3)))`. -/
def nestedCall : Api.Program :=
  counted (.invoke 0 (.lit (.nat 1))
    (.cons (.invoke 0 (.lit (.nat 2)) (.cons (.succeed (.lit (.nat 3))) .nil)) .nil))

/-- The value of a successful exit. -/
def successVal : Option ExitV → Option Val
  | some (.success v) => some v
  | _ => none

#guard oneCall.layerRefsWF
#guard nestedCall.layerRefsWF
#guard Api.wellTyped oneCall
#guard Api.wellTyped nestedCall
-- tested: one call provides its layer twice and builds it once
#guard successVal (Api.run oneCall 800).exit == some (.nat 1)
-- tested: a call nested in another builds its own: two builds, where a key by path alone
-- would hand the inner call the outer call's build
#guard successVal (Api.run nestedCall 1600).exit == some (.nat 2)
-- control: the nested call's callback needs the counter's service, which the printed parameter
-- type cannot carry, so the printer refuses it at the callback (`passedRequirementFault`,
-- src/Effect4/Codegen/CallbackRequirements.lean; seat 3B's finding: tsgo refused it, TS2375)
#guard (match Api.emitModule "main" nestedCall [] with
  | .error (.print (.callbackRequirement path)) => path == [1, 1, 0, 0, 0, 0]
  | _ => false)
-- reader: the single call's callback needs nothing, and the module prints
#guard (match Api.emitModule "main" oneCall [] with
  | .ok _ => true
  | .error _ => false)
end Test.Program.LayerSharingContract
