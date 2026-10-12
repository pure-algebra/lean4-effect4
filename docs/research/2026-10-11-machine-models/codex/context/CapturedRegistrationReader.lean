import Effect4.Laws.Program.Typed.Denotation
set_option autoImplicit false
namespace Test.CapturedRegistrationReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched Effect4.Program.Denote

/-!
Concept: residual-program-typing, R4 and R9; helper of the closed M5 source claim.
The reader consumes the real acquired continuation and the exact store operation it produces.
Its acquired value, captured map and issued argument policy are explicit producer premises.
It establishes neither a full body theorem nor whole-history preservation.
-/

example (program : NativeEff) (point : Point) (ctx : Ctx) (scope : Nat) (acquired : Val) :
    contAOf program (.acquired point ctx scope) acquired =
      Prim.onSuccess (Prim.sync (.op (.scopeAdd scope (.foreign (point.capture acquired ctx)))))
        (.afterScopeAdd acquired (.foreign (point.capture acquired ctx))) := by rfl

example (root : ProgramSource) (world : Typed.World) (point : Point)
    (acquire release : NativeEff) (env : List Ty) (type acquiredType : EffTy)
    (available : Env.Requirement) (ctx : Ctx) (scope : Nat) (acquired : Val)
    (node : Node.at_ (.eff root.program) point.path = some (.eff (.acquireRelease acquire release)))
    (checked : Checker.check (root.scopeSig point.path) env point.path
      (Eff.expandIn root.program (.acquireRelease acquire release)) = .ok type)
    (acquireChecked : Checker.check (root.scopeSig point.path) env (point.path ++ [0])
      (Eff.expandIn root.program acquire) = .ok acquiredType)
    (values : EnvTyped world env point.env) (answer : Fits world acquired acquiredType.answer)
    (requires : Row.Subset type.requires available) (covered : ctx.services.Satisfies available)
    (services : ServicesFit world ctx.services) (live : ScopeLive world scope)
    (arguments : AmbientStackTyped root world available
      (scopeParams root.program point.path) point.params) :
    AmbientProg root world available
      ((⟨.union .unit (.exitOf .unknown .unknown), .never, Env.Requirement.empty⟩ : EffTy),
        available, available)
      (storeR (.scopeAdd scope (.foreign (point.capture acquired ctx)))) := by
  have captureTyped : CaptureTyped root world (point.capture acquired ctx) :=
    ⟨acquire, release, env, type, acquiredType, node, checked, acquireChecked,
      envTyped_append values answer, services, ambientStackTyped_erases arguments⟩
  exact ambient_foreign_registration_typed root available scope _ live captureTyped
    (capturedReleasePolicy root world point acquire release env type acquiredType available ctx acquired
      node checked acquireChecked values answer requires covered arguments)
end Test.CapturedRegistrationReader
