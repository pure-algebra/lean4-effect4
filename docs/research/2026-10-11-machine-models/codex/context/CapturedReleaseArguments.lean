import Effect4.Laws.Program.Typed.Denotation
/-!
Concept: residual-program-typing, R4 and R9; helper of typed-state-reachable.
The reader transports actual acquisition checker evidence into the captured release child.
It consumes the issued argument policy, actual captured map and acquired value membership.
Its consumer is the ambient release-body producer, not a whole-history theorem.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

example (root : ProgramSource) (world : World) (point : Point)
    (acquire release : NativeEff) (env : List Ty) (type acquiredType : EffTy)
    (available : Env.Requirement) (ctx : Ctx) (acquired : Val)
    (node : Node.at_ (.eff root.program) point.path = some (.eff (.acquireRelease acquire release)))
    (checked : Checker.check (root.scopeSig point.path) env point.path
      (Eff.expandIn root.program (.acquireRelease acquire release)) = .ok type)
    (acquireChecked : Checker.check (root.scopeSig point.path) env (point.path ++ [0])
      (Eff.expandIn root.program acquire) = .ok acquiredType)
    (values : EnvTyped world env point.env) (answer : Fits world acquired acquiredType.answer)
    (requires : Row.Subset type.requires available) (covered : ctx.services.Satisfies available)
    (arguments : AmbientStackTyped root world available
      (scopeParams root.program point.path) point.params) :
    ∀ future, world.leHost future → ∀ completed,
      (∀ entry ∈ completed, ∃ declared, future.Γ entry.1 = some declared ∧ ExitOk future declared entry.2) →
      ∀ exitValue, Fits future exitValue (.exitOf .unknown .unknown) →
        ∃ releaseType,
          AmbientPointTyped root future ctx.services.keysRow
            ((Point.ofCapture (point.capture acquired ctx) completed).childWith 1 exitValue) releaseType ∧
          releaseType.error.normalize = .never ∧
          Row.Subset releaseType.requires ctx.services.keysRow :=
  capturedReleasePolicy root world point acquire release env type acquiredType available ctx acquired
    node checked acquireChecked values answer requires covered arguments
end Effect4.Program.Typed
