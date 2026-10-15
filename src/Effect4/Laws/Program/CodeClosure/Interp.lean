import Effect4.Laws.Program.CodeClosure.Qualified.Interp
import Effect4.Laws.Program.CodeClosure.Callbacks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native callback frames retain their supplied source annotations.
Consumer: the shared stable saved family and Timeout's pending source assertion.
Reach: actual completed-exit views within the existing direct source fragment.
Limit: initialization, numeric effects, and command histories remain separate obligations.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

abbrev IterAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.IterAt point env (Qualified.EnvironmentWrites env)

abbrev closeSeq_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.closeSeq_at point env (Qualified.EnvironmentWrites env)

abbrev store_iter_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.store_iter_at point env (Qualified.EnvironmentWrites env)

abbrev interp_iter_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_iter_at root point env (Qualified.EnvironmentWrites env)

abbrev interp_loopEnter_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_loopEnter_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev interp_loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_loopResume_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev interp_cancel_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_cancel_at root point env (Qualified.EnvironmentWrites env)

abbrev interp_fin_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_fin_at root fragment point env (Qualified.EnvironmentWrites env)

end Effect4.Program.CodeClosure.Slots
