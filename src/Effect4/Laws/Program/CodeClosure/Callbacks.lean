import Effect4.Laws.Program.CodeClosure.Qualified.Callbacks
import Effect4.Laws.Program.CodeClosure.Stored
import Effect4.Laws.Program.CodeClosure.Compile
import Effect4.Laws.Program.NativeScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: callbacks retain supplied source-point and captured-environment assertions.
Consumer: the Prefix callback instance and Timeout's actual attempt-source refinement.
Reach: the existing direct source fragment and the existing native callback definitions.
Limit: this contract supplies neither initialization nor an actual command history.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

abbrev Transport (point : Point → Prop) (env : List Val → Prop) := @Qualified.Transport point env

theorem operation_at (point : Point → Prop) (env : List Val → Prop) (bindings : List Val)
    (row : NativeOp) (value : Val) (operation : SyncOp)
    (held : env bindings) (answer : row.syncOpOf bindings value = some operation) : OpAt point env operation := by
  fun_cases NativeOp.syncOpOf row bindings value
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NativeOp.syncOpOf, OpAt, Qualified.OpAt, Qualified.EnvironmentWrites])


abbrev asyncRoute_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.asyncRoute_at point env (Qualified.EnvironmentWrites env)

theorem compile_contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (transport : Transport point env) :
    CodeClosure.CompileContract root point (NameAt point env) (ThunkAt point env)  :=
  Qualified.compile_contract root point env (Qualified.EnvironmentWrites env) transport
    (fun p row _ value op _ held _ selected =>
      operation_at point env p.env row value op (transport.environment held) selected)

abbrev Contract (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.Contract root point env (Qualified.EnvironmentWrites env)

theorem Contract.of_transport (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (transport : Transport point env) : Contract root point env where
  compilation := compile_contract root point env transport
  child := transport.child
  childWith := transport.childWith
  capture := transport.capture


abbrev compile_at (root : NativeEff) (_fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.compile_at root _fragment point env (Qualified.EnvironmentWrites env)

abbrev badShape_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.badShape_at point env (Qualified.EnvironmentWrites env)

abbrev resolve_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.resolve_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev resolve_child_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.resolve_child_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev resolve_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.resolve_arg_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev region_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.region_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev capture_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.capture_at root point env (Qualified.EnvironmentWrites env)

abbrev childBind (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.childBind root point env (Qualified.EnvironmentWrites env)

abbrev contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.contA_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.contE_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev loopFinish_at (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.loopFinish_at root point env (Qualified.EnvironmentWrites env)

abbrev select_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.select_arg_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev LoopAt (point : Point → Prop) (env : List Val → Prop) := @Qualified.LoopAt point env (Qualified.EnvironmentWrites env)

abbrev loopNext_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.loopNext_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.loopResume_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.suspend_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev cancel_at (point : Point → Prop) (env : List Val → Prop) := @Qualified.cancel_at point env (Qualified.EnvironmentWrites env)

abbrev ViewStable := @Qualified.ViewStable

abbrev interp_contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_contA_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev interp_contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_contE_at root fragment point env (Qualified.EnvironmentWrites env)

abbrev interp_suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.interp_suspend_at root fragment point env (Qualified.EnvironmentWrites env)

end Effect4.Program.CodeClosure.Slots
