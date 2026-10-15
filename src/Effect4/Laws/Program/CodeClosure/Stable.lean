import Effect4.Laws.Program.CodeClosure.Qualified.Stable
import Effect4.Laws.Program.CodeClosure.Interp
import Effect4.Laws.Program.AnswerSlots.Stable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual source callbacks retain one supplied code annotation through native frames.
Consumers: the Prefix stable instance and both Timeout numeric endpoint producers.
Reach: the existing direct source fragment, actual callback views, and actual saved suffixes.
Limit: this instance supplies no initialization, numeric effects, or command history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

abbrev prefixSpec (root : NativeEff) (table : RowTable) (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefixSpec root table point env (Qualified.EnvironmentWrites env)

abbrev prefix_ofExit (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_ofExit point env (Qualified.EnvironmentWrites env)

abbrev prefix_armA (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_armA root fragment point env (Qualified.EnvironmentWrites env)

abbrev prefix_armE (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_armE root fragment point env (Qualified.EnvironmentWrites env)

abbrev prefix_finalizerCode (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_finalizerCode root point env (Qualified.EnvironmentWrites env)

abbrev prefixEdge (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefixEdge point env (Qualified.EnvironmentWrites env)

abbrev prefix_path (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_path point env (Qualified.EnvironmentWrites env)

abbrev prefix_path_owned (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_path_owned point env (Qualified.EnvironmentWrites env)

abbrev prefix_family (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_family root fragment point env (Qualified.EnvironmentWrites env)

abbrev prefix_head (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefix_head root fragment point env (Qualified.EnvironmentWrites env)

abbrev prefixLaws (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) := @Qualified.prefixLaws root fragment point env (Qualified.EnvironmentWrites env)

end Effect4.Program.CodeClosure.Slots
