import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: store-typing R4, the shared code-graph closure.
This control checks that constructor normalization uses its named bank.
It asserts no program history or host behavior.
-/
set_option autoImplicit false
namespace Test.Program.CodeClosureBank
open Effect4 Effect4.Machine Effect4.Program

example : CodeClosure.Code (fun _ => True) (fun _ => True)
    (.onSuccess (.sync .getCtx) .abort) := by
  aesop (rule_sets := [Effect4.CodeClosure])

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  ⊢ CodeClosure.Code (fun x => True) (fun x => True) ((Prim.sync EffThunk.getCtx).onSuccess EffName.abort)
-/
#guard_msgs (error) in
example : CodeClosure.Code (fun _ => True) (fun _ => True)
    (.onSuccess (.sync .getCtx) .abort) := by
  aesop
end Test.Program.CodeClosureBank
