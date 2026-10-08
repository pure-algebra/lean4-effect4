import Effect4.Laws.Modules.Step.Lists
import Effect4.Laws.Modules.Step

/-! Readers and finite controls for common list operations.
Duplicate inputs distinguish removing one match from removing every match.
The shared value laws and Step reading and typing laws carry the general statements. -/
set_option autoImplicit false
open Effect4.Program Effect4.Program.Authoring Effect4.Modules Effect4.Schema.Model
namespace Test.Program.StepLists

def duplicates : Step [] (.list .nat) := .cons (.nat 1) (.cons (.nat 2) (.cons (.nat 1) .nil))
def isOne : Step [.nat] .bool := .eq (.var (.here _ _)) (.nat 1)
def one := Step.Lists.removeFirst duplicates isOne
def all := Step.Lists.removeBy duplicates isOne
#guard @BEq.beq (Bool × List Nat) inferInstance (one.eval (Γ := []) Leaves.opaque ()) (true, [2, 1])
#guard @BEq.beq (List Nat) inferInstance (all.eval (Γ := []) Leaves.opaque ()) [2]
#guard @BEq.beq (Bool × List Nat) inferInstance ((Step.Lists.removeFirst (.nil : Step [] (.list .nat)) isOne).eval (Γ := []) Leaves.opaque ()) (false, [])
#guard @BEq.beq Nat inferInstance ((Step.Lists.headOr (.nil : Step [] (.list .nat)) (.nat 7)).eval (Γ := []) Leaves.opaque ()) 7
#guard @BEq.beq Nat inferInstance ((Step.Lists.headOr duplicates (.nat 7)).eval (Γ := []) Leaves.opaque ()) 1

example : TypesEach nativeSignature (one.term (Input.source [])) {} [] [] (.prod .bool (.list .nat)) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil one rfl (Step.scope_of_alignment one rfl)

-- The first-match rule composes with ordinary list typing at an actual stored step.
example : Reads (one.term (Input.source [])) {} [] []
    (Effect4.Store.Val.list [.bool true, .list [.nat 2, .nat 1]]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil one rfl (Step.scope_of_alignment one rfl)

end Test.Program.StepLists
