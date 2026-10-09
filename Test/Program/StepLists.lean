import Effect4.Laws.Step.Lists
import Effect4.Laws.Step

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

-- The fused pass retains duplicate matches and maps only selected items.
def shifted : Step [.nat] .nat := .add (.var (.here _ _)) (.nat 10)
def fused := Step.Lists.filterMap duplicates isOne shifted
def changed := Step.Lists.filterMapWith duplicates (.nil : Step [] (.list .bool)) isOne isOne
#guard @BEq.beq (List Nat) inferInstance (fused.eval (Γ := []) Leaves.opaque ()) [11, 11]
#guard @BEq.beq (List Bool) inferInstance (changed.eval (Γ := []) Leaves.opaque ()) [true, true]
#guard @BEq.beq (List Nat) inferInstance
  ((Step.Lists.filterMap (.nil : Step [] (.list .nat)) isOne shifted).eval (Γ := []) Leaves.opaque ()) []
#guard @BEq.beq (List Nat) inferInstance
  ((Step.Lists.filterMap duplicates (.bool false) shifted).eval (Γ := []) Leaves.opaque ()) []
private def folds : Effect4.Program.TermAlgebra (fun _ => Nat) where
  term_var _ := 0
  term_lit _ := 0
  term_app _ args := args
  term_record _ _ values := values
  term_field _ target _ := target
  term_recordSet target _ value := target + value
  term_tupleAt target _ := target
  term_fold _ list init body := 1 + list + init + body
  terms_nil := 0
  terms_cons head tail := head + tail
-- This finite emitted term contains one fold, including its empty-list witness.
#guard ((fused.term (Input.source [])) {} []).toOption.map
  (Effect4.Program.cata_term folds) == some 1

example : TypesEach nativeSignature (changed.term (Input.source [])) {} [] [] (.list .bool) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil changed rfl (Step.scope_of_alignment changed rfl)
example : Reads (fused.term (Input.source [])) {} [] [] (Effect4.Store.Val.list [.nat 11, .nat 11]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil fused rfl (Step.scope_of_alignment fused rfl)
-- The general equation is read at the changing-type constructor's actual carrier.
example : changed.eval (Γ := []) Leaves.opaque () =
    ((duplicates.eval (Γ := []) Leaves.opaque ()).filter fun item => isOne.eval (Γ := [.nat]) Leaves.opaque (item, ())).map
      (fun item => isOne.eval (Γ := [.nat]) Leaves.opaque (item, ())) :=
  Step.Lists.eval_filterMapWith Leaves.opaque duplicates .nil isOne isOne ()

end Test.Program.StepLists
