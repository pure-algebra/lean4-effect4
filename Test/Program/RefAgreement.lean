import Effect4.Laws.Library.Ref.Callback
import Test.Program.StepCallback

/-!
# The Ref connector at a real captured update

The reader applies model agreement to a callback that returns the old value and stores a sum.
The typing reader starts with captures checked only at the caller's scope.
These consume the shared connectors; they do not restate their generic statements.
-/

set_option autoImplicit false
namespace Test.Program.RefAgreement
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Schema Effect4.Schema.Model
open Test.Program.StepCallback (Captures CallbackInputs caller callerValues sources)

/-- The independent numeric transition adds the supplied increment. -/
def transition (increment : Nat) (current : Nat) : Nat × Nat :=
  (current, current + increment)

def body : Step CallbackInputs.types (.prod .nat .nat) :=
  step_inputs% CallbackInputs => .pair current (.add current outer)

def operation : Src NativeOp := Step.callback body sources (Authoring.Ref.modifyWith (var "r"))

example : ∃ term request,
    operation caller [] = .ok (.perform (.refModifyWith term) request) ∧
    evalTerm callerValues request = some (Machine.Val.cell ⟨0⟩) ∧
    Machine.syncOpStep (.refModify ⟨0⟩ term callerValues)
      { Machine.Stores.empty with refs := [.nat 3] } =
      some ({ Machine.Stores.empty with refs := [.nat 10] }, .nat 3) := by
  have inputs : ∀ {t : Ty} (x : Input Captures.types t),
      Reads (sources x) caller [] callerValues
        ((imageAt Leaves.deferredKeys t).toVal (x.get ((7 : Nat), ()))) := by
    intro t x
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Effect4.Ref.modify_callback_agrees (L := Leaves.deferredKeys) body sources
    ((7 : Nat), ()) (transition 7) (3 : Nat) rfl inputs
    ⟨.var 0, rfl, rfl⟩ rfl rfl rfl

/-- The original caller scope contains a reference and a numeric capture. -/
def scope : TypedScope := ⟨caller, [.refOf .nat, .nat], rfl⟩

example : Answers nativeSignature operation scope .nat := by
  have reference : Typed nativeSignature (var "r") scope (.refOf .nat) :=
    fun _ _ => ⟨.var 0, rfl, rfl⟩
  have inputs : ∀ {t : Ty} (x : Input Captures.types t),
      Typed nativeSignature (sources x) scope t := by
    intro t x path const
    cases x with
    | here => exact ⟨.var 1, rfl, rfl⟩
    | there _ x => nomatch x
  exact Effect4.Ref.modify_callback_answers body sources rfl (nodesFormed_of_check rfl)
    rfl (nodesFormed_of_check rfl) reference inputs (Step.facts_of_normal body rfl)

-- Same reply type and value do not certify the update's behavior.
#guard Machine.syncOpStep
  (.refModify ⟨0⟩ (.app "pair" (.cons (.var 2) (.cons (.var 2) .nil))) callerValues)
  { Machine.Stores.empty with refs := [.nat 3] } !=
    some ({ Machine.Stores.empty with refs := [.nat 10] }, .nat 3)

end Test.Program.RefAgreement
