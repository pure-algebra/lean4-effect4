import Effect4.Modules.Step.Elab.Inputs
import Effect4.Laws.Modules.Step.Lists
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Tuples
import Effect4.Laws.Schema.Identity
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Schema Effect4.Schema.Model Effect4.Machine Effect4.Store
namespace Test.ModuleBoundaryFinal
-- Refusing used captures retain their original source location, even on an empty list.
def bad : TermSrc := fun env path => .error ⟨path, .unbound (if env.names.length == 1 then "captured" else "wrongScope")⟩
def used : Step [.list .nat, .nat] .nat :=
  .fold (.var (.here _ _)) (.nat 0) (.var (.there _ (.there _ (.there _ (.here _ _)))))
#guard match used.term (Input.source [app "nil" [], bad]) {names := ["xs"]} [4] with
  | .error ⟨path, .unbound name⟩ => path == [4] && name == "captured"
  | _ => false
-- A syntactically present capture is elaborated even when the loop list is empty.
#guard match used.term (Input.source [app "nil" [], bad]) {names := ["xs"]} [] with
  | .error _ => true
  | .ok _ => false
-- Transparent aliases to contexts and Step types remain name-safe.
step_context% Ctx (hint : .nat, id : .nat)
abbrev ContextAlias := Ctx
abbrev TreeAlias (Γ : List Ty) (t : Ty) := Step Γ t
def aliased : TreeAlias ContextAlias.types .nat := step_inputs% ContextAlias =>
  let outer : TreeAlias ContextAlias.types .nat := .add id hint
  let literals : TreeAlias ContextAlias.types (.list .nat) := .cons (.nat 1) .nil
  fold_step% literals from total := .nat 0 with entry => .add total outer
#guard match aliased.term (input_sources% (ContextAlias) {id := nat 3, hint := nat 9}) {} [] with
  | .ok tree => evalTerm [] tree == some (.nat 12)
  | .error _ => false
-- Exact flat tuple shape does not grant Modeled admission.
#guard Model.refusal (.tuple [.nat, .bool, .string]) == some "tuple"
#guard (imageAt Leaves.opaque (.tuple [.nat, .bool, .string])).toVal
  ((3 : Nat), (true, ("x", ()))) == Effect4.Store.Val.list [.nat 3, .bool true, .str "x"]
#guard (imageAt Leaves.opaque (.tuple [.nat, .bool, .string])).ofVal
  (Effect4.Store.Val.list [.nat 3, .bool true]) |>.isNone
-- Opaque equal-looking non-promise values have no native comparison reading.
#guard !Model.deferredEqual Leaves.opaque (.nat 3) (.nat 3)
#guard nativeAtom "sameHandle" [.nat 3, .nat 3] == none
end Test.ModuleBoundaryFinal
