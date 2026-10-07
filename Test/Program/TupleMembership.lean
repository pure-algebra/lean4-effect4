import Effect4.Laws.Program.Typed.Denotation

/-! World-indexed tuple membership controls.
A concrete declaration table witnesses the positive handle premise. -/
namespace Effect4.Test.TupleMembership
open Program Machine

def declaredWorld : Typed.World :=
  { Typed.initialWorld ⟨.unit, .never, Env.Requirement.empty⟩ with
    Ρ := Typed.tableInsert (fun _ => none) ⟨9⟩ .nat }
example : Typed.RefDeclared declaredWorld ⟨9⟩ .nat :=
  ⟨.nat, rfl, Ty.subN_refl _, Ty.subN_refl _⟩
example (w : Typed.World) (key : RefKey) (h : Typed.RefDeclared w key .nat) :
    ∃ out, Val.tupleAt? (.list [.nat 1, Store.Val.some (Val.cell key), .str "x"]) 1 = some out ∧
      Typed.Fits w out (.option (.refOf .nat)) := by
  apply Typed.tuple_typeAt_fits (input := .tuple [.nat, .option (.refOf .nat), .string]) rfl
  exact ⟨True.intro, h, True.intro, True.intro⟩
example (w : Typed.World) (key : RefKey) (h : ¬ Typed.RefDeclared w key .nat) :
    ¬ Typed.Fits w (.list [Val.cell key]) (.tuple [.refOf .nat]) := by
  intro hf
  exact h hf.1

end Effect4.Test.TupleMembership
