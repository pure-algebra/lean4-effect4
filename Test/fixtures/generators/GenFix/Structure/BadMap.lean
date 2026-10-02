import GenFix.Structure.Core
set_option autoImplicit false
universe u v
namespace GenFix.Structure
-- The type and recursive action look right; the String payload is silently replaced.
def ElemOf.map {α : Type u} {β : Type v} (f : α → β) (x : ElemOf α) : ElemOf β :=
  { isOptional := x.isOptional, type := f x.type, note := "corrupted" }
#guard (ElemOf.map (fun n : Nat => n) ⟨true, 7, "original"⟩).note != "original"
end GenFix.Structure
