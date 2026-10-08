import Effect4.Laws.Program.Typed.RecordValues
import Effect4.Laws.Program.Typed.Membership

/-!
# Named record value controls

These finite controls distinguish absent optional fields from present empty values.
The universal helper statements live in `Laws/Program/Typed/RecordValues.lean`.
No target execution claim is made here.
-/

namespace Effect4.Test.RecordValues
open Effect4.Program Effect4.Program.Typed Effect4.Machine

-- The same present value can fit required and optional declarations.
example : NamedFit [("nickname", false, fun v => v = Val.str "Ada")]
    [.str "nickname"] [.str "Ada"] :=
  (namedFit_cons_eq _ _ _ _ _ _ _).mpr ⟨rfl, trivial⟩

example : NamedFit [("nickname", true, fun v => v = Val.str "Ada")]
    [.str "nickname"] [.str "Ada"] :=
  (namedFit_cons_eq _ _ _ _ _ _ _).mpr ⟨rfl, trivial⟩

-- A missing optional field occupies neither column.
example : NamedFit [("nickname", true, fun v => v = Val.unit)] [] [] := ⟨rfl, trivial⟩

-- An explicit undefined occupies both columns.
example : NamedFit [("nickname", true, fun v => v = Val.unit)]
    [.str "nickname"] [.unit] :=
  (namedFit_cons_eq _ _ _ _ _ _ _).mpr ⟨rfl, trivial⟩

-- A present Option.none also occupies both columns.
example : NamedFit [("nickname", true, fun v => v = Store.Val.none)]
    [.str "nickname"] [Store.Val.none] :=
  (namedFit_cons_eq _ _ _ _ _ _ _).mpr ⟨rfl, trivial⟩

-- Optional-read results retain an outer presence distinction.
example : Store.Val.none ≠ Store.Val.some Val.unit := by intro h; cases h
example : Store.Val.none ≠ Store.Val.some Store.Val.none := by intro h; cases h
example : Store.Val.some Val.unit ≠ Store.Val.some Store.Val.none := by intro h; cases h

-- A required field cannot disappear.
example : ¬ NamedFit [("nickname", false, fun v => v = Val.unit)] [] [] := by
  intro h
  exact Bool.noConfusion h.1

end Effect4.Test.RecordValues
