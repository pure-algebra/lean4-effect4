import Effect4.Laws.Store.Names

/-!
# Test.Store.Names

A reader and a control for `Effect4.Laws.Store.Names`.

- The reader: wrapping a value as an exit's success payload (`ctor 0 [v]`) is parametric, by the
  fold's agreement and nothing else.
- The control: a map that invents a handle is not parametric, because `Parametric.support` would
  put that handle in the support of `unit`, which names none.
-/

namespace Test.Store.Names

open Effect4.Store Effect4.Store.Names

/-- A reader: a real wrapping map is parametric. -/
example : Parametric fun v => .ctor 0 [v] :=
  fun _ _ _ _ h => Rel.ctor_iff.mpr ⟨rfl, .cons h .nil⟩

/-- A control: a map that invents a handle is not parametric. -/
example : ¬ Parametric fun _ => .handle 1 0 := by
  intro hf
  have bound := Parametric.support hf .unit (1, 0) List.mem_cons_self
  exact nomatch bound

end Test.Store.Names
