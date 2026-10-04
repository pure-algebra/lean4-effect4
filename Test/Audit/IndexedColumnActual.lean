import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Auto.Obligations

/-! Phase B controls against the actual generated machine predicates.
The generated projections, each closed by the `Effect4.TypedState` bank. These names use the
two leaf labels HeapCell and PromiseCell from the source table. -/
open Effect4 Effect4.Machine Effect4.Program.Typed

namespace Test.IndexedColumnActual

def refLeafType {W : Type} (P : Preds W) : W → RefKey → Val → Prop := P.HeapCell
def cellLeafType {W : Type} (P : Preds W) : W → DeferredKey → DeferredCell → Prop := P.PromiseCell

theorem refs_projection {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    StoresOk P w e s →
      ∀ i v, s.refs[i]? = some v → P.HeapCell w ⟨i⟩ v := by
  aesop (rule_sets := [Effect4.TypedState])

theorem cells_projection {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    StoresOk P w e s →
      ∀ i c, s.deferreds.cells[i]? = some c → P.PromiseCell w ⟨i⟩ c := by
  aesop (rule_sets := [Effect4.TypedState])

theorem cells_owner_projection {W : Type} (P : Preds W) (w : W) (e : Expect)
    (s : DeferredStore) :
    DeferredStoreOk P w e s →
      ∀ i c, s.cells[i]? = some c → P.PromiseCell w ⟨i⟩ c := by
  aesop (rule_sets := [Effect4.TypedState])

-- The indexed cell owner cannot account away the due occurrence of Completion.
theorem due_group_retained {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    StoresOk P w e s → P.PromiseTable w s := by
  aesop (rule_sets := [Effect4.TypedState])

end Test.IndexedColumnActual

