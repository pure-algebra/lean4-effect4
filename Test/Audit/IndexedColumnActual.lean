import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Auto.Obligations

/-! Phase B controls against the actual generated machine predicates.
Statements only; their obligations remain explicit. These names use the two
leaf labels HeapCell and PromiseCell from the source table. Preserve this wanted
snapshot before the instrument is allowed to close projections. -/
open Effect4 Effect4.Machine Effect4.Program.Typed

namespace Test.IndexedColumnActual

def refLeafType {W : Type} (P : Preds W) : W → RefKey → Val → Prop := P.HeapCell
def cellLeafType {W : Type} (P : Preds W) : W → DeferredKey → DeferredCell → Prop := P.PromiseCell

def refs_projection {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    ProofGraph.Obligation (StoresOk P w e s →
      ∀ i v, s.refs[i]? = some v → P.HeapCell w ⟨i⟩ v) := ⟨⟩

def cells_projection {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    ProofGraph.Obligation (StoresOk P w e s →
      ∀ i c, s.deferreds.cells[i]? = some c → P.PromiseCell w ⟨i⟩ c) := ⟨⟩

def cells_owner_projection {W : Type} (P : Preds W) (w : W) (e : Expect)
    (s : DeferredStore) :
    ProofGraph.Obligation (DeferredStoreOk P w e s →
      ∀ i c, s.cells[i]? = some c → P.PromiseCell w ⟨i⟩ c) := ⟨⟩

-- The indexed cell owner cannot account away the due occurrence of Completion.
def due_group_retained {W : Type} (P : Preds W) (w : W) (e : Expect) (s : Stores) :
    ProofGraph.Obligation (StoresOk P w e s → P.PromiseTable w s) := ⟨⟩

end Test.IndexedColumnActual

#typed_state_obligations Test.IndexedColumnActual ceiling 4 using aesop (rule_sets := [Effect4.TypedState])
