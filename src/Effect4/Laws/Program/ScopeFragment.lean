import Effect4.Laws.Program.SourceScope
import Effect4.Laws.Program.Typing.Table

/-!
# The direct lexical source fragment

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The existing generated address census checks every source head.
The fragment excludes generators, layers, definitions, calls and program parameters.
Authored binds, iterators, captures, forks and races remain included.
The restriction bounds the first native source ownership bridge.
It makes no statement about excluded source execution or progress.
-/

set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Program

/-- The source heads supported by the first history bridge.
Consumer: `Fragment` and the native callback case census. -/
def directHead : Node NativeOp → Bool
  | .eff (.gen _) => false
  | .eff (.provideLayer _ _ _) => false
  | .eff (.defs _ _ _ _) => false
  | .eff (.invoke _ _ _) => false
  | .eff (.perform (.call _) _) => false
  | .eff (.perform (.param _) _) => false
  | .stmt _ | .stmts _ | .layer _ | .layers _ => false
  | _ => true

/-- Every node of this source belongs to the direct lexical fragment.
The address walk is the existing generated census, without a second traversal. -/
def Fragment (root : NativeEff) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all directHead) = true

/-- The checked fragment supplies the supported head at every actual source address.
Consumer: the source callback closure. -/
theorem Fragment.at {root : NativeEff} (h : Fragment root)
    {path : List Nat} {node : Node NativeOp} (found : Node.at_ (.eff root) path = some node) :
    directHead node = true := by
  have member : path ∈ Node.addresses (.eff root) :=
    (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
  have head := List.all_eq_true.mp h path member
  rw [found] at head
  exact head

end Effect4.Program.SourceScope
