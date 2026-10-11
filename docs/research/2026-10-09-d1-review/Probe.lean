import Tools.View.FlowOrder

open Tools.View Tools.View.Flow Tools.View.AGraph

-- Inspect the landed declarations; this review introduces no theorem.
#print axioms overlay_comm
#print axioms overlay_assoc
#print axioms empty_connect
#print axioms connect_empty
#print axioms connect_assoc
#print axioms connect_overlay
#print axioms overlay_connect
#print axioms decompose
#print axioms overlay_idem
#print axioms absorb
#print axioms Tools.View.Flow.lay_realizes
#print axioms Tools.View.Flow.place_keeps_order

namespace D1Review

def leaf (key : String) : Flow := .node key key ""
def flow : Flow := .par .fork "parallel" [leaf "a", .seq [leaf "b", leaf "c"]]

-- The source's informal slogan reverses the theorem's implication.
-- This is its smallest distinct-key parallel negative control, not a new claim.
#guard (by
  letI : Decidable ((denote flow.order).edge "a" "c") := by
    dsimp only [flow, leaf, Flow.order, orderPar, orderSeq, denote]
    infer_instance
  exact decide (¬ (denote flow.order).edge "a" "c"))
#guard (by
  letI : Decidable ((denote flow.order).edge "b" "c") := by
    dsimp only [flow, leaf, Flow.order, orderPar, orderSeq, denote]
    infer_instance
  exact decide ((denote flow.order).edge "b" "c"))
#guard (layout flow).edgesDescend
#guard (layout flow).boxesApart
#guard ((layout flow).find "a").isSome
#guard ((layout flow).find "c").isSome
#guard (match (layout flow).find "a", (layout flow).find "c" with
  | some a, some c => a.y + itemH a ≤ c.y
  | _, _ => false)

end D1Review
