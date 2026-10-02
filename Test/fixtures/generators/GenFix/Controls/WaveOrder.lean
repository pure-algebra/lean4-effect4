import GenFix.Wave.TyView

/-!
# The order at the wave's cross-head edges, through the generated laws (a generator fixture)

Codex's controls (19:30) and probe P's (`P/probes/P2Ty.lean:1281-1285`), on the wave fixture whose
view was generated in table mode (`GenFix.Wave.TyView`): the accepted cross-head case
`nat ⊑ number` — derived through the closure, not an entry of the table — and its rejected
converse, each proved through the restated laws rather than by evaluating `sub`; the other declared
edge outside the number tower; and the cyclic table's two-way reachability, the reason the
generator refuses one (`GenFix.LeafCyclic`).
-/

set_option autoImplicit false

namespace GenFix.Controls

open GenFix.Wave

/-- **The accepted cross-head case**: `nat` below `number`, by the different-head theorem
restated over the table (`sub` at two different heads IS the declared edge's closure). -/
theorem nat_sub_number : Ty.sub .nat .number = true :=
  (Ty.sub_eq_leafRule_of_not_sameHead .nat .number rfl rfl rfl rfl).trans rfl

/-- **Its rejected converse**: `number` is not below `nat`, by the different-head theorem with the
table's hypothesis (`hleaf`: no declared edge from `number` to `nat`). -/
theorem number_not_sub_nat : Ty.sub .number .nat = false :=
  Ty.sub_eq_false_of_not_sameHead .number .nat rfl rfl rfl rfl rfl

/-- `nat ⊑ number` is derived, never an entry of the table. -/
theorem nat_number_not_an_entry : (Ty.LeafHead.nat, Ty.LeafHead.number) ∉ Ty.leafEdges := by
  decide

/-- The other declared edge outside the number tower, and its converse. -/
theorem undefined_sub_unit : Ty.sub .undefined .unit = true :=
  (Ty.sub_eq_leafRule_of_not_sameHead .undefined .unit rfl rfl rfl rfl).trans rfl

theorem unit_not_sub_undefined : Ty.sub .unit .undefined = false :=
  Ty.sub_eq_false_of_not_sameHead .unit .undefined rfl rfl rfl rfl rfl

-- the same, computed (probe P's guards, `P2Ty.lean:1281-1283`)
#guard Ty.sub .nat .int && Ty.sub .int .number && Ty.sub .nat .number && Ty.sub .undefined .unit
#guard !Ty.sub .int .nat && !Ty.sub .number .int && !Ty.sub .unit .undefined && !Ty.sub .null .unit
-- the cyclic table (`int` below `nat` added) relates `nat` and `int` both ways (`P2Ty.lean:1285`)
#guard Ty.leafReach ((.int, .nat) :: Ty.leafEdges) 5 .nat .int &&
  Ty.leafReach ((.int, .nat) :: Ty.leafEdges) 5 .int .nat

end GenFix.Controls

#print axioms GenFix.Controls.nat_sub_number
#print axioms GenFix.Controls.number_not_sub_nat
#print axioms GenFix.Controls.nat_number_not_an_entry
#print axioms GenFix.Controls.undefined_sub_unit
#print axioms GenFix.Controls.unit_not_sub_undefined
