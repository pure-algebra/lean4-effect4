import ProbeQ.TyView

/-!
# Q2: the generated view of `ProbeQ.Ty` (record appended), its law shapes and receipts

Seat Q probe (2026-10-01). `ProbeQ.TyView` is written by the patched copy
`Q/tools/Effect4Gen/View.lean` from `ProbeQ.Ty` and `Q/generated/variances-record-only.json`.
-/

open ProbeQ ProbeQ.Ty

-- the law, the same statement as the tree's (`Laws/Program/TyView.lean:333`)
#check @Ty.sub_eq_args
-- the field-list arm lemma: the head is a premise
#check @Ty.sub_args_record
-- the two laws whose statements change at a head of variable arity
#check @Ty.eq_of_sameHead
#check @Ty.argsBelow_antisymm
#check @Ty.args

-- computed: the law at record pairs (permuted, depth, names, width)
#guard Ty.sub (.record [("b", .nat), ("a", .bool)]) (.record [("a", .bool), ("b", .nat)]) =
  (Ty.sameHead (.record [("b", .nat), ("a", .bool)]) (.record [("a", .bool), ("b", .nat)]) &&
   Ty.argsBelow Ty.sub (.record [("b", .nat), ("a", .bool)]) (.record [("a", .bool), ("b", .nat)]))
#guard Ty.args (.record [("b", .nat), ("a", .bool)]) = [(.co, .bool), (.co, .nat)]
#guard Ty.sameHead (.record [("b", .nat), ("a", .bool)]) (.record [("a", .bool), ("b", .nat)])
#guard !Ty.sameHead (.record [("a", .nat)]) (.record [("b", .nat)])

/-- Red control (proved): without the canonicity premise the view's node law is false at a
record. A permuted record has its canonical record's head and children and is another term. -/
theorem eq_of_sameHead_needs_canon :
    ¬ ∀ a b : Ty, Ty.sameHead a b = true → a.args.map Prod.snd = b.args.map Prod.snd → a = b := by
  intro h
  have := h (.record [("b", .nat), ("a", .bool)]) (.record [("a", .bool), ("b", .nat)]) (by decide)
    (by decide)
  exact absurd this (by decide)

#print axioms Ty.sub_eq_args
#print axioms Ty.sub_eq_false_of_not_sameHead
#print axioms Ty.sub_eq_argsBelow_of_sameHead
#print axioms Ty.sub_args_record
#print axioms Ty.eq_of_sameHead
#print axioms Ty.eq_of_sameHead_nil
#print axioms Ty.argsBelow_antisymm
#print axioms Ty.argsBelow_trans
#print axioms Ty.argsBelow_refl
#print axioms Ty.args_congr
#print axioms Ty.sameHead_refl
#print axioms Ty.sameHead_symm
#print axioms Ty.sameHead_trans
#print axioms Ty.sizeOf_args
#print axioms Ty.headCanon_of_args_nil
#print axioms Ty.eq_of_fields_record
#print axioms eq_of_sameHead_needs_canon
