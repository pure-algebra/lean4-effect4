import Effect4.Data.Constructive

/-!
# Constructive standard library axiom receipts

Every declaration in `Effect4.Data.Constructive` must stay within the repository's
strict axiom ceiling: propositional extensionality (`propext`) and quotient soundness
(`Quot.sound`). None may reach `Classical.choice`.
-/

#print axioms Effect4.Constructive.Option.bind_eq_some_iff
#print axioms Effect4.Constructive.Option.map_eq_some_iff
#print axioms Effect4.Constructive.Option.bind_eq_none_iff
#print axioms Effect4.Constructive.Option.isSome_iff_exists
#print axioms Effect4.Constructive.Option.isNone_iff_eq_none
#print axioms Effect4.Constructive.Bool.and_eq_true_iff
#print axioms Effect4.Constructive.Bool.or_eq_true_iff
#print axioms Effect4.Constructive.Bool.not_eq_true_iff
#print axioms Effect4.Constructive.Decidable.decide_and
#print axioms Effect4.Constructive.Decidable.decide_or
#print axioms Effect4.Constructive.Decidable.decide_iff
#print axioms Effect4.Constructive.List.all_eq_true_iff
#print axioms Effect4.Constructive.List.any_eq_true_iff
#print axioms Effect4.Constructive.List.find?_eq_some_iff
#print axioms Effect4.Constructive.List.lookup_mem
