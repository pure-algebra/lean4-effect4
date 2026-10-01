import Effect4.Machine.Term

/-!
# Seat R, question 1: the nested spelling of the record term (red control, pinned)

The brief's literal route (b), `Term.record (fields : List (String × Term))`, nests `Term` under
`List`/`Prod` inside the `Term`/`Terms` mutual block. The tree derives `Term`'s equality
(`Machine/Term.lean:109`, `deriving instance DecidableEq for Term, Terms`) and its wire codec from
the declaration. This file pins what Lean 4.33.1 says to that spelling, so the recommended
spelling (`record (labels : List String) (args : Terms)`, which reuses `Terms` and nests nothing)
is a measured choice, not a taste. Compiles (exit 0): the refusal is held by `#guard_msgs`.
-/

set_option autoImplicit false

namespace SeatR.NestedRed

open Effect4.Program (Lit)

mutual
  inductive NTerm
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : NTerms)
    | record (fields : List (String × NTerm))
  inductive NTerms
    | nil
    | cons (head : NTerm) (tail : NTerms)
end

/-- error: None of the deriving handlers for class `DecidableEq` applied to `NTerm` and `NTerms` -/
#guard_msgs in
deriving instance DecidableEq for NTerm, NTerms

/-! The positive twin: the recommended spelling reuses `Terms` and derives. -/

mutual
  inductive PTerm
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : PTerms)
    | record (labels : List String) (args : PTerms)
    | field (target : PTerm) (index : Nat) (name : String)
  inductive PTerms
    | nil
    | cons (head : PTerm) (tail : PTerms)
end

deriving instance DecidableEq for PTerm, PTerms

#guard decide (PTerm.record ["a"] (.cons (.var 0) .nil) = PTerm.record ["a"] (.cons (.var 0) .nil))
#guard !decide (PTerm.record ["a"] (.cons (.var 0) .nil) = PTerm.record ["b"] (.cons (.var 0) .nil))

end SeatR.NestedRed
