import Effect4.Laws.Program.AtomRules

/-!
# The negative fixture of the `Effect4.Atoms` bank (tooling plan 2.2)

`Effect4.Program.pair_inv_closes` (`src/Effect4/Laws/Program/AtomRules.lean`) closes with
`aesop (rule_sets := [Effect4.Atoms])`. This is the other half: the same goal, the same
hypothesis, and `aesop` with **no clause at all** — which fails, so the bank is what closed it.

The clause is omitted rather than negated. `(rule_sets := [-Effect4.Atoms])` would error at the
clause itself, because aesop refuses to subtract a set that is not active
(`Aesop/Frontend/Tactic.lean`), and an error at the clause says nothing about the goal. The
failure is captured by `#guard_msgs (error)`, so this module is green: what it pins is that the
message is still exactly this one.
-/

namespace Test.Program.AtomRulesRed

open Effect4 Effect4.Machine Effect4.Program

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  vs : List Val
  h : Fits vs [Ty.nat, Ty.nat]
  ⊢ ∃ m n, vs = [Val.nat m, Val.nat n]
-/
#guard_msgs (error) in
example {vs : List Val} (h : Fits vs [Ty.nat, Ty.nat]) :
    ∃ m n : Nat, vs = [Val.nat m, Val.nat n] := by
  aesop

#print axioms Effect4.Program.pair_inv_closes

end Test.Program.AtomRulesRed
