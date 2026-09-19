import Effect4.Laws.Program.Typing.CheckInversion

/-!
# The negative fixture of the `Effect4.Checker` bank (tooling plan 1.2)

`Effect4.Program.Checker.inv_succeed` (`src/Effect4/Laws/Program/Typing/CheckInversion.lean`) closes with
`aesop (rule_sets := [Effect4.Checker])`. This is the other half: the same goal,
and `aesop` with **no clause at all** — which fails, so the bank is what closed it.

The clause is omitted rather than negated. `(rule_sets := [-Effect4.Checker])` would error at the
clause itself, because aesop refuses to subtract a set that is not active
(`Aesop/Frontend/Tactic.lean`), and an error at the clause says nothing about the goal. The
failure is captured by `#guard_msgs (error)`, so this module is green: what it pins is that the
message is still exactly this one.
-/

namespace Test.Program.CheckerRulesRed

open Effect4.Program Effect4.Program.Checker

/--
error: unsolved goals
Op : Type
sig : Signature Op
env : TyEnv
p : List Nat
value : Term
t : EffTy
a : check sig env p (Eff.succeed value) = Except.ok t
⊢ ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty
-/
#guard_msgs (error, drop warning) in
example {Op : Type} (sig : Signature Op) (env : TyEnv) (p : List Nat) (value : Term) :
    ∀ t, check sig env p (.succeed value) = .ok t →
      ∃ ty, termTy sig env value = some ty ∧ t = EffTy.pure ty := by
  aesop

#print axioms Effect4.Program.Checker.inv_succeed

end Test.Program.CheckerRulesRed
