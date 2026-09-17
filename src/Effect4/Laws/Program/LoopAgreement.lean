import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Agreement.Machine

/-!
# The loop agreement: the statement, and the part that is proved

`LoopAgreement e` is obligation O12's machine half (S8a-L): when the budgeted meaning of `e`
finishes at some budget, the machine's ordinary run finishes with that exit and those stores
at every fuel past some bound. The bound is existential on purpose: a loop's step count
depends on its rounds, and no step formula is claimed. By `meaningB_unique` the exit and the
stores do not depend on the budget that found them, so the statement names one answer.

Proved here: the statement on the straight fragment (`loopAgreement_of_straight`), from
`run_eq_meaning` and `denoteB_straight`, with the bound `run_eq_meaning` names. The statement
on all of `Looped` is `Agreement.loopAgreement` (`Laws/Program/Agreement/Loop.lean`), which
imports this module. `Test/Program/LoopAgreementContract.lean` runs the machine on a loop in
every position.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The machine finishes with the budgeted meaning's answer, at every fuel past some bound. -/
def LoopAgreement (e : NativeEff) : Prop :=
  ∀ (k : Nat) (x : ExitV) (s' : Stores), meaningB k e [] Stores.empty = (some x, s') →
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (Api.run e fuel).outcome = Api.Outcome.finished ∧
        (Api.run e fuel).exit = some x ∧ (Api.run e fuel).stores = s'

/-- On the straight fragment the budgeted meaning is the meaning, at every budget. -/
theorem meaningB_straight (k : Nat) (e : NativeEff) (env : List Val) (s : Stores)
    (hs : Straight e = true) :
    meaningB k e env s = (some (meaning e env s).1, (meaning e env s).2) := by
  unfold meaningB
  rw [denoteB_straight k e env hs, runP_map]
  rfl

/-- The loop agreement holds on the straight fragment, with `run_eq_meaning`'s bound. -/
theorem loopAgreement_of_straight (e : NativeEff) (hs : Straight e = true) :
    LoopAgreement e := by
  intro k x s' h
  rw [meaningB_straight k e [] Stores.empty hs] at h
  cases h
  refine ⟨max (depth e) (2 * steps e + 6), fun fuel hfuel => ?_⟩
  exact run_eq_meaning e fuel hs (Nat.le_trans (Nat.le_max_left _ _) hfuel)
    (Nat.le_trans (Nat.le_max_right _ _) hfuel)

end Effect4.Program.Agreement
