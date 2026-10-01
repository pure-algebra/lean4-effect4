import Effect4.Laws.Program.IterLimit

/-!
# The limit of the budgeted meaning: controls

Controls for `src/Effect4/Laws/Program/IterLimit.lean` (formal pass, algebra note A8, probe
`P4ComodelIteration.lean`). Positive: a two-round loop converges, read off the fixpoint law; a
loop that never stops converges nowhere, read off leastness. Red: no single budget solves the
fixpoint equation (`budget_not_fixpoint`), which is why the laws are stated for the limit.
-/

set_option autoImplicit false
namespace Test.Program.IterLimit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The step of a two-round loop: from `0` continue at `1`, from anything else stop. -/
def twoRounds : Nat → Effects.Program StoreSig (Nat ⊕ Nat) :=
  fun n => pure (if n = 0 then .inr 1 else .inl n)

/-- A loop that never stops. -/
def spin : Nat → Effects.Program StoreSig (Nat ⊕ Nat) := fun n => pure (.inr n)

/-- The two-round loop converges from `0` with `1`, the stores unchanged: one continue, one
stop, by the fixpoint law. -/
theorem twoRounds_converges (s : Stores) : Conv twoRounds 0 s 1 s :=
  (conv_fixpoint twoRounds 0 s 1 s).mpr (.inr ⟨1, s, rfl, (conv_fixpoint twoRounds 1 s 1 s).mpr
    (.inl rfl)⟩)

/-- A loop that never stops converges nowhere: the empty relation is closed under its two rules,
so by leastness it contains convergence. -/
theorem spin_never_converges (x : Nat) (s : Stores) (y : Nat) (s' : Stores) :
    ¬ Conv spin x s y s' :=
  conv_least spin (fun _ _ _ _ => False) (fun _ _ _ _ h => nomatch h)
    (fun _ _ _ _ _ _ _ r => r) x s y s'

/-- **Red control: a fixed budget is not a fixpoint.** At budget 1 the loop is unfinished, while
one unfolding in front of the same budget finishes: the Elgot equation holds for the limit, not
for any single approximant. -/
theorem budget_not_fixpoint :
    iter twoRounds 1 0 ≠ (twoRounds 0 >>= iterNext (iter twoRounds 1)) := by
  intro h
  change (Effects.Program.pure none : Effects.Program StoreSig (Option Nat)) =
    Effects.Program.pure (some 1) at h
  injection h with h'
  cases h'

/-! The fixpoint equation at budget 1 is refused by computation as well. -/

/--
error: Type mismatch
  rfl
has type
  ?m.24 = ?m.24
but is expected to have type
  iter twoRounds 1 0 = twoRounds 0 >>= iterNext (iter twoRounds 1)
-/
#guard_msgs (error) in
example : iter twoRounds 1 0 = (twoRounds 0 >>= iterNext (iter twoRounds 1)) := rfl

#print axioms twoRounds_converges
#print axioms spin_never_converges
#print axioms budget_not_fixpoint
end Test.Program.IterLimit
