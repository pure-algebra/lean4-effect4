import Cas.Llm.Judge

/-!
# The judge measured — compositionality scoped to the grammar

`Judge.Compositional` quantifies over ALL strings, and no measurement
reaches that far. Scope the law instead to the names the grammar
actually mints. The registry is closed and still, so the name fragment
is FINITE, and the hypothesis stops being an article of faith and
becomes an ARITHMETIC MEASUREMENT: count the pairs on which the
morphism law fails, over an explicit list of them.

Counts, not rates — the module's name notwithstanding. A rate is a
PRESENTATION over `(defectCount F, F.length)`; the division is the
reader's, and it buys the algebra nothing. The count is what composes:
`defectCount` is a monoid hom from fragments under append into `Nat`
under addition (`defectCount_append`), which is the `Word.View` shape,
so a measurement grows with the word instead of being recomputed from
it.

ε = 0 recovers the exact law ON THE FRAGMENT
(`compositionalOn_iff`), and the global Level-2 hypothesis makes every
fragment defect-free (`Compositional.compositionalOn`). That
implication runs one way only: passing a finite study is NECESSARY for
the global claim and never sufficient, and the fragment measured is
the whole scope of what a study may assert (C5). A nonzero count is
the informative outcome — it refutes Level 2 outright and localizes
where human meaning declines to compose.

`discharges(judge-stable): STABLE is defined here` — Level 1 of the
judge-hypothesis lattice is `Judge.Stable` below: invariance under a
declared semantically-inert relation. That relation is a PARAMETER,
the same move `Word.columnBy` makes with its classifier — which
variations count as inert is the caller's declaration and never this
module's. LIMIT-STABLE (Level 3) is NOT defined here; that rung stays
owed at the ladder in `Judge`, and nothing below reaches it.

This module imports `Judge` and nothing else: the measurement is prior
to the store, and every statement holds of an arbitrary frozen judge.
-/

namespace Cas.Llm

/-! ## Level 1 — stability under inert variation -/

/-- Level 1 of the judge-hypothesis lattice: INVARIANCE under a
declared semantically-inert relation — the same verdict for a name and
its alias, its paraphrase, its harmless respelling. `E` is a
PARAMETER, exactly as `Word.columnBy` takes its classifier rather than
fixing one: which variations count as inert is the caller's
declaration, and this module never supplies it. Everything above this
rung presupposes it; nothing here measures it, because the count below
measures Level 2 alone. -/
def Judge.Stable (E : String → String → Prop) (J : Judge) : Prop :=
  ∀ s t, E s t → J s = J t

/-! ## The finite measurement of Level 2 -/

/-- One pair's verdict on the morphism law, COMPUTABLE: does the
judge's reading of the concatenation differ from the conjunction of
its readings of the parts? Three frozen calls and one boolean. This is
white-box arithmetic over receipts — a defect is computed, never
judged. -/
def Judge.violates (J : Judge) (p : String × String) : Bool :=
  !(J (p.1 ++ p.2) == (J p.1 && J p.2))

/-- The MEASUREMENT: how many pairs of an explicit fragment break the
morphism law. Because the registry is closed and still, `F` is a list
that can be enumerated and actually called, so Level 2 becomes a
finishable arithmetic fact about one frozen judge instead of an
unbounded claim about language. A COUNT, not a rate: a rate is what a
presentation makes of `(defectCount F, F.length)`, and the division
carries no structure the count does not already carry. -/
def Judge.defectCount (J : Judge) (F : List (String × String)) : Nat :=
  (F.filter (fun p => J.violates p)).length

/-- The count is a MONOID HOM from fragments under append into `Nat`
under addition — the `Word.View` shape, and the same append-locality
`columnBy_append` gives the columns. The measurement lane reads this as
INCREMENTAL MEASUREMENT: a fragment that grows by a suffix costs only
the suffix's calls, and a per-column defect view is maintained by
adding to it rather than by re-measuring the board. -/
theorem Judge.defectCount_append (J : Judge) (F G : List (String × String)) :
    J.defectCount (F ++ G) = J.defectCount F + J.defectCount G := by
  show (List.filter _ (F ++ G)).length
      = (List.filter _ F).length + (List.filter _ G).length
  rw [List.filter_append, List.length_append]

/-- ε = 0 on a fragment: the judge breaks the morphism law nowhere in
`F`. This is the proof-world end of the graded family — the kernel
takes only this rung — and a positive count is a measurement-world
claim that CONSUMES the defect view rather than licensing a theorem
from it. Keeping the two apart is the whole reason the fragment is
carried in the statement. -/
def Judge.CompositionalOn (J : Judge) (F : List (String × String)) : Prop :=
  J.defectCount F = 0

/-- THE RECOVERY: zero defects is not an approximation of the law but
the law itself, pointwise on `F`. So the count is an honest carrier —
nothing is lost passing between the arithmetic a study reports and the
equation a proof would use — and what is recovered is scoped to `F`
and to nothing outside it. -/
theorem Judge.compositionalOn_iff {J : Judge} {F : List (String × String)} :
    J.CompositionalOn F ↔ ∀ p ∈ F, J (p.1 ++ p.2) = (J p.1 && J p.2) := by
  -- One pair first: a clean verdict IS the equation, with no negation
  -- in between. `List.filter_eq_nil_iff` would shorten the induction
  -- below but reaches through `Classical.choice`, which this library's
  -- axiom ceiling does not admit — so the fragment is peeled by hand.
  have key : ∀ p : String × String,
      J.violates p = false ↔ J (p.1 ++ p.2) = (J p.1 && J p.2) := by
    intro p
    show (!(J (p.1 ++ p.2) == (J p.1 && J p.2))) = false ↔ _
    rw [Bool.not_eq_false', beq_iff_eq]
  show (List.filter (fun p => J.violates p) F).length = 0 ↔ _
  induction F with
  | nil => exact ⟨(fun _ _ hp => nomatch hp), (fun _ => rfl)⟩
  | cons a F ih =>
    rw [List.filter_cons]
    rcases Bool.eq_false_or_eq_true (J.violates a) with ha | ha
    · rw [if_pos ha, List.length_cons]
      refine ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => ?_⟩
      have hf : J.violates a = false := (key a).mpr (h a List.mem_cons_self)
      rw [hf] at ha
      exact Bool.noConfusion ha
    · rw [if_neg (by rw [ha]; exact Bool.false_ne_true)]
      refine ⟨fun h p hp => ?_,
        fun h => ih.mpr fun p hp => h p (List.mem_cons_of_mem a hp)⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact (key p).mp ha
      · exact ih.mp h p hp'

/-- The global hypothesis is fragment-defect-freedom EVERYWHERE: if
Level 2 holds of `J`, every fragment measures zero. Read in the
direction a study actually runs, this is a NECESSARY condition and
never a sufficient one — a fragment that measures clean has said
nothing about the strings it omits, and the fragment IS the scope of
what the study may claim (C5). The informative outcome is the other
one: a single defect refutes Level 2 outright. -/
theorem Judge.Compositional.compositionalOn {J : Judge} (h : J.Compositional)
    (F : List (String × String)) : J.CompositionalOn F :=
  Judge.compositionalOn_iff.mpr fun p _ => h.2 p.1 p.2

/-- Clean fragments compose: two studies that each measured zero
compose into one study that measures zero, straight off the hom. A
defect study is therefore assembled from independently measured
pieces — per column, per session — without re-running one call. -/
theorem Judge.CompositionalOn.append {J : Judge} {F G : List (String × String)}
    (hF : J.CompositionalOn F) (hG : J.CompositionalOn G) :
    J.CompositionalOn (F ++ G) := by
  have hF' : J.defectCount F = 0 := hF
  have hG' : J.defectCount G = 0 := hG
  show J.defectCount (F ++ G) = 0
  rw [Judge.defectCount_append, hF', hG']

end Cas.Llm
