import Effect4.Laws.Auto.Semantics

/-!
Concept: reactive-scheduling (R12).
Question: the registry claim `random-descent`. Its pointer is `complete_unique`; `bounded` and
`extends_all` state the same theorem's other halves.
Reach: any step function `step : S → D → Option S`, any decision type, any relation `R` that is an
equivalence and a bisimulation of the unlabelled step, under the local diamond up to `R`. All
three premises stay in every statement (Codex's review, DET-OW-01).
Not established: anything of the machine. The machine's raw decisions are no instance: a fire on
an absent owner, a yield verdict and the middleware's installation are always enabled
(`stepDecisionState`), so no live machine is terminal under them (DET-OW-02). An instance needs
an enabled-fire step. A terminal state of it is not a finished machine either: a fuel frontier
and a wait on a promise are terminal too (DET-OW-03).
Unlocks: the checked fragment of decisions row 361, its final-observation proof (D2) and its
canonical driver (D3), which wait until the authoring line asks for them.

A machine labelled by decisions is `step : S → D → Option S`: one decision, one step, `none` when
the decision is not enabled. A tape is a list of decisions (`run`). A state is terminal when no
decision is enabled. If every two one-step successors are `R`-equal or close in one step each,
then one complete tape from a state fixes every complete tape's length and its end up to `R`, and
bounds every tape. This is random descent at its simplest local criterion (van Oostrom, RTA 2007;
cited from the probe's note, not filed). The probe: `docs/research/2026-10-10-schedule-independence/
probes/RandomDescent.lean`.
-/
set_option autoImplicit false

namespace Effect4.Machine.Descent

universe u v
variable {S : Type u} {D : Type v}

/-- Replay a tape. -/
def run (step : S → D → Option S) : S → List D → Option S
  | s, [] => some s
  | s, d :: t => (step s d).bind fun u => run step u t

/-- No decision is enabled. -/
def Terminal (step : S → D → Option S) (s : S) : Prop := ∀ d, step s d = none

/-- `R` is a bisimulation of the unlabelled step relation. -/
def Bisim (step : S → D → Option S) (R : S → S → Prop) : Prop :=
  ∀ s s', R s s' → ∀ d u, step s d = some u → ∃ d' u', step s' d' = some u' ∧ R u u'

/-- The local diamond up to `R`: two one-step successors are `R`-equal or close in one step each.
Any decision may close a side. The disjunction keeps the proof constructive: no decision of `R`
is needed. -/
def Diamond (step : S → D → Option S) (R : S → S → Prop) : Prop :=
  ∀ s d1 d2 s1 s2, step s d1 = some s1 → step s d2 = some s2 →
    R s1 s2 ∨ ∃ e1 e2 v1 v2, step s1 e1 = some v1 ∧ step s2 e2 = some v2 ∧ R v1 v2

theorem run_nil (step : S → D → Option S) (s : S) : run step s [] = some s := rfl

theorem run_cons {step : S → D → Option S} {s u : S} {d : D} {t : List D}
    (h : step s d = some u) : run step s (d :: t) = run step u t := by
  simp only [run, h, Option.bind_some]

theorem run_cons_inv {step : S → D → Option S} {s v : S} {d : D} {t : List D}
    (h : run step s (d :: t) = some v) : ∃ u, step s d = some u ∧ run step u t = some v := by
  simp only [run] at h
  cases hs : step s d with
  | none => rw [hs] at h; cases h
  | some u => rw [hs] at h; exact ⟨u, rfl, h⟩

/-- A terminal state runs only the empty tape. -/
theorem run_terminal {step : S → D → Option S} {s u : S} {r : List D}
    (ht : Terminal step s) (h : run step s r = some u) : r = [] ∧ u = s := by
  cases r with
  | nil => simp only [run, Option.some.injEq] at h; exact ⟨rfl, h.symm⟩
  | cons d t =>
    obtain ⟨w, hw, -⟩ := run_cons_inv h
    rw [ht d] at hw
    cases hw

/-- A bisimulation carries terminality. -/
theorem terminal_transport {step : S → D → Option S} {R : S → S → Prop}
    (sym : ∀ a b, R a b → R b a) (bis : Bisim step R) {t t' : S}
    (ht : Terminal step t) (h : R t t') : Terminal step t' := by
  intro d
  cases hs : step t' d with
  | none => rfl
  | some u =>
    obtain ⟨d', u', hst, -⟩ := bis t' t (sym t t' h) d u hs
    rw [ht d'] at hst
    cases hst

/-- The extension property at length `n`: from any `R`-image of a state with a complete tape of
length `n`, every tape extends to a complete tape of total length `n`, ending `R`-equal. -/
def Extends (step : S → D → Option S) (R : S → S → Prop) (n : Nat) : Prop :=
  ∀ s t (c : List D), run step s c = some t → c.length = n → Terminal step t →
    ∀ s0, R s s0 → ∀ r u, run step s0 r = some u →
      ∃ r' t', run step u r' = some t' ∧ R t t' ∧ r.length + r'.length = n

section
variable {step : S → D → Option S} {R : S → S → Prop}

/-- **Random descent, the step.** Every length up to `n` has the extension property. A step of
`complete_unique` and `bounded`. -/
theorem extends_all (eqv : Equivalence R) (bis : Bisim step R) (dia : Diamond step R) :
    ∀ n, ∀ k ≤ n, Extends step R k := by
  intro n
  induction n with
  | zero =>
    intro k hk s t c hc hlen ht s0 hs0 r u hr
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    have hc0 : c = [] := List.eq_nil_of_length_eq_zero hlen
    subst hc0
    simp only [run, Option.some.injEq] at hc
    subst hc
    have ht0 := terminal_transport (fun _ _ h => eqv.symm h) bis ht hs0
    obtain ⟨hr0, hu⟩ := run_terminal ht0 hr
    subst hr0
    refine ⟨[], u, rfl, ?_, rfl⟩
    rw [hu]
    exact hs0
  | succ m ih =>
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · exact ih k (Nat.le_of_lt_succ hlt)
    subst heq
    intro s t c hc hlen ht s0 hs0 r u hr
    cases c with
    | nil => exact absurd hlen (Nat.zero_ne_add_one m)
    | cons d1 c' =>
      obtain ⟨s1, hs1, hc'⟩ := run_cons_inv hc
      have hlen' : c'.length = m := by
        rw [List.length_cons] at hlen
        omega
      cases r with
      | nil =>
        -- transport the complete tape from `s` to `s0`
        simp only [run, Option.some.injEq] at hr
        subst hr
        obtain ⟨d1', s1', hst', hR1⟩ := bis s s0 hs0 d1 s1 hs1
        obtain ⟨r', t', hr', hRt, hl⟩ := ih m (Nat.le_refl m) s1 t c' hc' hlen' ht s1' hR1 [] s1' rfl
        refine ⟨d1' :: r', t', ?_, hRt, ?_⟩
        · rw [run_cons hst']; exact hr'
        · simp only [List.length_nil, List.length_cons] at hl ⊢; omega
      | cons d r0 =>
        obtain ⟨u1, hu1, hr0⟩ := run_cons_inv hr
        obtain ⟨e, w, hw, hRw⟩ := bis s0 s (eqv.symm hs0) d u1 hu1
        rcases dia s d1 e s1 w hs1 hw with hsw | ⟨e1, e2, v1, v2, hv1, hv2, hRv⟩
        · obtain ⟨r', t', hr', hRt, hl⟩ :=
            ih m (Nat.le_refl m) s1 t c' hc' hlen' ht u1 (eqv.trans hsw (eqv.symm hRw)) r0 u hr0
          refine ⟨r', t', hr', hRt, ?_⟩
          simp only [List.length_cons] at hl ⊢; omega
        · -- from `s1`, the tape `[e1]` extends to a complete tape `c''` from `v1`
          obtain ⟨c'', t'', hc'', hRt'', hl''⟩ :=
            ih m (Nat.le_refl m) s1 t c' hc' hlen' ht s1 (eqv.refl s1) [e1] v1
              (by rw [run_cons hv1]; rfl)
          have hl2 : c''.length + 1 = m := by
            simp only [List.length_cons, List.length_nil] at hl''
            omega
          have ht'' : Terminal step t'' := terminal_transport (fun _ _ h => eqv.symm h) bis ht hRt''
          -- transport `c''` from `v1` to `v2`
          obtain ⟨r2, t3, hr2, hRt3, hl3⟩ :=
            ih (m - 1) (Nat.sub_le m 1) v1 t'' c'' hc'' (by omega) ht'' v2 hRv [] v2 rfl
          have ht3 : Terminal step t3 := terminal_transport (fun _ _ h => eqv.symm h) bis ht'' hRt3
          -- so `w` has the complete tape `e2 :: r2` of length `m`
          have hcw : run step w (e2 :: r2) = some t3 := by rw [run_cons hv2]; exact hr2
          have hlw : (e2 :: r2).length = m := by
            simp only [List.length_cons, List.length_nil] at hl3 ⊢; omega
          obtain ⟨r', t', hr', hRt', hl⟩ :=
            ih m (Nat.le_refl m) w t3 (e2 :: r2) hcw hlw ht3 u1 (eqv.symm hRw) r0 u hr0
          refine ⟨r', t', hr', eqv.trans hRt'' (eqv.trans hRt3 hRt'), ?_⟩
          simp only [List.length_cons] at hl ⊢; omega

/-- **Every complete tape has the same length and an `R`-equal end.** The pointer of the claim
`random-descent`. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem complete_unique (eqv : Equivalence R) (bis : Bisim step R) (dia : Diamond step R)
    {s t1 t2 : S} {c1 c2 : List D} (h1 : run step s c1 = some t1) (ht1 : Terminal step t1)
    (h2 : run step s c2 = some t2) (ht2 : Terminal step t2) :
    R t1 t2 ∧ c1.length = c2.length := by
  obtain ⟨r', t', hr', hR, hl⟩ :=
    extends_all eqv bis dia c1.length c1.length (Nat.le_refl _) s t1 c1 h1 rfl ht1 s
      (eqv.refl s) c2 t2 h2
  obtain ⟨rfl, rfl⟩ := run_terminal ht2 hr'
  exact ⟨hR, by simp only [List.length_nil, Nat.add_zero] at hl; exact hl.symm⟩

/-- **Weak termination gives strong termination**: one complete tape bounds every tape. -/
@[semantics "reactive-scheduling" (requirement := R12)]
theorem bounded (eqv : Equivalence R) (bis : Bisim step R) (dia : Diamond step R)
    {s t u : S} {c r : List D} (hc : run step s c = some t) (ht : Terminal step t)
    (hr : run step s r = some u) : r.length ≤ c.length := by
  obtain ⟨r', t', -, -, hl⟩ :=
    extends_all eqv bis dia c.length c.length (Nat.le_refl _) s t c hc rfl ht s (eqv.refl s) r u hr
  omega

end

end Effect4.Machine.Descent
