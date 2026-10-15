import Test.Dogfood.Scenario.Atomic.StoreFacts

/-!
Concept: store-typing, R4, the scenario claim `atomic`.
The endpoint connects request histories to their stage observation.
The observation algebra supplies the `counted` and `committed` consumers.
No progress or host agreement is asserted.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.Store
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Run (ControlHistory)

/-- **The stages exist** (program-specific; new). Every machine of every history of the shop
admits a stage assignment that fits its observation.

Placement. Concept `store-typing`, requirement R4. Question: the scenario clauses `counted` and
`committed`, whose step this is. Consumers: `Atomic.counted`, `Atomic.committed`; with a
`cleaned` stage per request it also serves `cleans_once` (R11, another seat's). Reach: the
built shop, every compile budget, every control history. Not established: that a request
decides (progress), anything of a lowered run. Route (`README.md`, section S2): the shop's
per-fiber positions, by the fiber-local residual law (G2), and one check per write site and per
interruption. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal shop_stages (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (compileFuel : Nat) :
    ∀ m, ControlHistory b compileFuel m → ∃ g, StagesFit g (observeM m)

/-! ### The observation algebra (proved) -/

theorem length_filter_zip_fst {α β : Type} (p : α → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => p x.1).length = (xs.filter p).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_fst p xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases p x
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- Filters of a zip by the right component count as filters of the right list. -/
theorem length_filter_zip_snd {α β : Type} (q : β → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => q x.2).length = (ys.filter q).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_snd q xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases q y
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- A filter by a stronger test is no longer. -/
theorem length_filter_le_of_imp {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_le_of_imp p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.filter_cons]
    cases hp : p x with
    | true =>
      rw [h x List.mem_cons_self hp]
      simp only [if_true, List.length_cons]
      exact Nat.succ_le_succ ih
    | false =>
      cases q x
      · exact ih
      · simp only [if_true, List.length_cons]
        exact Nat.le_succ_of_le ih

/-- Two disjoint filters together are no longer than the list. -/
theorem length_filter_add_le {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = false) →
      (l.filter p).length + (l.filter q).length ≤ l.length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_add_le p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hp : p x with
    | true =>
      have hq := h x List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true),
        List.length_cons, List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq, List.length_cons]
        omega
      | false =>
        rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]
        omega

/-- A filter that keeps the length keeps every element. -/
theorem all_of_length_filter {γ : Type} (p : γ → Bool) :
    ∀ l : List γ, (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | x :: l, h, y, hy => by
    cases hp : p x with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons] at h
      have bound := List.length_filter_le p l
      omega
    | true =>
      rw [List.filter_cons_of_pos hp, List.length_cons, List.length_cons] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact all_of_length_filter p l (Nat.succ.inj h) y hy

/-- The six request numbers. -/
theorem requests_length : requests.length = 6 := rfl

theorem mem_of_mem_zip_right {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.2 ∈ ys
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem b (mem_of_mem_zip_right h)

theorem mem_of_mem_zip_left {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.1 ∈ xs
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_of_mem_zip_left h)

/-- An admitted outcome is not the rejected one. -/
theorem not_rejected_of_admitted : ∀ outcome : RequestOutcome, outcome.isAdmitted = true →
    (outcome == .rejected) = false
  | .admitted, _ => rfl
  | .failedBehind, _ => rfl
  | .pending, h => absurd h Bool.false_ne_true
  | .rejected, h => absurd h Bool.false_ne_true
  | .interrupted _, h => absurd h Bool.false_ne_true
  | .other, h => absurd h Bool.false_ne_true

/-- **`counted` from the stages** (the algebra; proved). -/
theorem counted_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o) :
    o.counted = true := by
  have lengths : o.decisions.length = requests.length := h.six
  -- the outcome tests read through the stages, at every request
  have admittedLe : (o.decisions.filter RequestOutcome.isAdmitted).length ≤ o.admitted := by
    rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hadm => ?_
    rw [(h.exits x hx).1 hadm]
    rfl
  have rejectedLe : (o.decisions.filter (· == .rejected)).length ≤ o.rejected := by
    rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hrej => ?_
    rw [(h.exits x hx).2 (beq_iff_eq.mp hrej)]
    rfl
  have sumLe : o.admitted + o.rejected ≤ 6 := by
    rw [h.admitted, h.rejected]
    refine length_filter_add_le _ _ requests fun id _ hc => ?_
    cases hg : g id <;> rw [hg] at hc
    · cases hc
    · rfl
    · rfl
    · cases hc
  have lengthLe : o.deposits.length ≤ o.admitted := by
    rw [h.length, h.admitted]
    refine length_filter_le_of_imp _ _ requests fun id _ hd => ?_
    rw [of_decide_eq_true hd]
    rfl
  have perRequest : ((o.decisions.zip requests).all fun (outcome, id) =>
      if outcome.isAdmitted then o.deposits.count id == 1
      else if outcome == .rejected then o.deposits.count id == 0
      else decide (o.deposits.count id ≤ 1)) = true := by
    refine List.all_eq_true.mpr fun x hx => ?_
    obtain ⟨outcome, id⟩ := x
    dsimp only
    have hid : id ∈ requests := mem_of_mem_zip_right hx
    have hcount := h.deposit id hid
    obtain ⟨hadm, hrej⟩ := h.exits (outcome, id) hx
    cases hA : outcome.isAdmitted with
    | true =>
      rw [hcount, hadm hA]
      rfl
    | false =>
      cases hR : outcome == .rejected with
      | true =>
        have hg : g id = .rejected := hrej (beq_iff_eq.mp hR)
        rw [hcount, hg]
        rfl
      | false =>
        show decide (o.deposits.count id ≤ 1) = true
        rw [hcount]
        cases g id <;> rfl
  have complete : (o.completed != 6 ||
      (o.admitted == (o.decisions.filter RequestOutcome.isAdmitted).length &&
        o.rejected == (o.decisions.filter (· == .rejected)).length &&
        o.deposits.length == o.admitted)) = true := by
    cases hne : (o.completed != 6) with
    | true => rfl
    | false =>
      have hsix : o.completed = 6 := bne_eq_false_iff_eq.mp hne
      have every : ∀ x ∈ o.decisions, (x.isAdmitted || x == .rejected) = true := by
        refine all_of_length_filter _ o.decisions ?_
        rw [← h.completed, hsix, h.six]
      -- at a completed request, each outcome test is a stage test
      have stage : ∀ x ∈ o.decisions.zip requests,
          x.1.isAdmitted = (g x.2).counts ∧ (x.1 == .rejected) = decide (g x.2 = .rejected) ∧
            decide (g x.2 = .deposited) = (g x.2).counts := by
        intro x hx
        have hor := every x.1 (mem_of_mem_zip_left hx)
        obtain ⟨hadm, hrej⟩ := h.exits x hx
        cases hA : x.1.isAdmitted with
        | true =>
          rw [hadm hA, not_rejected_of_admitted x.1 hA]
          exact ⟨rfl, rfl, rfl⟩
        | false =>
          rw [hA, Bool.false_or] at hor
          rw [hrej (beq_iff_eq.mp hor), hor]
          exact ⟨rfl, rfl, rfl⟩
      have admittedEq : o.admitted = (o.decisions.filter RequestOutcome.isAdmitted).length := by
        rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).1.symm)
      have rejectedEq : o.rejected = (o.decisions.filter (· == .rejected)).length := by
        rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.1.symm)
      have depositsEq : o.deposits.length = o.admitted := by
        rw [h.length, h.admitted, ← length_filter_zip_snd (fun id => decide (g id = .deposited)) _ _
          lengths, ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.2)
      rw [Bool.false_or, beq_iff_eq.mpr admittedEq, beq_iff_eq.mpr rejectedEq,
        beq_iff_eq.mpr depositsEq]
      rfl
  unfold Observation.counted
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨perRequest, admittedLe⟩, rejectedLe⟩, sumLe⟩, lengthLe⟩, h.owned⟩, complete⟩

/-- **`committed` from the stages** (the algebra; proved). -/
theorem committed_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o)
    (hfail : o.decisions[1]? = some .failedBehind) : o.committed = true := by
  have hzip : ((RequestOutcome.failedBehind, 2) : RequestOutcome × Nat) ∈
      o.decisions.zip requests := by
    apply List.mem_of_getElem? (i := 1)
    rw [List.getElem?_zip_eq_some]
    exact ⟨hfail, rfl⟩
  have hg : g 2 = .deposited := (h.exits _ hzip).1 rfl
  have hcount : o.deposits.count 2 = 1 := by
    rw [h.deposit 2 (by decide), hg]
    rfl
  have hadm : 1 ≤ o.admitted := by
    rw [h.admitted]
    exact List.length_pos_of_mem (a := 2) (List.mem_filter.mpr ⟨by decide, by rw [hg]; rfl⟩)
  show ((o.deposits.count 2 == 1) && decide (1 ≤ o.admitted) &&
    (o.sawAt 2).any fun seen => decide (1 ≤ seen)) = true
  rw [hcount, decide_eq_true hadm, h.cleaned hfail]
  rfl

end Test.Dogfood.Scenario.Atomic.Store
