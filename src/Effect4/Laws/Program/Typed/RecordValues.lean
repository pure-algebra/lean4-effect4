import Effect4.Program.Typed
import Effect4.Laws.Machine.TermHandles

/-!
# Named record value helpers

Concept: Store Typing & Value Membership (`docs/core/semantics.md`).
Role: helpers for registry claim `denote-typed`, through `evalTerm_progress`
(`Laws/Program/Typed/Denotation.lean`). Slice 2's required read and overwrite consume these facts.

Reach: the existing `NamedFit` judgment over the names and values of row 165's record frame.
No world premise is needed because the field predicates retain their own membership premises.
Rows 178 and 195 do not change the meaning of `NamedFit`.

Limits: column length equality does not imply unique or sorted names. A required field's fitting
pair does not identify a first-match lookup without the declaration's unique-name premise.
These helpers establish no program termination, scheduling service, or host execution fact.

Consumer: typed record reads and overwrite on the M5 path. Requirement: R3 (data).
The full operation contract is `docs/research/2026-10-03-data-language/record-contract.md`.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine

/-- The two columns of a fitting record have equal lengths. The record lookup and overwrite
proofs use this before reading or rebuilding paired columns (claim `denote-typed`, R3). -/
theorem namedFit_lengths :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ns.length = xs.length
  | [], [], [], _ => rfl
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | (_n, _o, _P) :: _ps, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, v :: _, [], h => by cases v <;> exact h.elim
  | (n, o, P) :: ps, v :: ns, x :: xs, h => by
    cases v with
    | str m =>
      simp only [NamedFit] at h
      by_cases hm : m = n
      · rw [if_pos hm] at h
        exact congrArg Nat.succ (namedFit_lengths ps ns xs h.2)
      · rw [if_neg hm] at h
        exact namedFit_lengths ps (.str m :: ns) (x :: xs) h.2
    | _ => exact h.elim

/-- A required declaration has a fitting value at its own name in the paired columns.
Required-read progress consumes this witness with canonical unique names
(claim `denote-typed`, rows 165, 178 and 195, R3). -/
theorem namedFit_required_pair :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ∀ q ∈ ps, q.2.1 = false →
        ∃ x, (Val.str q.1, x) ∈ ns.zip xs ∧ q.2.2 x
  | [], _, _, _ => fun _ hq => absurd hq List.not_mem_nil
  | (n, o, P) :: ps, ns, xs, h => by
    intro q hq hrequired
    match ns, xs, h with
    | [], [], h =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Bool.noConfusion (hrequired.symm.trans h.1)
      · exact namedFit_required_pair ps [] [] h.2 q hq hrequired
    | [], _ :: _, h => exact h.elim
    | v :: _, [], h => cases v <;> exact h.elim
    | v :: ns, x :: xs, h =>
      cases v with
      | str m =>
        simp only [NamedFit] at h
        by_cases hm : m = n
        · rw [if_pos hm] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · refine ⟨x, ?_, h.1⟩
            rw [hm]
            exact List.mem_cons_self
          · obtain ⟨y, hy, hfit⟩ := namedFit_required_pair ps ns xs h.2 q hq hrequired
            exact ⟨y, List.mem_cons_of_mem _ hy, hfit⟩
        · rw [if_neg hm] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Bool.noConfusion (hrequired.symm.trans h.1)
          · exact namedFit_required_pair ps (.str m :: ns) (x :: xs) h.2 q hq hrequired
      | _ => exact h.elim

/-- A fitting frame's columns arise from paired string names and values.
This helper supplies the checked frame consumed by record lookup. -/
theorem namedFit_columns :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      NamedFit ps ns xs → ∃ es : List (String × Val),
        ns = es.map (fun e => .str e.1) ∧ xs = es.map Prod.snd
  | [], [], [], _ => ⟨[], rfl, rfl⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], [], _ => ⟨[], rfl, rfl⟩
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, v :: _, [], h => by cases v <;> exact h.elim
  | (n, o, P) :: ps, v :: ns, x :: xs, h => by
    cases v with
    | str m =>
      simp only [NamedFit] at h
      by_cases hm : m = n
      · rw [if_pos hm] at h
        obtain ⟨es, rfl, rfl⟩ := namedFit_columns ps ns xs h.2
        exact ⟨(m, x) :: es, rfl, rfl⟩
      · rw [if_neg hm] at h
        exact namedFit_columns ps (.str m :: ns) (x :: xs) h.2
    | _ => exact h.elim


/-- Present names form a subsequence of the declared names.
Canonical declarations therefore give distinct present names to lookup. -/
theorem namedFit_names_sublist :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd) →
        List.Sublist (es.map Prod.fst) (ps.map Prod.fst)
  | [], [], _ => .slnil
  | [], _ :: _, h => h.elim
  | _ :: _, [], _ => List.nil_sublist _
  | (n, o, P) :: ps, (m, x) :: es, h => by
    simp only [List.map_cons, NamedFit] at h
    by_cases hm : m = n
    · rw [if_pos hm] at h
      subst m
      exact (namedFit_names_sublist ps es h.2).cons_cons n
    · rw [if_neg hm] at h
      exact (namedFit_names_sublist ps ((m, x) :: es) h.2).cons _


/-- Reading paired columns recovers every pair without truncation. -/
theorem readColumns_frame (es : List (String × Val)) :
    Record.readColumns (es.map (fun e => .str e.1)) (es.map Prod.snd) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨n, x⟩
    simp only [List.map_cons, Record.readColumns, ih, Option.map_some]


/-- Lookup returns the declared predicate when present; absence requires an optional field. -/
theorem namedFit_lookup :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      (ps.map Prod.fst).Nodup →
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd) →
      ∀ q ∈ ps, match Field.firstOf q.1 es with
        | none => q.2.1 = true
        | some value => q.2.2 value
  | [], _, _, _, q, hq => absurd hq List.not_mem_nil
  | (n, o, P) :: ps, [], hnd, hfit, q, hq => by
    have hnd' := (List.nodup_cons.mp hnd).2
    simp only [List.map_nil, NamedFit] at hfit
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hfit.1
    · exact namedFit_lookup ps [] hnd' hfit.2 q hq
  | (n, o, P) :: ps, (m, x) :: es, hnd, hfit, q, hq => by
    have hn := List.nodup_cons.mp hnd
    simp only [List.map_cons, NamedFit] at hfit
    by_cases hm : m = n
    · rw [if_pos hm] at hfit
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only [Field.firstOf, hm]
        exact hfit.1
      · have hmq : m ≠ q.1 := by
          intro heq
          have hmem : q.1 ∈ ps.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
          exact hn.1 ((heq.symm.trans hm) ▸ hmem)
        simp only [Field.firstOf, if_neg hmq]
        exact namedFit_lookup ps es hn.2 hfit.2 q hq
    · rw [if_neg hm] at hfit
      rcases List.mem_cons.mp hq with rfl | hq
      · have hsub := namedFit_names_sublist ps ((m, x) :: es) hfit.2
        have absent : Field.firstOf n ((m, x) :: es) = none :=
          Field.firstOf_eq_none (fun p hp he => hn.1
            (he ▸ hsub.subset (List.mem_map.mpr ⟨p, hp, rfl⟩)))
        rw [absent]
        exact hfit.1
      · exact namedFit_lookup ps ((m, x) :: es) hn.2 hfit.2 q hq


/-- Sorted names included in sorted declarations form a subsequence.
Construction uses this fact after sorting paired arguments. -/
theorem ascending_names_sublist {α β : Type} :
    ∀ (ps : List (String × α)) (es : List (String × β)),
      Field.Ascending Field.bytesKey ps → Field.Ascending Field.bytesKey es →
      (es.map Prod.fst ⊆ ps.map Prod.fst) → List.Sublist (es.map Prod.fst) (ps.map Prod.fst)
  | [], [], _, _, _ => .slnil
  | [], e :: es, _, _, hsubset =>
    absurd (hsubset (List.mem_cons_self : e.1 ∈ e.1 :: es.map Prod.fst)) List.not_mem_nil
  | _ :: _, [], _, _, _ => List.nil_sublist _
  | p :: ps, e :: es, hp, he, hsubset => by
    have hp' := List.pairwise_cons.mp hp
    have he' := List.pairwise_cons.mp he
    by_cases heq : e.1 = p.1
    · have htail : es.map Prod.fst ⊆ ps.map Prod.fst := by
        intro n hn
        have hn' := hsubset (List.mem_cons_of_mem e.1 hn)
        rcases List.mem_cons.mp hn' with hn' | hn'
        · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hn
          have hlt := he'.1 q hq
          rw [hqn, hn', heq, Field.ltKey_irrefl] at hlt
          exact Bool.noConfusion hlt
        · exact hn'
      have ih := ascending_names_sublist ps es hp'.2 he'.2 htail
      simpa only [List.map_cons, heq] using ih.cons_cons p.1
    · have heMem : e.1 ∈ ps.map Prod.fst := by
        rcases List.mem_cons.mp (hsubset List.mem_cons_self) with h | h
        · exact (heq h).elim
        · exact h
      have hpAbsent : p.1 ∉ (e :: es).map Prod.fst := by
        intro h
        rcases List.mem_cons.mp h with h | h
        · exact heq h.symm
        · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
          obtain ⟨r, hr, hre⟩ := List.mem_map.mp heMem
          have hpe := hp'.1 r hr
          have hep := he'.1 q hq
          rw [hre] at hpe
          rw [hqp, Field.ltKey_asymm hpe] at hep
          exact Bool.noConfusion hep
      have htail : (e :: es).map Prod.fst ⊆ ps.map Prod.fst := by
        intro n hn
        rcases List.mem_cons.mp (hsubset hn) with hn' | hn'
        · exact (hpAbsent (hn' ▸ hn)).elim
        · exact hn'
      exact (ascending_names_sublist ps (e :: es) hp'.2 he htail).cons p.1


/-- An ordered frame with each declared lookup admitted satisfies `NamedFit`.
Construction and overwrite use this converse to the lookup bridge. -/
theorem namedFit_of_sublist_lookup :
    ∀ (ps : List (String × Bool × (Val → Prop))) (es : List (String × Val)),
      (ps.map Prod.fst).Nodup → List.Sublist (es.map Prod.fst) (ps.map Prod.fst) →
      (∀ q ∈ ps, match Field.firstOf q.1 es with
        | none => q.2.1 = true
        | some value => q.2.2 value) →
      NamedFit ps (es.map (fun e => .str e.1)) (es.map Prod.snd)
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, hsub, _ => by cases hsub
  | (n, o, P) :: ps, [], hnd, _, hall => by
    exact ⟨hall _ List.mem_cons_self,
      namedFit_of_sublist_lookup ps [] (List.nodup_cons.mp hnd).2 (List.nil_sublist _)
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))⟩
  | (n, o, P) :: ps, (m, x) :: es, hnd, hsub, hall => by
    have hn := List.nodup_cons.mp hnd
    by_cases hm : m = n
    · have hhead := hall (n, o, P) List.mem_cons_self
      simp only [Field.firstOf, if_pos hm] at hhead
      have htail : ∀ q ∈ ps, match Field.firstOf q.1 es with
          | none => q.2.1 = true
          | some value => q.2.2 value := by
        intro q hq
        have hmq : m ≠ q.1 := by
          intro heq
          have hmem : q.1 ∈ ps.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
          exact hn.1 ((heq.symm.trans hm) ▸ hmem)
        have h := hall q (List.mem_cons_of_mem _ hq)
        simpa only [Field.firstOf, if_neg hmq] using h
      simp only [List.map_cons, NamedFit, if_pos hm]
      exact ⟨hhead, namedFit_of_sublist_lookup ps es hn.2 hsub.of_cons_cons htail⟩
    · have hsub' : List.Sublist (((m, x) :: es).map Prod.fst) (ps.map Prod.fst) := by
        rcases List.sublist_cons_iff.mp hsub with h | ⟨r, heq, _⟩
        · exact h
        · exact (hm (List.cons.inj heq).1).elim
      have hnone : Field.firstOf n ((m, x) :: es) = none :=
        Field.firstOf_eq_none (fun p hp he => hn.1
          (he ▸ hsub'.subset (List.mem_map.mpr ⟨p, hp, rfl⟩)))
      have hhead := hall (n, o, P) List.mem_cons_self
      rw [hnone] at hhead
      simp only [List.map_cons, NamedFit, if_neg hm]
      exact ⟨hhead, namedFit_of_sublist_lookup ps ((m, x) :: es) hn.2 hsub'
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))⟩


/-- A successful branchwise check gives a result for each input branch. -/
theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | a :: xs, _, h, x, hx => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hxy⟩ := mapM_some_mem hbs x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩


/-- Removing one different name leaves a lookup unchanged. Overwrite uses this field-list law. -/
theorem firstOf_filter_other {α : Type} (removed name : String) (hne : removed ≠ name)
    (fields : List (String × α)) :
    Field.firstOf name (fields.filter (fun q => decide (q.1 ≠ removed))) =
      Field.firstOf name fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    by_cases hp : field.1 ≠ removed
    · simp only [List.filter_cons, decide_eq_true_eq, if_pos hp, Field.firstOf]
      rw [ih]
    · have heq : field.1 = removed := Decidable.of_not_not hp
      simp only [List.filter_cons, decide_eq_true_eq]
      rw [if_neg hp]
      simp only [Field.firstOf, heq, if_neg hne, ih]

/-- The named read: the proposition implies the check. -/
theorem namedFit_hasTy :
    ∀ (ps : List (String × Bool × (Val → Prop))) (cs : List (String × Bool × (Val → Bool)))
      (ns xs : List Val),
      ps.map (fun p => (p.1, p.2.1)) = cs.map (fun p => (p.1, p.2.1)) →
      (∀ pc ∈ ps.zip cs, ∀ x, pc.1.2.2 x → pc.2.2.2 x = true) →
      NamedFit ps ns xs → namedHasTy cs ns xs = true
  | [], [], [], [], _, _, _ => rfl
  | [], [], [], _ :: _, _, _, h => h.elim
  | [], [], _ :: _, _, _, _, h => h.elim
  | [], _ :: _, _, _, hh, _, _ => nomatch hh
  | _ :: _, [], _, _, hh, _, _ => nomatch hh
  | (n, o, P) :: ps, (m, p, c) :: cs, ns, xs, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
    obtain ⟨⟨rfl, rfl⟩, hrest⟩ := hh
    have hc : ∀ x, P x → c x = true := hpt ((n, o, P), (n, o, c)) List.mem_cons_self
    have hpt' : ∀ q ∈ ps.zip cs, ∀ x, q.1.2.2 x → q.2.2.2 x = true :=
      fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    match ns, xs, h with
    | [], [], h =>
      simp only [NamedFit] at h
      simp only [namedHasTy, Bool.and_eq_true]
      exact ⟨h.1, namedFit_hasTy ps cs [] [] hrest hpt' h.2⟩
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [NamedFit] at h
        simp only [namedHasTy]
        by_cases hk : k = n
        · rw [if_pos hk] at h
          rw [if_pos hk, Bool.and_eq_true]
          exact ⟨hc x h.1, namedFit_hasTy ps cs ns xs hrest hpt' h.2⟩
        · rw [if_neg hk] at h
          rw [if_neg hk, Bool.and_eq_true]
          exact ⟨h.1, namedFit_hasTy ps cs (.str k :: ns) (x :: xs) hrest hpt' h.2⟩
      | _ => exact h.elim


/-- The named read from the check: where each field's check implies its predicate, the Boolean
read implies the proposition (`namedFit_hasTy`'s converse). -/
theorem namedFit_of_namedHasTy {β : Type} (P : β → Val → Prop) (c : β → Val → Bool) :
    ∀ (l : List (String × Bool × β)) (ns xs : List Val),
      (∀ q ∈ l, ∀ x, c q.2.2 x = true → P q.2.2 x) →
      namedHasTy (l.map fun q => (q.1, q.2.1, c q.2.2)) ns xs = true →
      NamedFit (l.map fun q => (q.1, q.2.1, P q.2.2)) ns xs
  | [], ns, xs, _, h => by
    match ns, xs, h with
    | [], [], _ => trivial
    | [], _ :: _, h => exact Bool.noConfusion h
    | _ :: _, _, h => exact Bool.noConfusion h
  | (n, o, t) :: l, ns, xs, hpt, h => by
    have hl : ∀ q ∈ l, ∀ x, c q.2.2 x = true → P q.2.2 x :=
      fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    have ht : ∀ x, c t x = true → P t x := hpt (n, o, t) List.mem_cons_self
    match ns, xs, h with
    | [], [], h =>
      simp only [List.map_cons, namedHasTy, Bool.and_eq_true] at h
      exact ⟨h.1, namedFit_of_namedHasTy P c l [] [] hl h.2⟩
    | [], _ :: _, h => exact Bool.noConfusion h
    | v0 :: _, [], h => cases v0 <;> exact Bool.noConfusion h
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [List.map_cons, namedHasTy] at h
        simp only [List.map_cons, NamedFit]
        by_cases hk : k = n
        · rw [if_pos hk, Bool.and_eq_true] at h
          rw [if_pos hk]
          exact ⟨ht x h.1, namedFit_of_namedHasTy P c l ns xs hl h.2⟩
        · rw [if_neg hk, Bool.and_eq_true] at h
          rw [if_neg hk]
          exact ⟨h.1, namedFit_of_namedHasTy P c l (.str k :: ns) (x :: xs) hl h.2⟩
      | _ => exact Bool.noConfusion h

/-- The generic named proposition states exactly the Boolean field checks.
Legacy term typing and world membership share this frame connection. -/
theorem namedFit_check_iff (cs : List (String × Bool × (Val → Bool))) (ns xs : List Val) :
    NamedFit (cs.map (fun q => (q.1, q.2.1, fun x => q.2.2 x = true))) ns xs ↔
      namedHasTy cs ns xs = true := by
  induction cs generalizing ns xs with
  | nil =>
    cases ns <;> cases xs <;> simp only [List.map_nil, NamedFit, namedHasTy, Bool.false_eq_true]
  | cons q cs ih =>
    obtain ⟨n, o, c⟩ := q
    match ns, xs with
    | [], [] => simp only [List.map_cons, NamedFit, namedHasTy, Bool.and_eq_true, ih]
    | [], _ :: _ => simp only [List.map_cons, NamedFit, namedHasTy, Bool.false_eq_true]
    | value :: _, [] =>
      cases value <;> simp only [List.map_cons, NamedFit, namedHasTy, Bool.false_eq_true]
    | value :: ns, x :: xs =>
      cases value with
      | str m =>
        by_cases h : m = n
        · simp only [List.map_cons, NamedFit, namedHasTy, if_pos h, Bool.and_eq_true, ih]
        · simp only [List.map_cons, NamedFit, namedHasTy, if_neg h, Bool.and_eq_true, ih]
      | _ => simp only [List.map_cons, NamedFit, namedHasTy, Bool.false_eq_true]

end Effect4.Program.Typed
