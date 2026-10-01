/-!
# Seat TYPES, formal pass (2026-10-01): records in a world-indexed membership judgment

Research probe, a model. It extends the data probe's record model (`SynthRecordOrder.lean`, the
data synthesis Appendix A, SHA-256 `b7bdf58b…`; its `ins`, `canon` and order lemmas are copied
verbatim below) with the two things that model did not have: a **world** (a fiber table) and a
**handle type former** whose membership arm reads a declaration. Brief item 3 asks whether row
119's design (exact records, canonical field order, positional values, records not distributed)
keeps the logical relation's laws once membership is world-indexed.

* RED CONTROL (proved, `raw_not_invariant`): with the raw order in the handle arm (the tree's
  `FiberDeclared` today), a fiber declared at a record written out of canonical order does not
  fit the normal form of its own type. Records reach TY-01 through permutation alone.
* (proved, `fitsN_normalize`) with the declaration compared in the checker's order (TY-01's
  amendment), membership is invariant under normalization, the record arm reading canonical order
  and the handle arm reading normal forms; no premise.
* (proved, `normalize_idem`) normalization is idempotent with records and handles.
* (proved, `fitsN_mono`) membership is monotone in the world.
Model only: keys are `Nat`, there are no unions, one handle former, no store. Closure under the
exact record order is the data probe's tree-model `fitsFields_exact_mono` (not rerun here).
-/
set_option autoImplicit false

namespace RecWorld

inductive T where
  | nat
  | str
  | record (fields : List (Nat × T))
  | fiber (answer : T)

inductive V where
  | nat (n : Nat)
  | str (s : String)
  | ctor (args : List V)
  | fiber (id : Nat)

/-- Copied: insert by key; an existing equal key wins. -/
def ins {α : Type} (p : Nat × α) : List (Nat × α) → List (Nat × α)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by key, the first of a repeated key kept. -/
def canon {α : Type} (xs : List (Nat × α)) : List (Nat × α) :=
  xs.foldl (fun acc p => ins p acc) []


/-- The fold, paramorphic at the handle: the fiber arm sees its argument type. -/
structure Alg (A : Type) where
  nat : A
  str : A
  record : List (Nat × A) → A
  fiber : T → A → A

mutual
def cata {A : Type} (alg : Alg A) : T → A
  | .nat => alg.nat
  | .str => alg.str
  | .record fs => alg.record (cataFields alg fs)
  | .fiber a => alg.fiber a (cata alg a)
def cataFields {A : Type} (alg : Alg A) : List (Nat × T) → List (Nat × A)
  | [] => []
  | (n, t) :: fs => (n, cata alg t) :: cataFields alg fs
end

/-- Positional fit of argument values against checkers (copied). -/
def fitPos : List V → List (Nat × (V → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

mutual
def normalize : T → T
  | .nat => .nat
  | .str => .str
  | .record fs => .record (canon (normalizeFields fs))
  | .fiber a => .fiber (normalize a)
def normalizeFields : List (Nat × T) → List (Nat × T)
  | [] => []
  | (n, t) :: fs => (n, normalize t) :: normalizeFields fs
end

/-! The raw exact order: the same keys in the same written order, fieldwise below; a fiber is
covariant. Exactly the tree's situation: an order that does not see the normal form. -/
mutual
def sub : T → T → Bool
  | .nat, .nat => true
  | .str, .str => true
  | .record fs, .record gs => subFields fs gs
  | .fiber a, .fiber b => sub a b
  | _, _ => false
def subFields : List (Nat × T) → List (Nat × T) → Bool
  | [], [] => true
  | (k, a) :: fs, (k', b) :: gs => k == k' && sub a b && subFields fs gs
  | _, _ => false
end

/-- The checker's order: compare normal forms. -/
def subN (a b : T) : Bool := sub (normalize a) (normalize b)

abbrev World := Nat → Option T

/-- Membership with the raw handle arm (the tree's `FiberDeclared` today). -/
def fitsAlgRaw (w : World) : Alg (V → Bool) where
  nat := fun v => match v with | .nat _ => true | _ => false
  str := fun v => match v with | .str _ => true | _ => false
  record := fun rs v => match v with | .ctor vs => fitPos vs (canon rs) | _ => false
  fiber := fun a _ v => match v with
    | .fiber id => match w id with | some d => sub d a | none => false
    | _ => false

/-- Membership with TY-01's amendment: the declaration compared in the checker's order. -/
def fitsAlgN (w : World) : Alg (V → Bool) where
  nat := fun v => match v with | .nat _ => true | _ => false
  str := fun v => match v with | .str _ => true | _ => false
  record := fun rs v => match v with | .ctor vs => fitPos vs (canon rs) | _ => false
  fiber := fun a _ v => match v with
    | .fiber id => match w id with | some d => subN d a | none => false
    | _ => false

def fitsRaw (w : World) (t : T) : V → Bool := cata (fitsAlgRaw w) t
def fitsN (w : World) (t : T) : V → Bool := cata (fitsAlgN w) t

/-! ## The red control -/

/-- A fiber declared at a record written out of canonical order. -/
def declared : T := .record [(2, .nat), (1, .str)]

def w0 : World := fun id => if id = 0 then some declared else none

theorem raw_fits_declared : fitsRaw w0 (.fiber declared) (.fiber 0) = true := by decide

/-- **Red control (proved).** The raw handle arm is not invariant under normalization: a
permuted record inside a handle type is enough. -/
theorem raw_not_invariant :
    fitsRaw w0 (normalize (.fiber declared)) (.fiber 0) ≠ fitsRaw w0 (.fiber declared) (.fiber 0) := by
  decide

theorem amended_fits_normal : fitsN w0 (normalize (.fiber declared)) (.fiber 0) = true := by decide

/-! ## The nested eliminator (extended with the handle) -/

theorem T.ind' {motive : T → Prop} (nat : motive .nat) (str : motive .str)
    (record : ∀ fs, (∀ p ∈ fs, motive p.2) → motive (.record fs))
    (fiber : ∀ a, motive a → motive (.fiber a)) : ∀ t, motive t :=
  fun t =>
    T.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
      (motive_3 := fun p => motive p.2)
      nat str record fiber
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (fun _ _ ih => ih)
      t

/-! ## Order lemmas over `Nat` keys (copied verbatim) -/

def Sorted {α : Type} (l : List (Nat × α)) : Prop := l.Pairwise (fun a b => a.1 < b.1)

theorem ins_map {α β : Type} (f : α → β) (p : Nat × α) (l : List (Nat × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : p.1 < q.1
    · simp [ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp [ins, if_neg h1, if_pos h2]
      · simp [ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (Nat × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

theorem canon_map {α β : Type} (f : α → β) (xs : List (Nat × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : Nat × α) (l : List (Nat × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : p.1 < q.1
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem ins_sorted {α : Type} (p : Nat × α) (l : List (Nat × α)) (hl : Sorted l) :
    Sorted (ins p l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ p
  | cons q qs ih =>
    have hq : ∀ y ∈ qs, q.1 < y.1 := (List.pairwise_cons.mp hl).1
    have hqs : Sorted qs := (List.pairwise_cons.mp hl).2
    by_cases h1 : p.1 < q.1
    · simp only [ins, if_pos h1]
      refine List.pairwise_cons.mpr ⟨?_, hl⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · rw [hy]; exact h1
      · exact Nat.lt_trans h1 (hq y hy)
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2]
        exact hl
      · simp only [ins, if_neg h1, if_neg h2]
        refine List.pairwise_cons.mpr ⟨?_, ih hqs⟩
        intro y hy
        rcases mem_ins p y qs hy with hy | hy
        · rw [hy]; omega
        · exact hq y hy

theorem foldl_ins_sorted' {α : Type} (xs acc : List (Nat × α)) (h : Sorted acc) :
    Sorted (xs.foldl (fun a p => ins p a) acc) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih (ins x acc) (ins_sorted x acc h)

theorem canon_sorted {α : Type} (xs : List (Nat × α)) : Sorted (canon xs) :=
  foldl_ins_sorted' xs [] List.Pairwise.nil

theorem ins_last {α : Type} (p : Nat × α) (l : List (Nat × α)) (h : ∀ q ∈ l, q.1 < p.1) :
    ins p l = l ++ [p] := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    have hq : q.1 < p.1 := h q (List.mem_cons_self ..)
    have h1 : ¬ p.1 < q.1 := by omega
    have h2 : ¬ p.1 = q.1 := by omega
    simp only [ins, if_neg h1, if_neg h2, List.cons_append]
    rw [ih (fun r hr => h r (List.mem_cons_of_mem q hr))]

theorem foldl_ins_of_sorted {α : Type} (xs acc : List (Nat × α)) (h : Sorted (acc ++ xs)) :
    xs.foldl (fun a p => ins p a) acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    have hx : ∀ q ∈ acc, q.1 < x.1 := fun q hq =>
      (List.pairwise_append.mp h).2.2 q hq x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [ins_last x acc hx]
    have h' : Sorted ((acc ++ [x]) ++ xs) := by
      rw [List.append_assoc, List.singleton_append]
      exact h
    rw [ih (acc ++ [x]) h', List.append_assoc, List.singleton_append]

theorem canon_of_sorted {α : Type} (l : List (Nat × α)) (h : Sorted l) : canon l = l :=
  foldl_ins_of_sorted l [] (by simpa only [List.nil_append] using h)

theorem canon_idem {α : Type} (xs : List (Nat × α)) : canon (canon xs) = canon xs :=
  canon_of_sorted (canon xs) (canon_sorted xs)


theorem cataFields_eq_map {A : Type} (alg : Alg A) (fs : List (Nat × T)) :
    cataFields alg fs = fs.map (fun p => (p.1, cata alg p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [cataFields, List.map_cons, ih]

theorem normalizeFields_eq_map (fs : List (Nat × T)) :
    normalizeFields fs = fs.map (fun p => (p.1, normalize p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [normalizeFields, List.map_cons, ih]

/-! ## Idempotence -/

theorem normalize_idem : ∀ t : T, normalize (normalize t) = normalize t := by
  intro t
  induction t using T.ind' with
  | nat => rfl
  | str => rfl
  | record fs ih =>
    have hmap : (normalizeFields fs).map (fun p => (p.1, normalize p.2)) = normalizeFields fs := by
      rw [normalizeFields_eq_map, List.map_map]
      exact List.map_congr_left (fun p hp => by
        simp only [Function.comp_apply]
        exact congrArg (fun c => (p.1, c)) (ih p hp))
    show T.record (canon (normalizeFields (canon (normalizeFields fs)))) =
      T.record (canon (normalizeFields fs))
    rw [normalizeFields_eq_map (canon (normalizeFields fs)),
      ← canon_map normalize (normalizeFields fs), canon_idem, hmap]
  | fiber a ih =>
    show T.fiber (normalize (normalize a)) = T.fiber (normalize a)
    rw [ih]

theorem subN_normalize_right (d a : T) : subN d (normalize a) = subN d a := by
  unfold subN
  rw [normalize_idem]

/-! ## The law with the amendment: invariance under normalization, no premise -/

theorem record_congr (w : World) (rs1 rs2 : List (Nat × (V → Bool))) (h : canon rs1 = canon rs2) :
    (fitsAlgN w).record rs1 = (fitsAlgN w).record rs2 := by
  funext v
  cases v with
  | nat n => rfl
  | str s => rfl
  | ctor vs =>
    show fitPos vs (canon rs1) = fitPos vs (canon rs2)
    rw [h]
  | fiber id => rfl

theorem fitsN_normalize (w : World) : ∀ t : T, fitsN w (normalize t) = fitsN w t := by
  intro t
  induction t using T.ind' with
  | nat => rfl
  | str => rfl
  | record fs ih =>
    have hmap : (normalizeFields fs).map (fun p => (p.1, cata (fitsAlgN w) p.2)) =
        fs.map (fun p => (p.1, cata (fitsAlgN w) p.2)) := by
      rw [normalizeFields_eq_map, List.map_map]
      exact List.map_congr_left (fun p hp => by
        simp only [Function.comp_apply]
        exact congrArg (fun c => (p.1, c)) (ih p hp))
    have key : canon ((canon (normalizeFields fs)).map (fun p => (p.1, cata (fitsAlgN w) p.2))) =
        canon (fs.map (fun p => (p.1, cata (fitsAlgN w) p.2))) := by
      rw [← canon_map (cata (fitsAlgN w)) (normalizeFields fs), canon_idem, hmap]
    simp only [fitsN, normalize, cata]
    rw [cataFields_eq_map, cataFields_eq_map]
    exact record_congr w _ _ key
  | fiber a _ =>
    funext v
    cases v with
    | nat n => rfl
    | str s => rfl
    | ctor vs => rfl
    | fiber id =>
      show (match w id with | some d => subN d (normalize a) | none => false) =
        (match w id with | some d => subN d a | none => false)
      cases w id with
      | none => rfl
      | some d => exact subN_normalize_right d a

/-! ## Monotone in the world -/

def WorldLe (w w' : World) : Prop := ∀ id d, w id = some d → w' id = some d

theorem mem_canon {α : Type} (x : Nat × α) (xs : List (Nat × α)) (h : x ∈ canon xs) : x ∈ xs := by
  have gen : ∀ (ys acc : List (Nat × α)), x ∈ ys.foldl (fun a p => ins p a) acc → x ∈ acc ∨ x ∈ ys := by
    intro ys
    induction ys with
    | nil => intro acc h; exact Or.inl h
    | cons y ys ih =>
      intro acc h
      rcases ih (ins y acc) h with h' | h'
      · rcases mem_ins y x acc h' with h'' | h''
        · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
        · exact Or.inl h''
      · exact Or.inr (List.mem_cons.mpr (Or.inr h'))
  rcases gen xs [] h with h' | h'
  · cases h'
  · exact h'

theorem fitPos_mono (c c' : T → V → Bool) :
    ∀ (ps : List (Nat × T)) (vs : List V), (∀ p ∈ ps, ∀ v, c p.2 v = true → c' p.2 v = true) →
      fitPos vs (ps.map (fun p => (p.1, c p.2))) = true →
      fitPos vs (ps.map (fun p => (p.1, c' p.2))) = true := by
  intro ps
  induction ps with
  | nil =>
    intro vs _ h
    exact h
  | cons p ps ih =>
    intro vs hc h
    cases vs with
    | nil => exact absurd h (by simp only [List.map_cons, fitPos, Bool.false_eq_true, not_false_eq_true])
    | cons v vs =>
      simp only [List.map_cons, fitPos, Bool.and_eq_true] at h ⊢
      exact ⟨hc p (List.mem_cons_self ..) v h.1,
        ih vs (fun q hq => hc q (List.mem_cons_of_mem p hq)) h.2⟩

theorem fitsN_mono (w w' : World) (hle : WorldLe w w') :
    ∀ (t : T) (v : V), fitsN w t v = true → fitsN w' t v = true := by
  intro t
  induction t using T.ind' with
  | nat => intro v h; exact h
  | str => intro v h; exact h
  | record fs ih =>
    intro v h
    cases v with
    | nat n => exact h
    | str s => exact h
    | fiber id => exact h
    | ctor vs =>
      simp only [fitsN, cata] at h ⊢
      rw [cataFields_eq_map] at h ⊢
      change fitPos vs (canon (fs.map (fun p => (p.1, cata (fitsAlgN w) p.2)))) = true at h
      change fitPos vs (canon (fs.map (fun p => (p.1, cata (fitsAlgN w') p.2)))) = true
      rw [canon_map] at h ⊢
      exact fitPos_mono (cata (fitsAlgN w)) (cata (fitsAlgN w')) (canon fs) vs
        (fun p hp v' hv => ih p (mem_canon p fs hp) v' hv) h
  | fiber a _ =>
    intro v h
    cases v with
    | nat n => exact h
    | str s => exact h
    | ctor vs => exact h
    | fiber id =>
      change (match w id with | some d => subN d a | none => false) = true at h
      change (match w' id with | some d => subN d a | none => false) = true
      cases hw : w id with
      | none => rw [hw] at h; exact Bool.noConfusion h
      | some d =>
        rw [hw] at h
        rw [hle id d hw]
        exact h

end RecWorld

#print axioms RecWorld.raw_fits_declared
#print axioms RecWorld.raw_not_invariant
#print axioms RecWorld.amended_fits_normal
#print axioms RecWorld.normalize_idem
#print axioms RecWorld.fitsN_normalize
#print axioms RecWorld.fitsN_mono
