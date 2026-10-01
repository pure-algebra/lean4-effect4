import Effect4.Machine.Term
import Effect4.Program.Ty

/-!
# Seat R, question 1, under an amended value clause: record values that carry their names

Type-language probe, 2026-10-01. A model, not the tree. The same model as `Q1Positional.lean`
(the same names, canonical order, literal rule, typer and evaluator shapes) with one change, the
record value: `ctor 0 [list names, list values]`, names and values in canonical field order, in
the carrier's existing frames (`ctor`, `list`, `str`; no new `Val` constructor). Membership stays
exact (the names must be exactly the type's canonical names) and stays a fold.

What it shows:
1. route (b) with a name-only projection, `field (target : Term) (name : String)`, has progress
   and preservation with an untyped evaluator (`sound`, `termFits`): the evaluator finds the
   name in the value;
2. route (a) becomes sound too (`recordGet_sound`): the atom's evaluator sees the names;
3. the union that `Q1Positional.union_value_ambiguous` breaks is unambiguous here
   (`union_values_distinct`): rc.112's two objects lay out to two values.
-/

set_option autoImplicit false

namespace SeatR.Named

open Effect4.Machine
open Effect4.Program (Lit)

/-! ## 1. Names, their order, the canonical field list -/

/-- The UTF-8 byte order on names: the key order `Ty.key` uses for a `lit` (`Ty.lean:155-176`). -/
def nameLt (a b : String) : Bool :=
  Effect4.Program.Ty.ltKey (Effect4.Program.Ty.key (.lit a)) (Effect4.Program.Ty.key (.lit b))

/-- Insert by name; an equal name already present wins, so a left fold keeps the first. -/
def ins {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by name, the first of a repeated name kept. -/
def canon {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => ins p acc) []

theorem ins_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, ins, if_neg h1, if_pos h2]
      · simp only [List.map_cons, ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

/-- The canonicaliser is payload-polymorphic: it commutes with any map of the payloads. -/
theorem canon_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : String × α) (l : List (String × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
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

theorem mem_foldl_ins {α : Type} (x : String × α) (xs acc : List (String × α))
    (h : x ∈ xs.foldl (fun a p => ins p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    simp only [List.foldl_cons] at h
    rcases ih (ins y acc) h with h' | h'
    · rcases mem_ins y x acc h' with h'' | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Every field of the canonical list is a field of the input. -/
theorem mem_canon {α : Type} (x : String × α) (xs : List (String × α)) (h : x ∈ canon xs) :
    x ∈ xs := by
  rcases mem_foldl_ins x xs [] h with h' | h'
  · cases h'
  · exact h'

/-- The value of a name in a field list, first match. -/
def lookupName {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookupName n rest

/-! ## 2. The model type language and membership: names in the value -/

inductive MTy where
  | unit
  | nat
  | string
  | bool
  | lit (s : String)
  | prod (a b : MTy)
  | union (a b : MTy)
  | record (fields : List (String × MTy))

def fitPos : List Val → List (String × (Val → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

/-- The value's name header against canonical fields, position by position. -/
def namesFit {α : Type} : List Val → List (String × α) → Bool
  | [], [] => true
  | .str n :: ns, (m, _) :: fs => decide (n = m) && namesFit ns fs
  | _, _ => false

mutual
def hasTy : MTy → Val → Bool
  | .unit, v => match v with | .unit => true | _ => false
  | .nat, v => match v with | .nat _ => true | _ => false
  | .string, v => match v with | .str _ => true | _ => false
  | .bool, v => match v with | .bool _ => true | _ => false
  | .lit s, v => match v with | .str t => decide (t = s) | _ => false
  | .prod a b, v => match v with | .list [x, y] => hasTy a x && hasTy b y | _ => false
  | .union a b, v => hasTy a v || hasTy b v
  | .record fs, v =>
    match v with
    | .ctor 0 [.list ns, .list vs] => namesFit ns (canon fs) && fitPos vs (canon (checks fs))
    | _ => false
def checks : List (String × MTy) → List (String × (Val → Bool))
  | [] => []
  | (n, t) :: fs => (n, hasTy t) :: checks fs
end

theorem checks_eq_map (fs : List (String × MTy)) :
    checks fs = fs.map (fun p => (p.1, hasTy p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [checks, List.map_cons, ih]

theorem canon_checks (fs : List (String × MTy)) :
    canon (checks fs) = (canon fs).map (fun p => (p.1, hasTy p.2)) := by
  rw [checks_eq_map]
  exact canon_map hasTy fs

theorem hasTy_record_inv (fs : List (String × MTy)) (v : Val) (h : hasTy (.record fs) v = true) :
    ∃ ns vs, v = .ctor 0 [.list ns, .list vs] ∧ namesFit ns (canon fs) = true ∧
      fitPos vs (canon (checks fs)) = true := by
  cases v with
  | ctor k args =>
    cases k with
    | zero =>
      match args, h with
      | [.list ns, .list vs], h =>
        simp only [hasTy, Bool.and_eq_true] at h
        exact ⟨ns, vs, rfl, h.1, h.2⟩
      | [], h => simp only [hasTy, Bool.false_eq_true] at h
      | [.unit], h | [.bool _], h | [.nat _], h | [.str _], h | [.bytes _], h | [.list _], h
      | [.pair _ _], h | [.none], h | [.some _], h | [.ctor _ _], h | [.ref _ _], h
      | [.handle _ _], h => simp only [hasTy, Bool.false_eq_true] at h
      | _ :: _ :: _ :: _, h => simp only [hasTy, Bool.false_eq_true] at h
      | [.unit, _], h | [.bool _, _], h | [.nat _, _], h | [.str _, _], h | [.bytes _, _], h
      | [.pair _ _, _], h | [.none, _], h | [.some _, _], h | [.ctor _ _, _], h | [.ref _ _, _], h
      | [.handle _ _, _], h => simp only [hasTy, Bool.false_eq_true] at h
      | [.list _, .unit], h | [.list _, .bool _], h | [.list _, .nat _], h | [.list _, .str _], h
      | [.list _, .bytes _], h | [.list _, .pair _ _], h | [.list _, .none], h
      | [.list _, .some _], h | [.list _, .ctor _ _], h | [.list _, .ref _ _], h
      | [.list _, .handle _ _], h => simp only [hasTy, Bool.false_eq_true] at h
    | succ k => simp only [hasTy, Bool.false_eq_true] at h
  | _ => simp only [hasTy, Bool.false_eq_true] at h

theorem fitPos_get (fs : List (String × MTy)) (vs : List Val) (i : Nat) (m : String) (τ : MTy)
    (hfit : fitPos vs (fs.map (fun p => (p.1, hasTy p.2))) = true)
    (hi : fs[i]? = some (m, τ)) : ∃ w, vs[i]? = some w ∧ hasTy τ w = true := by
  induction fs generalizing vs i with
  | nil => simp only [List.getElem?_nil, reduceCtorEq] at hi
  | cons p fs ih =>
    cases vs with
    | nil => simp only [List.map_cons, fitPos, Bool.false_eq_true] at hfit
    | cons v vs =>
      simp only [List.map_cons, fitPos, Bool.and_eq_true] at hfit
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨v, rfl, hfit.1⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi ⊢
        exact ih vs i hfit.2 hi

theorem fitPos_map_map {β : Type} (M : List (String × β)) (g : β → Val) (c : β → Val → Bool) :
    fitPos (M.map (fun p => g p.2)) (M.map (fun p => (p.1, c p.2))) = M.all (fun p => c p.2 (g p.2)) := by
  induction M with
  | nil => rfl
  | cons p M ih =>
    simp only [List.map_cons, fitPos, List.all_cons, ih]

/-- The first position of a name in a value's name header. -/
def idxStr (n : String) : List Val → Option Nat
  | [] => none
  | .str m :: rest => if m = n then some 0 else (idxStr n rest).map (· + 1)
  | _ :: rest => (idxStr n rest).map (· + 1)

/-- A name the canonical fields hold is found in a fitting header at the same position, and
the value there fits the field. -/
theorem lookup_found {α : Type} (n : String) (τ : α) (M : List (String × α)) (ns : List Val)
    (hns : namesFit ns M = true) (h : lookupName n M = some τ) :
    ∃ i, idxStr n ns = some i ∧ M[i]? = some (n, τ) := by
  induction M generalizing ns with
  | nil => simp only [lookupName, reduceCtorEq] at h
  | cons p M ih =>
    obtain ⟨m, a⟩ := p
    cases ns with
    | nil => simp only [namesFit, Bool.false_eq_true] at hns
    | cons x rest =>
      cases x with
      | str k =>
        simp only [namesFit, Bool.and_eq_true, decide_eq_true_eq] at hns
        obtain ⟨hk, hrest⟩ := hns
        subst hk
        simp only [lookupName] at h
        by_cases hm : k = n
        · simp only [hm, ↓reduceIte, Option.some.injEq] at h
          subst h
          subst hm
          exact ⟨0, by simp only [idxStr, ↓reduceIte], rfl⟩
        · simp only [hm, ↓reduceIte] at h
          obtain ⟨i, hi, hget⟩ := ih rest hrest h
          exact ⟨i + 1, by simp only [idxStr, hm, ↓reduceIte, hi, Option.map_some],
            by simp only [List.getElem?_cons_succ, hget]⟩
      | _ => simp only [namesFit, Bool.false_eq_true] at hns

/-- The canonical header of a field list: its names, as strings. -/
def header {α : Type} (M : List (String × α)) : List Val := M.map (fun p => .str p.1)

theorem namesFit_header {α β : Type} (M : List (String × α)) (f : α → β) :
    namesFit (header M) (M.map (fun p => (p.1, f p.2))) = true := by
  induction M with
  | nil => rfl
  | cons p M ih =>
    simp only [header, List.map_cons, namesFit, decide_true, Bool.true_and]
    exact ih

/-! ## 3. The terms: route (b), the projection by name only -/

mutual
  inductive Term
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
    | record (labels : List String) (args : Terms)
    /-- `t.name`: the name only; the value carries what the evaluator needs. -/
    | field (target : Term) (name : String)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

deriving instance DecidableEq for Term, Terms

structure Sig where
  atomOf : String → List MTy → Option MTy
  constAtom : String → Bool

def litArgTy (const : Bool) : Lit → MTy
  | .str s => if const then .lit s else .string
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool

def distinct : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinct ns

def fieldTy : MTy → String → Option MTy
  | .record fs, name => lookupName name (canon fs)
  | _, _ => none

mutual
  def argTy (sig : Sig) (env : List MTy) (const : Bool) : Term → Option MTy
    | .var index => env[index]?
    | .lit value => some (litArgTy const value)
    | .app atom args => do
      let tys ← argsTy sig env (sig.constAtom atom) args
      sig.atomOf atom tys
    | .record labels args => do
      let tys ← argsTy sig env false args
      if labels.length = tys.length ∧ distinct labels = true then
        some (.record (labels.zip tys))
      else none
    | .field target name => do
      let r ← argTy sig env false target
      fieldTy r name
  def argsTy (sig : Sig) (env : List MTy) (const : Bool) : Terms → Option (List MTy)
    | .nil => some []
    | .cons head tail => do
      let t ← argTy sig env const head
      let rest ← argsTy sig env const tail
      some (t :: rest)
end

/-- The record value of canonical (name, value) pairs. -/
def mkRecord (M : List (String × Val)) : Val := .ctor 0 [.list (header M), .list (M.map Prod.snd)]

/-- Projection by name: the name's position in the value's own header. -/
def getField (name : String) : Val → Option Val
  | .ctor 0 [.list ns, .list vs] => (idxStr name ns).bind (fun i => vs[i]?)
  | _ => none

mutual
  def evalTerm (eval : String → List Val → Option Val) (env : List Val) : Term → Option Val
    | .var index => env[index]?
    | .lit value => value.toVal
    | .app atom args => do
      let vs ← evalTerms eval env args
      eval atom vs
    | .record labels args => do
      let vs ← evalTerms eval env args
      if labels.length = vs.length then some (mkRecord (canon (labels.zip vs))) else none
    | .field target name => do
      let v ← evalTerm eval env target
      getField name v
  def evalTerms (eval : String → List Val → Option Val) (env : List Val) :
      Terms → Option (List Val)
    | .nil => some []
    | .cons head tail => do
      let v ← evalTerm eval env head
      let rest ← evalTerms eval env tail
      some (v :: rest)
end

/-! ## 4. Progress and preservation -/

def fitsL : List Val → List MTy → Bool
  | [], [] => true
  | v :: vs, t :: ts => hasTy t v && fitsL vs ts
  | _, _ => false

def AtomsSound (sig : Sig) (eval : String → List Val → Option Val) : Prop :=
  ∀ (atom : String) (tys : List MTy) (τ : MTy) (vs : List Val),
    sig.atomOf atom tys = some τ → fitsL vs tys = true →
      ∃ v, eval atom vs = some v ∧ hasTy τ v = true

def EnvTyped (Γ : List MTy) (env : List Val) : Prop :=
  Γ.length = env.length ∧
    ∀ (i : Nat) (τ : MTy) (v : Val), Γ[i]? = some τ → env[i]? = some v → hasTy τ v = true

theorem fitsL_length {vs : List Val} {tys : List MTy} (h : fitsL vs tys = true) :
    vs.length = tys.length := by
  induction vs generalizing tys with
  | nil => cases tys with
    | nil => rfl
    | cons t ts => simp only [fitsL, Bool.false_eq_true] at h
  | cons v vs ih => cases tys with
    | nil => simp only [fitsL, Bool.false_eq_true] at h
    | cons t ts =>
      simp only [fitsL, Bool.and_eq_true] at h
      simp only [List.length_cons, ih h.2]

theorem fitsL_zip {vs : List Val} {tys : List MTy} (h : fitsL vs tys = true) :
    ∀ q ∈ vs.zip tys, hasTy q.2 q.1 = true := by
  induction vs generalizing tys with
  | nil => intro q hq; simp only [List.zip_nil_left, List.not_mem_nil] at hq
  | cons v vs ih => cases tys with
    | nil => intro q hq; simp only [List.zip_nil_right, List.not_mem_nil] at hq
    | cons t ts =>
      simp only [fitsL, Bool.and_eq_true] at h
      intro q hq
      simp only [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst hq; exact h.1
      · exact ih h.2 q hq

theorem zip3_proj {β γ : Type} (ks : List String) (xs : List β) (ys : List γ)
    (h : xs.length = ys.length) :
    (ks.zip (xs.zip ys)).map (fun p => (p.1, p.2.1)) = ks.zip xs ∧
      (ks.zip (xs.zip ys)).map (fun p => (p.1, p.2.2)) = ks.zip ys := by
  induction ks generalizing xs ys with
  | nil => exact ⟨rfl, rfl⟩
  | cons k ks ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => exact ⟨rfl, rfl⟩
      | cons y ys => exact absurd h (Nat.succ_ne_zero _).symm
    | cons x xs =>
      cases ys with
      | nil => exact absurd h (Nat.succ_ne_zero _)
      | cons y ys =>
        obtain ⟨h1, h2⟩ := ih xs ys (Nat.succ.inj h)
        simp only [List.zip_cons_cons, List.map_cons, h1, h2, and_self]

/-- Construction is sound: the header is the canonical names, the values fit in that order. -/
theorem align (ks : List String) (vs : List Val) (tys : List MTy)
    (hf : fitsL vs tys = true) :
    hasTy (.record (ks.zip tys)) (mkRecord (canon (ks.zip vs))) = true := by
  obtain ⟨h1, h2⟩ := zip3_proj ks vs tys (fitsL_length hf)
  have hv : canon (ks.zip vs) = (canon (ks.zip (vs.zip tys))).map (fun q => (q.1, q.2.1)) := by
    rw [← h1]
    exact canon_map Prod.fst (ks.zip (vs.zip tys))
  have hc : canon (checks (ks.zip tys)) =
      (canon (ks.zip (vs.zip tys))).map (fun q => (q.1, hasTy q.2.2)) := by
    rw [checks_eq_map, ← h2, List.map_map]
    exact canon_map (fun x => hasTy x.2) (ks.zip (vs.zip tys))
  have hn : canon (ks.zip tys) = (canon (ks.zip (vs.zip tys))).map (fun q => (q.1, q.2.2)) := by
    rw [← h2]
    exact canon_map Prod.snd (ks.zip (vs.zip tys))
  simp only [mkRecord, hasTy, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [hv, hn, header]
    simp only [List.map_map, Function.comp_def]
    have := namesFit_header (canon (ks.zip (vs.zip tys))) Prod.snd
    simp only [header] at this
    exact this
  · rw [hv, hc, List.map_map]
    have key := fitPos_map_map (canon (ks.zip (vs.zip tys))) Prod.fst (fun x => hasTy x.2)
    simp only [Function.comp_def] at key ⊢
    rw [key, List.all_eq_true]
    intro q hq
    exact fitsL_zip hf q.2 (List.of_mem_zip (mem_canon q _ hq)).2

theorem field_sound {fs : List (String × MTy)} {v : Val} {n : String} {τ : MTy}
    (hv : hasTy (.record fs) v = true) (hl : lookupName n (canon fs) = some τ) :
    ∃ w, getField n v = some w ∧ hasTy τ w = true := by
  obtain ⟨ns, vs, rfl, hns, hfit⟩ := hasTy_record_inv fs v hv
  obtain ⟨i, hi, hget⟩ := lookup_found n τ (canon fs) ns hns hl
  rw [canon_checks] at hfit
  obtain ⟨w, hw, hτ⟩ := fitPos_get (canon fs) vs i n τ hfit hget
  exact ⟨w, by simp only [getField, hi, Option.bind_some, hw], hτ⟩

theorem lit_sound (c : Bool) (value : Lit) :
    ∃ v, value.toVal = some v ∧ hasTy (litArgTy c value) v = true := by
  cases value with
  | unit => exact ⟨_, rfl, rfl⟩
  | nat n => exact ⟨_, rfl, rfl⟩
  | bool b => exact ⟨_, rfl, rfl⟩
  | str s =>
    cases c with
    | true => exact ⟨_, rfl, by simp only [litArgTy, ↓reduceIte, hasTy, decide_true]⟩
    | false => exact ⟨_, rfl, rfl⟩

theorem var_sound {Γ : List MTy} {env : List Val} (hΓ : EnvTyped Γ env) {i : Nat} {τ : MTy}
    (h : Γ[i]? = some τ) : ∃ v, env[i]? = some v ∧ hasTy τ v = true := by
  have hi : i < Γ.length := (List.getElem?_eq_some_iff.mp h).1
  have hi' : i < env.length := hΓ.1 ▸ hi
  exact ⟨env[i], List.getElem?_eq_getElem hi', hΓ.2 i τ env[i] h (List.getElem?_eq_getElem hi')⟩

theorem fieldTy_inv {r : MTy} {n : String} {τ : MTy} (h : fieldTy r n = some τ) :
    ∃ fs, r = .record fs ∧ lookupName n (canon fs) = some τ := by
  cases r with
  | record fs => exact ⟨fs, rfl, h⟩
  | _ => simp only [fieldTy, reduceCtorEq] at h

mutual
theorem sound (sig : Sig) (eval : String → List Val → Option Val) (hA : AtomsSound sig eval)
    (Γ : List MTy) (env : List Val) (hΓ : EnvTyped Γ env) :
    ∀ (t : Term) (c : Bool) (τ : MTy), argTy sig Γ c t = some τ →
      ∃ v, evalTerm eval env t = some v ∧ hasTy τ v = true
  | .var i, c, τ, h => by
    simp only [argTy] at h
    obtain ⟨v, hv, hτ⟩ := var_sound hΓ h
    exact ⟨v, by simp only [evalTerm, hv], hτ⟩
  | .lit value, c, τ, h => by
    simp only [argTy, Option.some.injEq] at h
    subst h
    obtain ⟨v, hv, hτ⟩ := lit_sound c value
    exact ⟨v, by simp only [evalTerm, hv], hτ⟩
  | .app atom args, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨tys, htys, hatom⟩ := h
    obtain ⟨vs, hvs, hfit⟩ := soundArgs sig eval hA Γ env hΓ args (sig.constAtom atom) tys htys
    obtain ⟨v, hv, hτ⟩ := hA atom tys τ vs hatom hfit
    exact ⟨v, by simp only [evalTerm, hvs, Option.bind_eq_bind, Option.bind_some, hv], hτ⟩
  | .record labels args, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨tys, htys, hrec⟩ := h
    split at hrec
    · rename_i hcond
      simp only [Option.some.injEq] at hrec
      subst hrec
      obtain ⟨vs, hvs, hfit⟩ := soundArgs sig eval hA Γ env hΓ args false tys htys
      have hlen : labels.length = vs.length := by rw [fitsL_length hfit]; exact hcond.1
      refine ⟨mkRecord (canon (labels.zip vs)), ?_, align labels vs tys hfit⟩
      simp only [evalTerm, hvs, Option.bind_eq_bind, Option.bind_some, hlen, ↓reduceIte]
    · exact nomatch hrec
  | .field target n, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hfield⟩ := h
    obtain ⟨fs, rfl, hl⟩ := fieldTy_inv hfield
    obtain ⟨v, hv, hrec⟩ := sound sig eval hA Γ env hΓ target false (.record fs) hr
    obtain ⟨w, hw, hτ⟩ := field_sound hrec hl
    exact ⟨w, by simp only [evalTerm, hv, Option.bind_eq_bind, Option.bind_some, hw], hτ⟩
theorem soundArgs (sig : Sig) (eval : String → List Val → Option Val) (hA : AtomsSound sig eval)
    (Γ : List MTy) (env : List Val) (hΓ : EnvTyped Γ env) :
    ∀ (ts : Terms) (c : Bool) (tys : List MTy), argsTy sig Γ c ts = some tys →
      ∃ vs, evalTerms eval env ts = some vs ∧ fitsL vs tys = true
  | .nil, c, tys, h => by
    simp only [argsTy, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | .cons head tail, c, tys, h => by
    simp only [argsTy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, rest, hrest, rfl⟩ := h
    obtain ⟨v, hv, hτ⟩ := sound sig eval hA Γ env hΓ head c t ht
    obtain ⟨vs, hvs, hfit⟩ := soundArgs sig eval hA Γ env hΓ tail c rest hrest
    refine ⟨v :: vs, ?_, ?_⟩
    · simp only [evalTerms, hv, hvs, Option.bind_eq_bind, Option.bind_some]
    · simp only [fitsL, hτ, hfit, Bool.and_self]
end

theorem termFits (sig : Sig) (eval : String → List Val → Option Val) (hA : AtomsSound sig eval)
    (Γ : List MTy) (env : List Val) (t : Term) (τ : MTy) (v : Val)
    (hty : argTy sig Γ false t = some τ) (hΓ : EnvTyped Γ env)
    (hv : evalTerm eval env t = some v) : hasTy τ v = true := by
  obtain ⟨w, hw, hτ⟩ := sound sig eval hA Γ env hΓ t false τ hty
  rw [hv, Option.some.injEq] at hw
  rw [hw]
  exact hτ

/-! ## 5. Route (a) under this value clause: `recordGet` is sound -/

def recordGetRule : List MTy → Option MTy
  | [.record fs, .lit n] => lookupName n (canon fs)
  | _ => none

def evGet : List Val → Option Val
  | [r, .str n] => getField n r
  | _ => none

def AtomSoundAt (rule : List MTy → Option MTy) (ev : List Val → Option Val) : Prop :=
  ∀ (tys : List MTy) (τ : MTy) (vs : List Val), rule tys = some τ → fitsL vs tys = true →
    ∃ v, ev vs = some v ∧ hasTy τ v = true

theorem recordGetRule_inv {tys : List MTy} {τ : MTy} (h : recordGetRule tys = some τ) :
    ∃ fs n, tys = [.record fs, .lit n] ∧ lookupName n (canon fs) = some τ := by
  unfold recordGetRule at h
  split at h
  · rename_i fs n
    exact ⟨fs, n, rfl, h⟩
  · exact nomatch h

theorem fitsL_two {vs : List Val} {a b : MTy} (h : fitsL vs [a, b] = true) :
    ∃ x y, vs = [x, y] ∧ hasTy a x = true ∧ hasTy b y = true := by
  match vs, h with
  | [x, y], h =>
    simp only [fitsL, Bool.and_true, Bool.and_eq_true] at h
    exact ⟨x, y, rfl, h.1, h.2⟩
  | [], h => simp only [fitsL, Bool.false_eq_true] at h
  | [_], h => simp only [fitsL, Bool.and_false, Bool.false_eq_true] at h
  | _ :: _ :: _ :: _, h => simp only [fitsL, Bool.and_false, Bool.false_eq_true] at h

theorem hasTy_lit_inv {n : String} {w : Val} (h : hasTy (.lit n) w = true) : w = .str n := by
  cases w with
  | str k =>
    simp only [hasTy, decide_eq_true_eq] at h
    rw [h]
  | _ => simp only [hasTy, Bool.false_eq_true] at h

theorem recordGet_sound : AtomSoundAt recordGetRule evGet := by
  intro tys τ vs hrule hfit
  obtain ⟨fs, n, rfl, hl⟩ := recordGetRule_inv hrule
  obtain ⟨r, w, rfl, hr, hw⟩ := fitsL_two hfit
  rw [hasTy_lit_inv hw]
  exact field_sound hr hl

/-! ## 6. The union of `Q1Positional.union_value_ambiguous`, here -/

def branchA : MTy := .record [("_tag", .lit "A"), ("a", .string)]
def branchD : MTy := .record [("M", .string), ("_tag", .lit "D")]
def objA : List (String × Val) := [("_tag", .str "A"), ("a", .str "D")]
def objD : List (String × Val) := [("M", .str "A"), ("_tag", .str "D")]

/-- rc.112's two objects lay out to two values, each a member of its own branch only. -/
theorem union_values_distinct :
    mkRecord (canon objA) ≠ mkRecord (canon objD) ∧
      hasTy branchA (mkRecord (canon objA)) = true ∧ hasTy branchD (mkRecord (canon objA)) = false ∧
      hasTy branchD (mkRecord (canon objD)) = true ∧ hasTy branchA (mkRecord (canon objD)) = false := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro h
  have h' : getField "_tag" (mkRecord (canon objA)) = getField "_tag" (mkRecord (canon objD)) := by
    rw [h]
  have hA : getField "_tag" (mkRecord (canon objA)) = some (.str "A") := by rfl
  have hD : getField "_tag" (mkRecord (canon objD)) = some (.str "D") := by rfl
  rw [hA, hD, Option.some.injEq] at h'
  injection h' with h''
  exact absurd h'' (by decide)

-- `{a: nat} | {b: nat}`: one value per object now
#guard hasTy (.record [("a", .nat)]) (mkRecord [("a", .nat 42)])
#guard !hasTy (.record [("b", .nat)]) (mkRecord [("a", .nat 42)])
-- the p2 shapes: `user.name` by name, whatever the layout
#guard getField "name" (mkRecord (canon [("role", .str "member"), ("id", .nat 2), ("name", .str "bob")])) == some (.str "bob")
#guard getField "email" (mkRecord (canon [("id", .nat 2), ("name", .str "bob")])) == none

/-! ## 7. Under this clause the atom is sound, but its label is an argument

The printer spells `recordGet(r, "b")` as `r.b` only when the label is a literal of the term:
a variable typed at the literal type `"b"` (the literal rule keeps it under a const-generic atom)
types the same application and leaves the printer no label to write. A `Term.field` carries the
label as data, so every well-typed projection has its member image. -/

def sigGet : Sig :=
  { atomOf := fun a tys => if a = "recordGet" then recordGetRule tys else none,
    constAtom := fun a => decide (a = "recordGet") }

/-- `recordGet(a0, a1)`, the label a variable. -/
def getByVar : Term := .app "recordGet" (.cons (.var 0) (.cons (.var 1) .nil))

/-- The label a member-access image needs: present only as a literal argument. -/
def memberLabel? : Term → Option String
  | .app "recordGet" (.cons _ (.cons (.lit (.str n)) .nil)) => some n
  | .field _ n => some n
  | _ => none

-- well typed, with `a1 : "b"` …
#guard (argTy sigGet [.record [("a", .nat), ("b", .string)], .lit "b"] false getByVar).isSome
-- … and no label to print; the literal spelling and the constructor have one
#guard (memberLabel? getByVar).isNone
#guard memberLabel? (.app "recordGet" (.cons (.var 0) (.cons (.lit (.str "b")) .nil))) == some "b"
#guard memberLabel? (.field (.var 0) "b") == some "b"

end SeatR.Named

#print axioms SeatR.Named.canon_map
#print axioms SeatR.Named.align
#print axioms SeatR.Named.lookup_found
#print axioms SeatR.Named.field_sound
#print axioms SeatR.Named.sound
#print axioms SeatR.Named.soundArgs
#print axioms SeatR.Named.termFits
#print axioms SeatR.Named.recordGet_sound
#print axioms SeatR.Named.union_values_distinct
