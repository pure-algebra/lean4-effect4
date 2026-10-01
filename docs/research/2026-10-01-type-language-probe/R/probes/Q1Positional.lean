import Effect4.Machine.Term
import Effect4.Program.Ty

/-!
# Seat R, question 1, under row 119 as ruled: positional record values

Type-language probe, 2026-10-01. A model, not the tree.

* `MTy` is an eight-former copy of the type language with row 119's record:
  `record (fields : List (String × MTy))`, canonical field order by the UTF-8 key order `Ty.key`
  already uses for `lit` (`nameLt`, Codex's `ConstructiveOrdering.lean` reuse), the first of a
  repeated name kept.
* Values are the tree's own carrier `Effect4.Store.Val`; a record value is positional,
  `ctor 0 vs`, `vs` in canonical field order (row 119).
* The term language, the literal rule (`litArgTy`), the term typer (`argTy`/`argsTy`) and the
  evaluator (`evalTerm`/`evalTerms`) are copies of `Machine/Term.lean:97-107, :424-438` and
  `Program/Typing/Rules.lean:77-102` with two record forms added (route (b)):
  `record (labels : List String) (args : Terms)` and `field (target : Term) (index : Nat)
  (name : String)`.
* Atom typing receives the argument types only and atom evaluation the argument values only,
  as `Signature.atomOf : String → List Ty → Option Ty` (`Typing/Rules.lean:54`) and
  `NativeAtom.eval : NativeAtom → List Val → Option Val` (`Machine/Term.lean:365`) do.

What it shows:
1. route (a), the atoms: no evaluator makes `recordGet` sound, with or without an index
   argument (`recordGet_unsound`, `recordGetAt_unsound`): the typer cannot see the index
   (`index_blind`) and the evaluator cannot see the record type;
2. route (b) as the brief writes it, `field (t : Term) (name : String)`: no untyped evaluator is
   sound either (`NameOnly.unsound`), so the stored projection must carry its position;
3. route (b) with a checked position: progress and preservation for the whole term language
   (`sound`, `termFits`), from atom soundness and `EnvTyped`;
4. positional values make a union of records ambiguous (`union_value_ambiguous`): one value fits
   two branches that rc.112 keeps apart, so a `_tag` select cannot be faithful.
-/

set_option autoImplicit false

namespace SeatR.Positional

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

/-! ## 2. The model type language and its membership check (a fold, canonical-order read) -/

inductive MTy where
  | unit
  | nat
  | string
  | bool
  | lit (s : String)
  | prod (a b : MTy)
  | union (a b : MTy)
  | record (fields : List (String × MTy))

/-- Positional fit of argument values against checkers. -/
def fitPos : List Val → List (String × (Val → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

mutual
/-- Membership. The record arm reads the value's positions in canonical field order (the
synthesis model's repair, `SynthRecord.hasTy_normalize`). -/
def hasTy : MTy → Val → Bool
  | .unit, v => match v with | .unit => true | _ => false
  | .nat, v => match v with | .nat _ => true | _ => false
  | .string, v => match v with | .str _ => true | _ => false
  | .bool, v => match v with | .bool _ => true | _ => false
  | .lit s, v => match v with | .str t => decide (t = s) | _ => false
  | .prod a b, v => match v with | .list [x, y] => hasTy a x && hasTy b y | _ => false
  | .union a b, v => hasTy a v || hasTy b v
  | .record fs, v => match v with | .ctor 0 vs => fitPos vs (canon (checks fs)) | _ => false
/-- The field checkers, in written order. -/
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

theorem hasTy_record_ctor (fs : List (String × MTy)) (vs : List Val) :
    hasTy (.record fs) (.ctor 0 vs) = fitPos vs (canon (checks fs)) := by
  simp only [hasTy]

/-- A record member is a positional `ctor 0` whose positions fit the canonical fields. -/
theorem hasTy_record_inv (fs : List (String × MTy)) (v : Val)
    (h : hasTy (.record fs) v = true) :
    ∃ vs, v = .ctor 0 vs ∧ fitPos vs (canon (checks fs)) = true := by
  cases v with
  | ctor k vs =>
    cases k with
    | zero => exact ⟨vs, rfl, h⟩
    | succ k => simp only [hasTy, Bool.false_eq_true] at h
  | _ => simp only [hasTy, Bool.false_eq_true] at h

/-- Reading position `i` of a fitting value: the checker at `i` holds there. -/
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

/-- A positional value fits a mapped list exactly when every pair fits. -/
theorem fitPos_map_map {β : Type} (M : List (String × β)) (g : β → Val) (c : β → Val → Bool) :
    fitPos (M.map (fun p => g p.2)) (M.map (fun p => (p.1, c p.2))) = M.all (fun p => c p.2 (g p.2)) := by
  induction M with
  | nil => rfl
  | cons p M ih =>
    simp only [List.map_cons, fitPos, List.all_cons, ih]

/-! ## 3. The model terms: the tree's `Term`/`Terms` with route (b)'s two forms -/

mutual
  inductive Term
    | var (index : Nat)
    | lit (value : Lit)
    | app (atom : String) (args : Terms)
    /-- `{ l₁: t₁, …, lₙ: tₙ }`: the labels in written order, the values a `Terms` list, so no
    new nested family (the existing generator emits its fold arm: two leaf/direct positions). -/
    | record (labels : List String) (args : Terms)
    /-- `t.name`, read at canonical position `index`, which the typer checks against `name`. -/
    | field (target : Term) (index : Nat) (name : String)
  inductive Terms
    | nil
    | cons (head : Term) (tail : Terms)
end

deriving instance DecidableEq for Term, Terms

/-! ## 4. The checker's interface: the literal rule and the term typer (a fold) -/

/-- What the term typer reads of a signature: the atoms by argument types, the const flag. -/
structure Sig where
  atomOf : String → List MTy → Option MTy
  constAtom : String → Bool

/-- The literal rule (`Typing/Rules.lean:77-81`): a string literal keeps its literal type only as
a direct argument of a const-generic atom; every number literal is `nat`. -/
def litArgTy (const : Bool) : Lit → MTy
  | .str s => if const then .lit s else .string
  | .unit => .unit
  | .nat _ => .nat
  | .bool _ => .bool

/-- No repeated label (row 119 (e): refused at formation, TS2300/TS1117 on the target). -/
def distinct : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && distinct ns

/-- The record arm of the typer for `field`: the target must be a record whose canonical
position `index` holds `name`. -/
def fieldTy : MTy → Nat → String → Option MTy
  | .record fs, index, name =>
    match (canon fs)[index]? with
    | some (m, τ) => if m = name then some τ else none
    | none => none
  | _, _, _ => none

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
    | .field target index name => do
      let r ← argTy sig env false target
      fieldTy r index name
  def argsTy (sig : Sig) (env : List MTy) (const : Bool) : Terms → Option (List MTy)
    | .nil => some []
    | .cons head tail => do
      let t ← argTy sig env const head
      let rest ← argsTy sig env const tail
      some (t :: rest)
end

/-- Located refusals of the two record arms (the checker's `Except TypeRefusal` would carry
them with a path). -/
inductive RecordRefusal
  | notARecord
  | unknownName (name : String)
  | wrongIndex (name : String) (expected given : Nat)
  | arity (labels values : Nat)
  | repeated
deriving DecidableEq, Repr

def explainField : MTy → Nat → String → Option RecordRefusal
  | .record fs, index, name =>
    match (canon fs).findIdx? (fun p => decide (p.1 = name)) with
    | none => some (.unknownName name)
    | some expected => if expected = index then none else some (.wrongIndex name expected index)
  | _, _, _ => some .notARecord

/-! ## 5. The evaluator (untyped, below the type language, as in the tree) -/

mutual
  def evalTerm (eval : String → List Val → Option Val) (env : List Val) : Term → Option Val
    | .var index => env[index]?
    | .lit value => value.toVal
    | .app atom args => do
      let vs ← evalTerms eval env args
      eval atom vs
    | .record labels args => do
      let vs ← evalTerms eval env args
      if labels.length = vs.length then
        some (.ctor 0 ((canon (labels.zip vs)).map Prod.snd))
      else none
    | .field target index _ => do
      let v ← evalTerm eval env target
      match v with
      | .ctor 0 vs => vs[index]?
      | _ => none
  def evalTerms (eval : String → List Val → Option Val) (env : List Val) :
      Terms → Option (List Val)
    | .nil => some []
    | .cons head tail => do
      let v ← evalTerm eval env head
      let rest ← evalTerms eval env tail
      some (v :: rest)
end

/-! ## 6. Route (b) with a checked position: progress and preservation

The tree's per-atom obligation is `NativeAtom.Sound` (`Laws/Program/Typed.lean:606`): at any
argument types the atom accepts, fitting arguments evaluate and the answer fits. `AtomsSound` is
that, over the whole model table. `EnvTyped` is seat A's form (`Typed/Admission.lean:71`). -/

/-- Argument values fit argument types, position by position. -/
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

/-- The three-way zip projects back to its two two-way zips when the payload lists agree. -/
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

/-- Construction is sound: the canonical permutation of the values fits the canonical fields,
because `canon` sorts by name only (`canon_map`). -/
theorem align (ks : List String) (vs : List Val) (tys : List MTy)
    (hf : fitsL vs tys = true) :
    fitPos ((canon (ks.zip vs)).map Prod.snd) (canon (checks (ks.zip tys))) = true := by
  obtain ⟨h1, h2⟩ := zip3_proj ks vs tys (fitsL_length hf)
  have hv : canon (ks.zip vs) = (canon (ks.zip (vs.zip tys))).map (fun q => (q.1, q.2.1)) := by
    rw [← h1]
    exact canon_map Prod.fst (ks.zip (vs.zip tys))
  have hc : canon (checks (ks.zip tys)) =
      (canon (ks.zip (vs.zip tys))).map (fun q => (q.1, hasTy q.2.2)) := by
    rw [checks_eq_map, ← h2, List.map_map]
    exact canon_map (fun x => hasTy x.2) (ks.zip (vs.zip tys))
  rw [hv, hc, List.map_map]
  have key := fitPos_map_map (canon (ks.zip (vs.zip tys))) Prod.fst (fun x => hasTy x.2)
  simp only [Function.comp_def] at key ⊢
  rw [key, List.all_eq_true]
  intro q hq
  have hmem := mem_canon q _ hq
  exact fitsL_zip hf q.2 (List.of_mem_zip hmem).2

theorem fieldTy_inv {r : MTy} {i : Nat} {n : String} {τ : MTy} (h : fieldTy r i n = some τ) :
    ∃ fs, r = .record fs ∧ (canon fs)[i]? = some (n, τ) := by
  cases r with
  | record fs =>
    simp only [fieldTy] at h
    split at h
    · rename_i m σ hget
      split at h
      · rename_i hm
        subst hm
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨fs, rfl, hget⟩
      · exact nomatch h
    · exact nomatch h
  | _ => simp only [fieldTy, reduceCtorEq] at h

/-- Projection is sound: the checked position holds a member of the field's type. -/
theorem field_sound {fs : List (String × MTy)} {v : Val} {i : Nat} {n : String} {τ : MTy}
    (hv : hasTy (.record fs) v = true) (hi : (canon fs)[i]? = some (n, τ)) :
    ∃ vs w, v = .ctor 0 vs ∧ vs[i]? = some w ∧ hasTy τ w = true := by
  obtain ⟨vs, rfl, hfit⟩ := hasTy_record_inv fs v hv
  rw [canon_checks] at hfit
  obtain ⟨w, hw, hτ⟩ := fitPos_get (canon fs) vs i n τ hfit hi
  exact ⟨vs, w, rfl, hw, hτ⟩

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

mutual
/-- Progress and preservation for the model's terms, route (b) with a checked position. -/
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
      refine ⟨.ctor 0 ((canon (labels.zip vs)).map Prod.snd), ?_, ?_⟩
      · simp only [evalTerm, hvs, Option.bind_eq_bind, Option.bind_some, hlen, ↓reduceIte]
      · rw [hasTy_record_ctor]
        exact align labels vs tys hfit
    · exact nomatch hrec
  | .field target i n, c, τ, h => by
    simp only [argTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, hfield⟩ := h
    obtain ⟨fs, rfl, hi⟩ := fieldTy_inv hfield
    obtain ⟨v, hv, hrec⟩ := sound sig eval hA Γ env hΓ target false (.record fs) hr
    obtain ⟨vs, w, rfl, hw, hτ⟩ := field_sound hrec hi
    exact ⟨w, by simp only [evalTerm, hv, Option.bind_eq_bind, Option.bind_some, hw], hτ⟩
/-- The argument lists, position by position. -/
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

/-- The tree's `TermFits` shape (`Typed/Assembly.lean:837`, row 148's `evalTerm_fits`):
preservation only, outside a const-generic atom. -/
theorem termFits (sig : Sig) (eval : String → List Val → Option Val) (hA : AtomsSound sig eval)
    (Γ : List MTy) (env : List Val) (t : Term) (τ : MTy) (v : Val)
    (hty : argTy sig Γ false t = some τ) (hΓ : EnvTyped Γ env)
    (hv : evalTerm eval env t = some v) : hasTy τ v = true := by
  obtain ⟨w, hw, hτ⟩ := sound sig eval hA Γ env hΓ t false τ hty
  rw [hv, Option.some.injEq] at hw
  rw [hw]
  exact hτ

/-! ## 7. Route (a), the atoms: no evaluator makes `recordGet` sound

`recordGet(r, "b")` and `recordGet(r, "b", i)` as const-generic atoms: the label reaches the typer
as `lit "b"` (the literal rule), the index as `nat` (every number literal), and the evaluator gets
the values `[r, "b"]` or `[r, "b", i]` and nothing else. -/

/-- The atom's typing as a custom scheme: the record's canonical field named by the label. -/
def recordGetRule : List MTy → Option MTy
  | [.record fs, .lit n] => lookupName n (canon fs)
  | _ => none

/-- The same with an index argument, which the literal rule types `nat` whatever its value. -/
def recordGetAtRule : List MTy → Option MTy
  | [.record fs, .lit n, .nat] => lookupName n (canon fs)
  | _ => none

/-- The tree's `NativeAtom.Sound` (`Laws/Program/Typed.lean:606`) at one atom, as data. -/
def AtomSoundAt (rule : List MTy → Option MTy) (ev : List Val → Option Val) : Prop :=
  ∀ (tys : List MTy) (τ : MTy) (vs : List Val), rule tys = some τ → fitsL vs tys = true →
    ∃ v, ev vs = some v ∧ hasTy τ v = true

/-- Two layouts with one positional image: `{a: nat, b: string}` and `{b: nat, c: string}`. -/
def layoutAB : MTy := .record [("a", .nat), ("b", .string)]
def layoutBC : MTy := .record [("b", .nat), ("c", .string)]
def shared : Val := .ctor 0 [.nat 1, .str "x"]

theorem shared_fits_AB : hasTy layoutAB shared = true := by decide +kernel
theorem shared_fits_BC : hasTy layoutBC shared = true := by decide +kernel

theorem string_nat_disjoint (v : Val) (h1 : hasTy .string v = true) (h2 : hasTy .nat v = true) :
    False := by
  cases v <;> simp only [hasTy, Bool.false_eq_true] at h1 h2

/-- **What the atom route cannot state.** No evaluator makes `recordGet` sound: one argument
list fits both layouts' argument types, and soundness then needs one answer at `string` and at
`nat`. -/
theorem recordGet_unsound (ev : List Val → Option Val) : ¬ AtomSoundAt recordGetRule ev := by
  intro h
  obtain ⟨v₁, hv₁, h₁⟩ := h [layoutAB, .lit "b"] .string [shared, .str "b"]
    (by rfl) (by decide +kernel)
  obtain ⟨v₂, hv₂, h₂⟩ := h [layoutBC, .lit "b"] .nat [shared, .str "b"]
    (by rfl) (by decide +kernel)
  rw [hv₁, Option.some.injEq] at hv₂
  subst hv₂
  exact string_nat_disjoint v₁ h₁ h₂

/-- The index does not help: the typer cannot see its value, so the same argument list (index 1,
right for `{a, b}` and wrong for `{b, c}`) types at both layouts. -/
theorem recordGetAt_unsound (ev : List Val → Option Val) : ¬ AtomSoundAt recordGetAtRule ev := by
  intro h
  obtain ⟨v₁, hv₁, h₁⟩ := h [layoutAB, .lit "b", .nat] .string [shared, .str "b", .nat 1]
    (by rfl) (by decide +kernel)
  obtain ⟨v₂, hv₂, h₂⟩ := h [layoutBC, .lit "b", .nat] .nat [shared, .str "b", .nat 1]
    (by rfl) (by decide +kernel)
  rw [hv₁, Option.some.injEq] at hv₂
  subst hv₂
  exact string_nat_disjoint v₁ h₁ h₂

/-- The literal rule erases an index: a wrong-but-in-range index has the same argument types as
the right one, under either flag, so an atom's typing cannot refuse it. -/
theorem index_blind (sig : Sig) (Γ : List MTy) (c : Bool) (r : Term) (n : String) (k₁ k₂ : Nat) :
    argsTy sig Γ c (.cons r (.cons (.lit (.str n)) (.cons (.lit (.nat k₁)) .nil))) =
      argsTy sig Γ c (.cons r (.cons (.lit (.str n)) (.cons (.lit (.nat k₂)) .nil))) := by
  simp only [argsTy, argTy, litArgTy]

/-! ## 8. Route (b) as the brief writes it, `field (t : Term) (name : String)`: no untyped
evaluator is sound either. Any evaluator of the tree's shape is a function of the environment's
values and the term, and the type is not among them. -/

namespace NameOnly

inductive TermN
  | var (index : Nat)
  | field (target : TermN) (name : String)

def argTyN (Γ : List MTy) : TermN → Option MTy
  | .var i => Γ[i]?
  | .field t n =>
    match argTyN Γ t with
    | some (.record fs) => lookupName n (canon fs)
    | _ => none

theorem envAB : EnvTyped [layoutAB] [shared] := by
  refine ⟨rfl, fun i τ v hτ hv => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hτ hv
    subst hτ hv
    exact shared_fits_AB
  | succ i => simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hτ

theorem envBC : EnvTyped [layoutBC] [shared] := by
  refine ⟨rfl, fun i τ v hτ hv => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hτ hv
    subst hτ hv
    exact shared_fits_BC
  | succ i => simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hτ

/-- No evaluator of a name-only projection has progress and preservation. -/
theorem unsound (ev : List Val → TermN → Option Val) :
    ¬ ∀ (Γ : List MTy) (env : List Val) (t : TermN) (τ : MTy), EnvTyped Γ env →
        argTyN Γ t = some τ → ∃ v, ev env t = some v ∧ hasTy τ v = true := by
  intro h
  obtain ⟨v₁, hv₁, h₁⟩ := h [layoutAB] [shared] (.field (.var 0) "b") .string envAB
    (by rfl)
  obtain ⟨v₂, hv₂, h₂⟩ := h [layoutBC] [shared] (.field (.var 0) "b") .nat envBC
    (by rfl)
  rw [hv₁, Option.some.injEq] at hv₂
  subst hv₂
  exact string_nat_disjoint v₁ h₁ h₂

end NameOnly

/-! ## 9. Positional values make a union of records ambiguous (stage 2's `_tag` select)

The canonical order is UTF-8 bytes: `M` (77) < `_tag` (95) < `a` (97), so `_tag` is not at one
position across branches. One value then fits two branches that rc.112 keeps apart. -/

def branchA : MTy := .record [("_tag", .lit "A"), ("a", .string)]
def branchD : MTy := .record [("M", .string), ("_tag", .lit "D")]
def ambiguous : Val := .ctor 0 [.str "A", .str "D"]

/-- The adapter's canonical layout of a host object (route A), positional. -/
def layOut (obj : List (String × Val)) : Val := .ctor 0 ((canon obj).map Prod.snd)

def objA : List (String × Val) := [("_tag", .str "A"), ("a", .str "D")]
def objD : List (String × Val) := [("M", .str "A"), ("_tag", .str "D")]

theorem union_value_ambiguous :
    hasTy branchA ambiguous = true ∧ hasTy branchD ambiguous = true := by decide +kernel

/-- Two host objects of the union, distinct as objects (different keys), lay out to one value. -/
theorem positional_not_injective : layOut objA = ambiguous ∧ layOut objD = ambiguous ∧ objA ≠ objD := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  have := congrArg (fun o => o.map Prod.fst) h
  simp only [objA, objD, List.map_cons, List.map_nil, List.cons.injEq] at this
  exact absurd this.1 (by decide)

-- Codex's union image for records: `{a: nat} | {b: nat}` shares every value.
#guard hasTy (.record [("a", .nat)]) (.ctor 0 [.nat 42]) && hasTy (.record [("b", .nat)]) (.ctor 0 [.nat 42])
-- The canonical order puts `M` before `_tag` before `a`.
#guard (canon objD).map Prod.fst == ["M", "_tag"]
#guard (canon objA).map Prod.fst == ["_tag", "a"]

/-! ## 10. Finite checks on p2's data, and the typer's located refusals -/

/-- A signature with no atoms: enough for records. -/
def sig0 : Sig := { atomOf := fun _ _ => none, constAtom := fun _ => false }
def ev0 : String → List Val → Option Val := fun _ _ => none

def userTy : MTy := .record [("id", .nat), ("name", .string), ("role", .union (.lit "admin") (.lit "member"))]

/-- `{ role: "member", id: 2, name: "bob" }`, written out of canonical order. -/
def bobTerm : Term :=
  .record ["role", "id", "name"]
    (.cons (.lit (.str "member")) (.cons (.lit (.nat 2)) (.cons (.lit (.str "bob")) .nil)))

-- the written order is kept in the type, the canonical order in the value
#guard evalTerm ev0 [] bobTerm == some (.ctor 0 [.nat 2, .str "bob", .str "member"])
#guard (evalTerm ev0 [] bobTerm).map (hasTy userTy) == some true
-- `user.name` at canonical position 1
#guard evalTerm ev0 [.ctor 0 [.nat 2, .str "bob", .str "member"]] (.field (.var 0) 1 "name") == some (.str "bob")
#guard (argTy sig0 [userTy] false (.field (.var 0) 1 "name")).isSome
-- a wrong-but-in-range index is refused, and says where the name is
#guard (argTy sig0 [userTy] false (.field (.var 0) 0 "name")).isNone
#guard explainField userTy 0 "name" == some (.wrongIndex "name" 1 0)
-- an unknown name, a non-record target
#guard explainField userTy 0 "email" == some (.unknownName "email")
#guard explainField .string 0 "name" == some .notARecord
#guard explainField userTy 1 "name" == none
-- a repeated label is refused at formation; a short label list too
#guard (argTy sig0 [] false (.record ["a", "a"] (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil)))).isNone
#guard (argTy sig0 [] false (.record ["a"] (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil)))).isNone

/-! ## 11. The generated fold over the extended `Term`

The tree's generator (`tools/Effect4Gen/Fold.lean`) emits `TermAlgebra`/`cata_term` from the
declaration; the two new constructors have leaf positions (`List String`, `Nat`, `String`) and
direct ones (`Term`, `Terms`) only, which its position grammar already has (`Pos.leaf`,
`Pos.direct`, `Fold.lean:44-62`). This is the shape it would emit, and the evaluator is one of
its folds. -/

inductive TermFam
  | term
  | terms

structure TermAlgebra (R : TermFam → Type) where
  term_var : Nat → R .term
  term_lit : Lit → R .term
  term_app : String → R .terms → R .term
  term_record : List String → R .terms → R .term
  term_field : R .term → Nat → String → R .term
  terms_nil : R .terms
  terms_cons : R .term → R .terms → R .terms

mutual
def cata_term {R : TermFam → Type} (alg : TermAlgebra R) : Term → R .term
  | .var a0 => alg.term_var a0
  | .lit a0 => alg.term_lit a0
  | .app a0 a1 => alg.term_app a0 (cata_terms alg a1)
  | .record a0 a1 => alg.term_record a0 (cata_terms alg a1)
  | .field a0 a1 a2 => alg.term_field (cata_term alg a0) a1 a2
def cata_terms {R : TermFam → Type} (alg : TermAlgebra R) : Terms → R .terms
  | .nil => alg.terms_nil
  | .cons a0 a1 => alg.terms_cons (cata_term alg a0) (cata_terms alg a1)
end

abbrev EvalCarrier : TermFam → Type
  | .term => List Val → Option Val
  | .terms => List Val → Option (List Val)

def evalAlg (eval : String → List Val → Option Val) : TermAlgebra EvalCarrier where
  term_var i := fun env => env[i]?
  term_lit v := fun _ => v.toVal
  term_app atom args := fun env => do
    let vs ← args env
    eval atom vs
  term_record labels args := fun env => do
    let vs ← args env
    if labels.length = vs.length then some (.ctor 0 ((canon (labels.zip vs)).map Prod.snd))
    else none
  term_field target index _ := fun env => do
    let v ← target env
    match v with
    | .ctor 0 vs => vs[index]?
    | _ => none
  terms_nil := fun _ => some []
  terms_cons h t := fun env => do
    let v ← h env
    let rest ← t env
    some (v :: rest)

mutual
theorem evalTerm_fold (eval : String → List Val → Option Val) :
    ∀ (t : Term) (env : List Val), evalTerm eval env t = cata_term (evalAlg eval) t env
  | .var _, _ => rfl
  | .lit _, _ => rfl
  | .app atom args, env => by
    simp only [evalTerm, cata_term, evalAlg, evalTerms_fold eval args env]
  | .record labels args, env => by
    simp only [evalTerm, cata_term, evalAlg, evalTerms_fold eval args env]
  | .field target index name, env => by
    simp only [evalTerm, cata_term, evalAlg, evalTerm_fold eval target env]
theorem evalTerms_fold (eval : String → List Val → Option Val) :
    ∀ (ts : Terms) (env : List Val), evalTerms eval env ts = cata_terms (evalAlg eval) ts env
  | .nil, _ => rfl
  | .cons head tail, env => by
    simp only [evalTerms, cata_terms, evalAlg, evalTerm_fold eval head env,
      evalTerms_fold eval tail env]
end

end SeatR.Positional

#print axioms SeatR.Positional.canon_map
#print axioms SeatR.Positional.mem_canon
#print axioms SeatR.Positional.align
#print axioms SeatR.Positional.field_sound
#print axioms SeatR.Positional.sound
#print axioms SeatR.Positional.soundArgs
#print axioms SeatR.Positional.termFits
#print axioms SeatR.Positional.recordGet_unsound
#print axioms SeatR.Positional.recordGetAt_unsound
#print axioms SeatR.Positional.index_blind
#print axioms SeatR.Positional.NameOnly.unsound
#print axioms SeatR.Positional.union_value_ambiguous
#print axioms SeatR.Positional.positional_not_injective
#print axioms SeatR.Positional.evalTerm_fold
#print axioms SeatR.Positional.fitsL_length
#print axioms SeatR.Positional.fitsL_zip
#print axioms SeatR.Positional.zip3_proj
#print axioms SeatR.Positional.fitPos_map_map
#print axioms SeatR.Positional.lit_sound
#print axioms SeatR.Positional.var_sound
#print axioms SeatR.Positional.fieldTy_inv
#print axioms SeatR.Positional.fitPos_get
#print axioms SeatR.Positional.hasTy_record_inv
#print axioms SeatR.Positional.checks_eq_map
#print axioms SeatR.Positional.canon_checks
