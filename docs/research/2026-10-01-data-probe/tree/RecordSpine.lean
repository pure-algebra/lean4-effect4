import Lean
import Effect4.Data.Row

/-!
# Seat TREE feasibility probe (2026-10-01): `Ty` with a mutual `Fields` spine (option B)

The type algebra note's recommendation (2026-09-18 §1.3): `record (fields : Fields)` with
`Fields := nil | cons (name : String) (type : Ty) (rest : Fields)` mutual with `Ty`. This probe
measures what the spine buys and costs against `RecordNested.lean` (option C, the same tree
code): the derived instances at full size, the eliminator, the hardest existing proof
(`key_injective`, `Ty.lean:253-276`) with its text unchanged, and normalization through the
spine. Probe choices as in `RecordNested.lean` (fields ascending by name key; first of a repeated
name kept). Order theorems and subtyping are not repeated here: they do not read the spine
differently from the list.
-/

set_option autoImplicit false

namespace DataProbe.Spine

mutual
inductive Ty
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | except (error value : Ty)
  | exitOf (value error : Ty)
  | causeOf (error : Ty)
  | fiberOf (value error : Ty)
  | union (left right : Ty)
  | lit (value : String)
  | refOf (value : Ty)
  | deferredOf (value error : Ty)
  | var (index : Nat)
  | unknown
  | record (fields : Fields)
inductive Fields
  | nil
  | cons (name : String) (type : Ty) (rest : Fields)
end

-- B: the derived equality survives (E1, now at full size).
deriving instance DecidableEq for Ty, Fields

-- B: the derived `Repr` is `partial` (E1); its `opaque` members are listed below.
deriving instance Repr for Ty, Fields

open Lean in
/-- Which constants of this namespace are `opaque` (what `partial def` elaborates to). -/
elab "#opaque_members" : command => do
  let env ← getEnv
  for (n, info) in env.constants.map₂.toList do
    if (`DataProbe.Spine).isPrefixOf n then
      if let .opaqueInfo _ := info then
        logInfo m!"opaque: {n}"

#opaque_members

namespace Fields

/-- B: the list view the laws are stated through. -/
def toList : Fields → List (String × Ty)
  | .nil => []
  | .cons n t rest => (n, t) :: rest.toList

def ofList : List (String × Ty) → Fields
  | [] => .nil
  | (n, t) :: rest => .cons n t (ofList rest)

theorem ofList_toList (fs : Fields) : ofList fs.toList = fs := by
  induction fs using Fields.rec (motive_1 := fun _ => True) with
  | nil => rfl
  | cons n t rest _ ih => simp only [toList, ofList, ih]
  | _ => trivial

theorem toList_ofList (l : List (String × Ty)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons p rest ih => obtain ⟨n, t⟩ := p; simp only [ofList, toList, ih]

end Fields

namespace Ty

@[induction_eliminator]
theorem ind {motive : Ty → Prop}
    (never : motive .never) (unit : motive .unit) (nat : motive .nat) (int : motive .int)
    (string : motive .string) (bool : motive .bool)
    (handle : ∀ target, motive (.handle target))
    (option : ∀ inner, motive inner → motive (.option inner))
    (list : ∀ inner, motive inner → motive (.list inner))
    (prod : ∀ left right, motive left → motive right → motive (.prod left right))
    (except : ∀ error value, motive error → motive value → motive (.except error value))
    (exitOf : ∀ value error, motive value → motive error → motive (.exitOf value error))
    (causeOf : ∀ error, motive error → motive (.causeOf error))
    (fiberOf : ∀ value error, motive value → motive error → motive (.fiberOf value error))
    (union : ∀ left right, motive left → motive right → motive (.union left right))
    (lit : ∀ value, motive (.lit value))
    (refOf : ∀ value, motive value → motive (.refOf value))
    (deferredOf : ∀ value error, motive value → motive error → motive (.deferredOf value error))
    (var : ∀ index, motive (.var index))
    (unknown : motive .unknown)
    (record : ∀ fields, (∀ p ∈ fields.toList, motive p.2) → motive (.record fields)) :
    ∀ t, motive t := fun t =>
  Ty.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs.toList, motive p.2)
    never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union
    lit refOf deferredOf var unknown record
    (fun _ h => nomatch h)
    (fun _ _ _ ihHead ihTail => fun p hp => by
      cases hp with
      | head => exact ihHead
      | tail _ h => exact ihTail p h)
    t

def nameKey (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

mutual
def key : Ty → List Nat
  | .never => [0]
  | .unknown => [19]
  | .unit => [1]
  | .nat => [2]
  | .int => [3]
  | .string => [4]
  | .bool => [5]
  | .handle target => 6 :: target.toUTF8.data.toList.map UInt8.toNat
  | .option inner => 7 :: key inner
  | .list inner => 8 :: key inner
  | .prod left right => 9 :: (key left).length :: key left ++ key right
  | .except error value => 10 :: (key error).length :: key error ++ key value
  | .exitOf value error => 11 :: (key value).length :: key value ++ key error
  | .causeOf error => 12 :: key error
  | .fiberOf value error => 13 :: (key value).length :: key value ++ key error
  | .union left right => 14 :: (key left).length :: key left ++ key right
  | .lit value => 15 :: value.toUTF8.data.toList.map UInt8.toNat
  | .refOf value => 16 :: key value
  | .deferredOf value error => 17 :: (key value).length :: key value ++ key error
  | .var index => [18, index]
  | .record fields => 20 :: keyFields fields
def keyFields : Fields → List Nat
  | .nil => [0]
  | .cons n t rest =>
    1 :: (nameKey n).length :: nameKey n ++ (key t).length :: key t ++ keyFields rest
end

private theorem utf8_key_injective {s t : String}
    (h : s.toUTF8.data.toList.map UInt8.toNat =
      t.toUTF8.data.toList.map UInt8.toNat) : s = t := by
  have bytes : s.toUTF8.data.toList = t.toUTF8.data.toList :=
    List.map_inj_right (fun _ _ he => UInt8.toNat_inj.mp he) |>.mp h
  have arrays : s.toUTF8.data = t.toUTF8.data := Array.toList_inj.mp bytes
  apply String.toByteArray_inj.mp
  exact ByteArray.ext arrays

private theorem prefixed_inj {a b r s : List Nat}
    (h : a.length :: (a ++ r) = b.length :: (b ++ s)) : a = b ∧ r = s := by
  simp only [List.cons.injEq] at h
  exact List.append_inj h.2 h.1

/-- B: the companion's injectivity; the induction is on the spine, by its own recursor. -/
private theorem keyFields_injective (fs : Fields)
    (ih : ∀ p ∈ fs.toList, ∀ {b : Ty}, key p.2 = key b → p.2 = b) :
    ∀ {gs : Fields}, keyFields fs = keyFields gs → fs = gs := by
  induction fs using Fields.rec (motive_1 := fun _ => True) with
  | nil =>
    intro gs h
    cases gs with
    | nil => rfl
    | cons m u gs =>
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
  | cons n t fs _ ihf =>
    intro gs h
    cases gs with
    | nil =>
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
    | cons m u gs =>
      simp only [keyFields, List.cons.injEq, List.append_assoc, List.cons_append] at h
      obtain ⟨hn, hrest⟩ := List.append_inj h.2.2 h.2.1
      obtain ⟨ht, hfs⟩ := prefixed_inj hrest
      have hnm : n = m := utf8_key_injective hn
      have htu : t = u := ih (n, t) List.mem_cons_self ht
      have hfg : fs = gs := ihf (fun p hp => ih p (List.mem_cons_of_mem _ hp)) hfs
      rw [hnm, htu, hfg]
  | _ => trivial

/-- The original text (`Ty.lean:253-276`), one goal more: the same as option C. -/
theorem key_injective {a b : Ty} (h : key a = key b) : a = b := by
  induction a generalizing b <;> cases b <;>
    simp only [key, List.cons_append, List.cons.injEq] at h
  all_goals try (rcases h with ⟨h, _⟩; contradiction)
  all_goals try rfl
  · exact congrArg Ty.handle (utf8_key_injective h.2)
  · exact congrArg Ty.option (by apply_assumption; exact h.2)
  · exact congrArg Ty.list (by apply_assumption; exact h.2)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · exact congrArg Ty.causeOf (by apply_assumption; exact h.2)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · exact congrArg Ty.lit (utf8_key_injective h.2)
  · exact congrArg Ty.refOf (by apply_assumption; exact h.2)
  · obtain ⟨hl, hr⟩ := List.append_inj h.2.2 h.2.1
    congr 1 <;> (apply_assumption; assumption)
  · exact congrArg Ty.var h.2.1
  · rename_i fields ih gs
    exact congrArg Ty.record (keyFields_injective fields (fun p hp _ hb => ih p hp hb) h.2)

/-! ### Normalization through the spine -/

def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

/-- B: insertion is written on the spine (structural recursion needs the spine form). -/
def insertField (n : String) (t : Ty) : Fields → Fields
  | .nil => .cons n t .nil
  | .cons m u rest =>
    if nameKey n = nameKey m then .cons n t rest
    else if ltKey (nameKey n) (nameKey m) then .cons n t (.cons m u rest)
    else .cons m u (insertField n t rest)

/-- B: the same insertion on the list view, where the list laws live. -/
def insertFieldL (p : String × Ty) : List (String × Ty) → List (String × Ty)
  | [] => [p]
  | q :: rest =>
    if nameKey p.1 = nameKey q.1 then p :: rest
    else if ltKey (nameKey p.1) (nameKey q.1) then p :: q :: rest
    else q :: insertFieldL p rest

/-- B: the bridge every spine law crosses. -/
theorem toList_insertField (n : String) (t : Ty) (fs : Fields) :
    (insertField n t fs).toList = insertFieldL (n, t) fs.toList := by
  induction fs using Fields.rec (motive_1 := fun _ => True) with
  | nil => rfl
  | cons m u rest _ ih =>
    simp only [insertField, insertFieldL, Fields.toList]
    split
    · rfl
    · split
      · rfl
      · simp only [Fields.toList, ih]
  | _ => trivial

mutual
/-- Normalization: only the arms that matter here; the others are the identity. -/
def normalize : Ty → Ty
  | .option t => .option (normalize t)
  | .list t => .list (normalize t)
  | .record fs => .record (normalizeFields fs)
  | t => t
def normalizeFields : Fields → Fields
  | .nil => .nil
  | .cons n t rest => insertField n (normalize t) (normalizeFields rest)
end

def FieldsAscending (fs : Fields) : Prop :=
  fs.toList.Pairwise fun p q => ltKey (nameKey p.1) (nameKey q.1) = true

inductive Normal : Ty → Prop
  | nat : Normal .nat
  | string : Normal .string
  | option {t} : Normal t → Normal (.option t)
  | list {t} : Normal t → Normal (.list t)
  | record {fs : Fields} : (∀ p ∈ fs.toList, Normal p.2) → FieldsAscending fs → Normal (.record fs)

theorem mem_insertFieldL {p x : String × Ty} {fs : List (String × Ty)}
    (h : x ∈ insertFieldL p fs) : x = p ∨ x ∈ fs := by
  induction fs with
  | nil => simp only [insertFieldL, List.mem_singleton] at h; exact Or.inl h
  | cons q rest ih =>
    simp only [insertFieldL] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- B: membership of the normalized spine, through the bridge. -/
theorem mem_normalizeFields {x : String × Ty} {fs : Fields}
    (h : x ∈ (normalizeFields fs).toList) : ∃ p ∈ fs.toList, x = (p.1, normalize p.2) := by
  induction fs using Fields.rec (motive_1 := fun _ => True) with
  | nil => nomatch h
  | cons n t rest _ ih =>
    simp only [normalizeFields, toList_insertField] at h
    rcases mem_insertFieldL h with h | h
    · exact ⟨(n, t), List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hx⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩
  | _ => trivial

/-- The record arm of `normal_normalize`, through the spine (ascent is `RecordNested.lean`'s
`ascending_insertField` on the list view; it is the same lemma and is taken as a premise here). -/
theorem normal_normalize_record (fs : Fields)
    (ih : ∀ p ∈ fs.toList, Normal (normalize p.2))
    (ascent : FieldsAscending (normalizeFields fs)) :
    Normal (normalize (.record fs)) := by
  refine .record (fun x hx => ?_) ascent
  obtain ⟨p, hp, rfl⟩ := mem_normalizeFields hx
  exact ih p hp

end Ty

end DataProbe.Spine

#print axioms DataProbe.Spine.Ty.ind
#print axioms DataProbe.Spine.Ty.key_injective
#print axioms DataProbe.Spine.Ty.toList_insertField
#print axioms DataProbe.Spine.Ty.mem_normalizeFields
#print axioms DataProbe.Spine.Ty.normal_normalize_record
