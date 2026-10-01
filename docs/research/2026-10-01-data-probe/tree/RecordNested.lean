import Effect4.Data.Row
import Effect4.Store.Carrier.Val

/-!
# Seat TREE feasibility probe (2026-10-01): `Ty` with one appended `record` constructor

A copy of `src/Effect4/Program/Ty.lean` at `bc77e97f` (lines 37–884, the parts normalization
and its laws need) in the namespace `DataProbe.Nested`, with one constructor appended:

    | record (fields : List (String × Ty))

and the arms, companions and lemmas that the record costs. It measures the **shape** of option
C of the type algebra note (2026-09-18 §1.2), not the tree edit. What is copied unchanged is
marked "unchanged"; every other declaration is new or carries a new arm, and is marked
"record:". Probe choices that are design decisions, not recommendations:

* canonical record: fields strictly ascending by the UTF-8 bytes of the name (the key `Ty.key`
  already uses for strings, `Ty.lean:142-145`), so names are distinct;
* `normalize` keeps the **first** field of a repeated name (a formation-time refusal is the
  likely ruling; recorded as open in the note);
* subtyping is TypeScript's width-and-depth rule for readonly fields;
* a record value is `Val.ctor 0 [v₁, …, vₙ]` in canonical field order: the tree's own rule for
  a structure (`Machine/Value.lean:31-33`; `Store/Domain/Shape.lean:172`).

The value judgment at the end (`FitsV`) is the world-free part of
`Laws/Program/Typed/Membership.lean`'s `Fits`: every arm that does not read a declaration table.
-/

set_option autoImplicit false

namespace DataProbe.Nested

/-! ## The type language, one constructor appended -/

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
  /-- record: `{ readonly f₁: T₁; … }`, appended last (the mirror pins declaration order). -/
  | record (fields : List (String × Ty))

namespace Ty

/-! ### record: what `deriving DecidableEq, Repr` no longer gives (E1: refused / `partial`) -/

mutual
/-- record: structural equality as a Boolean, by hand. -/
def beq : Ty → Ty → Bool
  | .never, .never | .unit, .unit | .nat, .nat | .int, .int | .string, .string
  | .bool, .bool | .unknown, .unknown => true
  | .handle a, .handle b | .lit a, .lit b => decide (a = b)
  | .option a, .option b | .list a, .list b | .causeOf a, .causeOf b
  | .refOf a, .refOf b => beq a b
  | .prod a1 a2, .prod b1 b2 | .except a1 a2, .except b1 b2 | .exitOf a1 a2, .exitOf b1 b2
  | .fiberOf a1 a2, .fiberOf b1 b2 | .union a1 a2, .union b1 b2
  | .deferredOf a1 a2, .deferredOf b1 b2 => beq a1 b1 && beq a2 b2
  | .var i, .var j => decide (i = j)
  | .record fs, .record gs => beqFields fs gs
  | _, _ => false
/-- record: the field-list companion. -/
def beqFields : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | (n, s) :: fs, (m, t) :: gs => decide (n = m) && beq s t && beqFields fs gs
  | _, _ => false
end

mutual
theorem beq_iff (a b : Ty) : beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [beq, beq_iff, beqFields_iff]
termination_by structural a
theorem beqFields_iff (fs gs : List (String × Ty)) : beqFields fs gs = true ↔ fs = gs := by
  match fs, gs with
  | [], [] => simp [beqFields]
  | [], _ :: _ => simp [beqFields]
  | _ :: _, [] => simp [beqFields]
  | (n, s) :: fs, (m, t) :: gs => simp [beqFields, beq_iff s t, beqFields_iff fs gs]
termination_by structural fs
end

instance instDecidableEq : DecidableEq Ty := fun a b => decidable_of_iff _ (beq_iff a b)

/-- record: the single-motive eliminator, membership form, as `Store.Val.ind`
(`Store/Carrier/Val.lean:270-287`). Registered, so `induction t with | ctor … ih` works. -/
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
    (record : ∀ fields, (∀ p ∈ fields, motive p.2) → motive (.record fields)) :
    ∀ t, motive t := fun t =>
  Ty.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
    (motive_3 := fun p => motive p.2)
    never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union
    lit refOf deferredOf var unknown record
    (fun _ h => nomatch h)
    (fun _ _ ihHead ihTail => fun p hp => by
      cases hp with
      | head => exact ihHead
      | tail _ h => exact ihTail p h)
    (fun _ _ ih => ih)
    t

/-! ### Names: the UTF-8 key of a field name (`Ty.lean:142-145`'s rule) -/

/-- record: a field name's order key. -/
def nameKey (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

/-! ### Spelling, members, keys (one arm each; companions where the arm recurses) -/

mutual
/-- record arm: `{ readonly a: A; readonly b: B }`, TypeScript's object type literal. -/
def renderRaw : Ty → String
  | .never => "never"
  | .unknown => "unknown"
  | .unit => "void"
  | .nat | .int => "number"
  | .string => "string"
  | .bool => "boolean"
  | .handle target => target
  | .option inner => "Option.Option<" ++ renderRaw inner ++ ">"
  | .list inner => "ReadonlyArray<" ++ renderRaw inner ++ ">"
  | .prod left right => "readonly [" ++ renderRaw left ++ ", " ++ renderRaw right ++ "]"
  | .except error value => "Result.Result<" ++ renderRaw value ++ ", " ++ renderRaw error ++ ">"
  | .exitOf value error => "Exit.Exit<" ++ renderRaw value ++ ", " ++ renderRaw error ++ ">"
  | .causeOf error => "Cause.Cause<" ++ renderRaw error ++ ">"
  | .fiberOf value error => "Fiber.Fiber<" ++ renderRaw value ++ ", " ++ renderRaw error ++ ">"
  | .union left right => renderRaw left ++ " | " ++ renderRaw right
  | .lit value => "\"" ++ value ++ "\""
  | .refOf value => "Ref.Ref<" ++ renderRaw value ++ ">"
  | .deferredOf value error => "Deferred.Deferred<" ++ renderRaw value ++ ", " ++ renderRaw error ++ ">"
  | .var 0 => "A"
  | .var 1 => "E"
  | .var index => "T" ++ toString index
  | .record [] => "{}"
  | .record fields => "{ " ++ renderFields fields ++ " }"
/-- record: the field-list companion. -/
def renderFields : List (String × Ty) → String
  | [] => ""
  | [(n, t)] => "readonly " ++ n ++ ": " ++ renderRaw t
  | (n, t) :: rest => "readonly " ++ n ++ ": " ++ renderRaw t ++ "; " ++ renderFields rest
end

/-- record: a hand `Repr` (E1: the derived one is `partial`, which the trust gate refuses). -/
instance : Repr Ty := ⟨fun t _ => Std.Format.text (renderRaw t)⟩

/-- The members of a union, flattened at the top; `never` contributes none. record: one arm. -/
def members : Ty → List Ty
  | .never => []
  | .unknown => [.unknown]
  | .union left right => members left ++ members right
  | .unit => [.unit]
  | .nat => [.nat]
  | .int => [.int]
  | .string => [.string]
  | .bool => [.bool]
  | .handle target => [.handle target]
  | .option inner => [.option inner]
  | .list inner => [.list inner]
  | .prod left right => [.prod left right]
  | .except error value => [.except error value]
  | .exitOf value error => [.exitOf value error]
  | .causeOf error => [.causeOf error]
  | .fiberOf value error => [.fiberOf value error]
  | .lit value => [.lit value]
  | .refOf value => [.refOf value]
  | .deferredOf value error => [.deferredOf value error]
  | .var index => [.var index]
  | .record fields => [.record fields]

mutual
/-- An injective structural key. record arm: code 20, then the fields, each a length-prefixed
name key and a length-prefixed type key, the list closed by a `0` marker. -/
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
/-- record: the field-list companion. -/
def keyFields : List (String × Ty) → List Nat
  | [] => [0]
  | (n, t) :: rest =>
    1 :: (nameKey n).length :: nameKey n ++ (key t).length :: key t ++ keyFields rest
end

/-- Lexicographic order on keys, as a Boolean. unchanged. -/
def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

/-- unchanged. -/
def insertMember (t : Ty) : List Ty → List Ty
  | [] => [t]
  | u :: rest =>
    if t = u then u :: rest
    else if ltKey t.key u.key then t :: u :: rest
    else u :: insertMember t rest

/-- unchanged. -/
def ofMembers : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: rest => .union t (ofMembers rest)

private theorem utf8_key_injective {s t : String}
    (h : s.toUTF8.data.toList.map UInt8.toNat =
      t.toUTF8.data.toList.map UInt8.toNat) : s = t := by
  have bytes : s.toUTF8.data.toList = t.toUTF8.data.toList :=
    List.map_inj_right (fun _ _ he => UInt8.toNat_inj.mp he) |>.mp h
  have arrays : s.toUTF8.data = t.toUTF8.data := Array.toList_inj.mp bytes
  apply String.toByteArray_inj.mp
  exact ByteArray.ext arrays

/-- record: a length-prefixed segment determines itself and the rest. -/
private theorem prefixed_inj {a b r s : List Nat}
    (h : a.length :: (a ++ r) = b.length :: (b ++ s)) : a = b ∧ r = s := by
  simp only [List.cons.injEq] at h
  exact List.append_inj h.2 h.1

/-- record: the companion's injectivity, from the types' (the eliminator's hypothesis). -/
private theorem keyFields_injective {fs : List (String × Ty)}
    (ih : ∀ p ∈ fs, ∀ {b : Ty}, key p.2 = key b → p.2 = b) :
    ∀ {gs : List (String × Ty)}, keyFields fs = keyFields gs → fs = gs := by
  induction fs with
  | nil =>
    intro gs h
    cases gs with
    | nil => rfl
    | cons q gs =>
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
  | cons p fs ihf =>
    intro gs h
    obtain ⟨n, t⟩ := p
    cases gs with
    | nil =>
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
    | cons q gs =>
      obtain ⟨m, u⟩ := q
      simp only [keyFields, List.cons.injEq, List.append_assoc, List.cons_append] at h
      obtain ⟨hn, hrest⟩ := List.append_inj h.2.2 h.2.1
      obtain ⟨ht, hfs⟩ := prefixed_inj hrest
      have hnm : n = m := utf8_key_injective hn
      have htu : t = u := ih (n, t) List.mem_cons_self ht
      have hfg : fs = gs := ihf (fun p hp => ih p (List.mem_cons_of_mem _ hp)) hfs
      rw [hnm, htu, hfg]

/-- record: the original proof (`Ty.lean:253-276`), one goal more. -/
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
    exact congrArg Ty.record (keyFields_injective (fun p hp _ hb => ih p hp hb) h.2)

/-! ### The order: unchanged from `Ty.lean:278-400` -/

theorem ltKey_iff_lex (a b : List Nat) :
    ltKey a b = true ↔ List.Lex (· < ·) a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [ltKey]
  | cons a as ih =>
    cases b with
    | nil => simp [ltKey]
    | cons b bs =>
      rw [List.cons_lex_cons_iff]
      by_cases hab : a < b
      · simp [ltKey, hab]
      · by_cases hba : b < a
        · have hne : a ≠ b := by omega
          simp [ltKey, hab, hba, hne]
        · have he : a = b := by omega
          subst b
          simp [ltKey, ih]

private theorem lex_trichotomy (a b : List Nat) :
    List.Lex (· < ·) a b ∨ a = b ∨ List.Lex (· < ·) b a := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b bs => exact Or.inl List.Lex.nil
  | cons a as ih =>
    cases b with
    | nil => exact Or.inr (Or.inr List.Lex.nil)
    | cons b bs =>
      by_cases hab : a < b
      · exact Or.inl (List.Lex.rel hab)
      · by_cases hba : b < a
        · exact Or.inr (Or.inr (List.Lex.rel hba))
        · have he : a = b := by omega
          subst b
          rcases ih bs with hab | he | hba
          · exact Or.inl (List.Lex.cons hab)
          · exact Or.inr (Or.inl (congrArg (List.cons a) he))
          · exact Or.inr (Or.inr (List.Lex.cons hba))

instance instLT : LT Ty where
  lt a b := ltKey a.key b.key = true

instance instDecidableLT (a b : Ty) : Decidable (a < b) :=
  inferInstanceAs (Decidable (ltKey a.key b.key = true))

theorem lt_iff (a b : Ty) : a < b ↔ List.Lex (· < ·) a.key b.key :=
  ltKey_iff_lex a.key b.key

theorem lt_irrefl (a : Ty) : ¬ a < a := by
  intro h
  exact List.lex_irrefl Nat.lt_irrefl a.key ((lt_iff a a).mp h)

theorem lt_trans {a b c : Ty} (hab : a < b) (hbc : b < c) : a < c := by
  apply (lt_iff a c).mpr
  exact List.lex_trans Nat.lt_trans ((lt_iff a b).mp hab) ((lt_iff b c).mp hbc)

theorem lt_trichotomy (a b : Ty) : a < b ∨ a = b ∨ b < a := by
  rcases lex_trichotomy a.key b.key with h | h | h
  · exact Or.inl ((lt_iff a b).mpr h)
  · exact Or.inr (Or.inl (key_injective h))
  · exact Or.inr (Or.inr ((lt_iff b a).mpr h))

protected def Le (a b : Ty) : Prop := a < b ∨ a = b

instance instLE : LE Ty where
  le := Ty.Le

instance instDecidableLE (a b : Ty) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

theorem lt_asymm {a b : Ty} (h : a < b) : ¬ b < a :=
  fun reverse => lt_irrefl a (lt_trans h reverse)

theorem le_refl (a : Ty) : a ≤ a := Or.inr rfl

theorem le_trans {a b c : Ty} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with h | h
  · rcases hbc with hbc | hbc
    · exact Or.inl (lt_trans h hbc)
    · exact Or.inl (hbc ▸ h)
  · exact h ▸ hbc

theorem le_antisymm {a b : Ty} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with h | h
  · rcases hba with hba | hba
    · exact absurd hba (lt_asymm h)
    · exact hba.symm
  · exact h

theorem le_total (a b : Ty) : a ≤ b ∨ b ≤ a := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem lt_iff_le_not_le (a b : Ty) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro h
    refine ⟨Or.inl h, ?_⟩
    intro hba
    rcases hba with hba | hba
    · exact lt_asymm h hba
    · exact lt_irrefl a (hba ▸ h)
  · intro h
    rcases h.1 with hab | hab
    · exact hab
    · exact (h.2 (Or.inr hab.symm)).elim

instance instIsPreorder : Std.IsPreorder Ty where
  le_refl := Ty.le_refl
  le_trans _ _ _ := Ty.le_trans

instance instIsPartialOrder : Std.IsPartialOrder Ty where
  le_antisymm _ _ := Ty.le_antisymm

instance instIsLinearOrder : Std.IsLinearOrder Ty where
  le_total := Ty.le_total

instance instLawfulOrderLT : Std.LawfulOrderLT Ty where
  lt_iff := Ty.lt_iff_le_not_le

/-! ### Members and factors (record: one arm in `isMember`) -/

def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown | .record _ => true

theorem members_isMember {t x : Ty} (h : x ∈ members t) : isMember x = true := by
  induction t <;> simp only [members, List.mem_append, List.mem_singleton] at h
  all_goals try contradiction
  all_goals try (subst x; rfl)
  case union a b iha ihb => exact h.elim iha ihb

theorem members_atom {t : Ty} (h : isMember t = true) : members t = [t] := by
  cases t <;> simp_all [isMember, members]

theorem members_ofMembers (xs : List Ty)
    (h : ∀ x ∈ xs, isMember x = true) : members (ofMembers xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact members_atom (h x List.mem_cons_self)
    | cons y ys =>
      simp only [ofMembers, members, members_atom (h x List.mem_cons_self)]
      rw [ih (fun z hz => h z (List.mem_cons_of_mem x hz))]
      rfl

/-! ### Subtyping (record: one arm, width and depth; lookup carries membership) -/

/-- record: the first field of a name, with the evidence that it is a field. -/
def lookupField (n : String) : (fs : List (String × Ty)) → Option {s : Ty // (n, s) ∈ fs}
  | [] => none
  | (m, s) :: rest =>
    if h : m = n then some ⟨s, h ▸ List.mem_cons_self⟩
    else (lookupField n rest).map fun found => ⟨found.1, List.mem_cons_of_mem _ found.2⟩

/-- record: a field's type is smaller than its record. -/
theorem sizeOf_field_lt {n : String} {s : Ty} {fs : List (String × Ty)} (h : (n, s) ∈ fs) :
    sizeOf s < 1 + sizeOf fs := by
  have hm := List.sizeOf_lt_of_mem h
  simp only [Prod.mk.sizeOf_spec] at hm
  omega

def sub (a b : Ty) : Bool :=
  if a = b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  | _, .unknown => true
  | .lit _, .string => true
  | .option a, .option b => sub a b
  | .list a, .list b => sub a b
  | .prod a1 a2, .prod b1 b2 => sub a1 b1 && sub a2 b2
  | .except e1 a1, .except e2 a2 => sub e1 e2 && sub a1 a2
  | .exitOf a1 e1, .exitOf a2 e2 => sub a1 a2 && sub e1 e2
  | .causeOf e1, .causeOf e2 => sub e1 e2
  | .fiberOf a1 e1, .fiberOf a2 e2 => sub a1 a2 && sub e1 e2
  | .refOf a1, .refOf a2 => sub a1 a2 && sub a2 a1
  | .deferredOf a1 e1, .deferredOf a2 e2 => sub a1 a2 && sub a2 a1 && sub e1 e2 && sub e2 e1
  -- record: every field the target names is present in the source at a subtype
  | .record fs, .record gs =>
    gs.attach.all fun ⟨(n, t), hg⟩ =>
      match lookupField n fs with
      | some ⟨s, hs⟩ =>
        have := sizeOf_field_lt hs
        have := sizeOf_field_lt hg
        sub s t
      | none => false
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-! ### Normal forms (record: a field order, an insertion, two arms) -/

/-- unchanged. -/
def factors (t : Ty) : List Ty :=
  match t with
  | .never => [.never]
  | t => t.members

/-- unchanged: a record is a factor. -/
def isFactor : Ty → Bool
  | .union _ _ => false
  | _ => true

theorem factors_isFactor {t x : Ty} (h : x ∈ factors t) : isFactor x = true := by
  cases t with
  | never => simp only [factors, List.mem_singleton] at h; subst x; rfl
  | union a b =>
    have hm := members_isMember (t := .union a b) h
    cases x <;> simp_all [isMember, isFactor]
  | _ =>
    simp only [factors, members, List.mem_singleton] at h
    subst x
    rfl

theorem factors_singleton {t : Ty} (h : isFactor t = true) : factors t = [t] := by
  cases t <;> simp_all [factors, isFactor, members]

def normalizeRow (xs : List Ty) : Effect4.Row Ty :=
  ⟨Effect4.Row.antichain sub (Effect4.Row.normalize xs).elems,
    Effect4.Row.ascending_antichain sub (Effect4.Row.normalize xs).ascending⟩

theorem mem_normalizeRow (x : Ty) (xs : List Ty) :
    x ∈ (normalizeRow xs).elems ↔
      x ∈ xs ∧ ∀ y ∈ xs, sub x y = true → sub y x = true := by
  simp only [normalizeRow, Effect4.Row.mem_antichain_iff]
  change (x ∈ Effect4.Row.normalize xs ∧
    ∀ y ∈ (Effect4.Row.normalize xs).elems, sub x y = true → sub y x = true) ↔ _
  simp only [Effect4.Row.mem_normalize, ← Effect4.Row.mem_def]

def productMembers (a b : Ty) : List Ty :=
  a.factors.flatMap fun x => b.factors.map fun y => .prod x y

/-- record: fields strictly ascending by name key, hence distinct names. -/
def FieldsAscending (fs : List (String × Ty)) : Prop :=
  fs.Pairwise fun p q => ltKey (nameKey p.1) (nameKey q.1) = true

/-- record: insert a field by name; a field of the same name already present wins
(probe choice: the first occurrence of a repeated name survives `normalizeFields`). -/
def insertField (p : String × Ty) : List (String × Ty) → List (String × Ty)
  | [] => [p]
  | q :: rest =>
    if nameKey p.1 = nameKey q.1 then p :: rest
    else if ltKey (nameKey p.1) (nameKey q.1) then p :: q :: rest
    else q :: insertField p rest

mutual
/-- Deep normalization. record arm: normalize every field type, then sort by name. -/
def normalize : Ty → Ty
  | .option t => .option (normalize t)
  | .list t => .list (normalize t)
  | .prod a b => ofMembers (normalizeRow (productMembers (normalize a) (normalize b))).elems
  | .except a b => .except (normalize a) (normalize b)
  | .exitOf a b => .exitOf (normalize a) (normalize b)
  | .causeOf t => .causeOf (normalize t)
  | .fiberOf a b => .fiberOf (normalize a) (normalize b)
  | .refOf a => .refOf (normalize a)
  | .deferredOf a b => .deferredOf (normalize a) (normalize b)
  | .var i => .var i
  | .union a b => ofMembers (normalizeRow
      ((normalize a).members ++ (normalize b).members)).elems
  | .never => .never
  | .unknown => .unknown
  | .unit => .unit
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .handle s => .handle s
  | .lit s => .lit s
  | .record fs => .record (normalizeFields fs)
/-- record: the field-list companion. -/
def normalizeFields : List (String × Ty) → List (String × Ty)
  | [] => []
  | (n, t) :: rest => insertField (n, normalize t) (normalizeFields rest)
end

/-- record arm: canonical fields, each canonical. -/
inductive Normal : Ty → Prop
  | never : Normal .never
  | unknown : Normal .unknown
  | unit : Normal .unit
  | nat : Normal .nat
  | int : Normal .int
  | string : Normal .string
  | bool : Normal .bool
  | handle (s : String) : Normal (.handle s)
  | lit (s : String) : Normal (.lit s)
  | option {t} : Normal t → Normal (.option t)
  | list {t} : Normal t → Normal (.list t)
  | prod {a b} : Normal a → Normal b → isFactor a = true → isFactor b = true → Normal (.prod a b)
  | except {a b} : Normal a → Normal b → Normal (.except a b)
  | exitOf {a b} : Normal a → Normal b → Normal (.exitOf a b)
  | causeOf {t} : Normal t → Normal (.causeOf t)
  | fiberOf {a b} : Normal a → Normal b → Normal (.fiberOf a b)
  | refOf {a} : Normal a → Normal (.refOf a)
  | deferredOf {a b} : Normal a → Normal b → Normal (.deferredOf a b)
  | var (i : Nat) : Normal (.var i)
  | row (r : Effect4.Row Ty)
      (children : ∀ t ∈ r.elems, Normal t)
      (atoms : ∀ t ∈ r.elems, isMember t = true)
      (maximal : ∀ x ∈ r.elems, ∀ y ∈ r.elems, sub x y = true → sub y x = true) :
      Normal (ofMembers r.elems)
  | record {fs : List (String × Ty)} :
      (∀ p ∈ fs, Normal p.2) → FieldsAscending fs → Normal (.record fs)

theorem Normal.members {t x : Ty} (h : Normal t) (hx : x ∈ t.members) : Normal x := by
  cases h <;> try (simp only [Ty.members, List.mem_singleton] at hx; subst x; constructor <;> assumption)
  case never => exact False.elim (List.not_mem_nil hx)
  case row r children atoms maximal =>
    rw [members_ofMembers r.elems atoms] at hx
    exact children x hx

theorem Normal.factors {t x : Ty} (h : Normal t) (hx : x ∈ t.factors) : Normal x := by
  cases t with
  | never => simp only [Ty.factors, List.mem_singleton] at hx; subst x; exact h
  | _ => exact h.members hx

theorem normal_row (xs : List Ty) (hn : ∀ t ∈ xs, Normal t)
    (ha : ∀ t ∈ xs, isMember t = true) : Normal (ofMembers (normalizeRow xs).elems) := by
  apply Normal.row
  · intro t ht; exact hn t ((mem_normalizeRow t xs).mp ht).1
  · intro t ht; exact ha t ((mem_normalizeRow t xs).mp ht).1
  · intro x hx y hy hxy
    exact ((mem_normalizeRow x xs).mp hx).2 y ((mem_normalizeRow y xs).mp hy).1 hxy

/-! #### record: the field insertion's laws -/

private theorem ltKey_irrefl (a : List Nat) : ltKey a a = false := by
  cases h : ltKey a a with
  | false => rfl
  | true => exact absurd ((ltKey_iff_lex a a).mp h) (List.lex_irrefl Nat.lt_irrefl a)

private theorem ltKey_trans {a b c : List Nat} (hab : ltKey a b = true) (hbc : ltKey b c = true) :
    ltKey a c = true :=
  (ltKey_iff_lex a c).mpr
    (List.lex_trans Nat.lt_trans ((ltKey_iff_lex a b).mp hab) ((ltKey_iff_lex b c).mp hbc))

private theorem ltKey_total {a b : List Nat} (hne : a ≠ b) (hab : ltKey a b = false) :
    ltKey b a = true := by
  rcases lex_trichotomy a b with h | h | h
  · rw [(ltKey_iff_lex a b).mpr h] at hab; cases hab
  · exact absurd h hne
  · exact (ltKey_iff_lex b a).mpr h

theorem mem_insertField {p x : String × Ty} {fs : List (String × Ty)}
    (h : x ∈ insertField p fs) : x = p ∨ x ∈ fs := by
  induction fs with
  | nil => simp only [insertField, List.mem_singleton] at h; exact Or.inl h
  | cons q rest ih =>
    simp only [insertField] at h
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

/-- Every name of an insertion is the inserted name or an old one. -/
private theorem nameKey_mem_insertField {p x : String × Ty} {fs : List (String × Ty)}
    (h : x ∈ insertField p fs) : nameKey x.1 = nameKey p.1 ∨ ∃ y ∈ fs, nameKey x.1 = nameKey y.1 := by
  rcases mem_insertField h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨x, h, rfl⟩

theorem ascending_insertField (p : String × Ty) {fs : List (String × Ty)}
    (h : FieldsAscending fs) : FieldsAscending (insertField p fs) := by
  induction fs with
  | nil => exact List.pairwise_singleton _ _
  | cons q rest ih =>
    have hq := List.pairwise_cons.mp h
    simp only [insertField]
    split
    · next heq =>
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hq.2⟩
      rw [heq]; exact hq.1 y hy
    · split
      · next hne hlt =>
        refine List.pairwise_cons.mpr ⟨fun y hy => ?_, h⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hlt
        · exact ltKey_trans hlt (hq.1 y hy)
      · next hne hlt =>
        have hqp : ltKey (nameKey q.1) (nameKey p.1) = true :=
          ltKey_total hne (Bool.eq_false_iff.mpr hlt)
        refine List.pairwise_cons.mpr ⟨fun y hy => ?_, ih hq.2⟩
        rcases nameKey_mem_insertField hy with hy | ⟨z, hz, hy⟩
        · rw [hy]; exact hqp
        · rw [hy]; exact hq.1 z hz

theorem ascending_normalizeFields (fs : List (String × Ty)) :
    FieldsAscending (normalizeFields fs) := by
  induction fs with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
    obtain ⟨n, t⟩ := p
    exact ascending_insertField _ ih

theorem mem_normalizeFields {x : String × Ty} {fs : List (String × Ty)}
    (h : x ∈ normalizeFields fs) : ∃ p ∈ fs, x = (p.1, normalize p.2) := by
  induction fs with
  | nil => nomatch h
  | cons p rest ih =>
    obtain ⟨n, t⟩ := p
    rcases mem_insertField h with h | h
    · exact ⟨(n, t), List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hx⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hx⟩

/-- record: an ascending list is fixed by its own insertion of its head. -/
private theorem insertField_head {p : String × Ty} {fs : List (String × Ty)}
    (h : ∀ q ∈ fs, ltKey (nameKey p.1) (nameKey q.1) = true) : insertField p fs = p :: fs := by
  cases fs with
  | nil => rfl
  | cons q rest =>
    have hlt := h q List.mem_cons_self
    have hne : nameKey p.1 ≠ nameKey q.1 := by
      intro heq; rw [heq, ltKey_irrefl] at hlt; cases hlt
    simp only [insertField, hne, hlt, ↓reduceIte]

theorem normalizeFields_fixed (fs : List (String × Ty))
    (hf : ∀ p ∈ fs, normalize p.2 = p.2) (hasc : FieldsAscending fs) :
    normalizeFields fs = fs := by
  induction fs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨n, t⟩ := p
    have hq := List.pairwise_cons.mp hasc
    have hrest := ih (fun q hq' => hf q (List.mem_cons_of_mem _ hq')) hq.2
    simp only [normalizeFields, hrest, hf (n, t) List.mem_cons_self]
    exact insertField_head hq.1

/-- record: the original proof (`Ty.lean:677-714`), one arm more. -/
theorem normal_normalize (t : Ty) : Normal (normalize t) := by
  induction t with
  | never => exact .never
  | unknown => exact .unknown
  | unit => exact .unit
  | nat => exact .nat
  | int => exact .int
  | string => exact .string
  | bool => exact .bool
  | handle s => exact .handle s
  | lit s => exact .lit s
  | option t ih => exact .option ih
  | list t ih => exact .list ih
  | prod a b iha ihb =>
    apply normal_row
    · intro t ht
      obtain ⟨x, hx, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      exact .prod (iha.factors hx) (ihb.factors hy) (factors_isFactor hx) (factors_isFactor hy)
    · intro t ht
      obtain ⟨x, hx, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      rfl
  | except a b iha ihb => exact .except iha ihb
  | exitOf a b iha ihb => exact .exitOf iha ihb
  | causeOf t ih => exact .causeOf ih
  | fiberOf a b iha ihb => exact .fiberOf iha ihb
  | refOf a ih => exact .refOf ih
  | deferredOf a b iha ihb => exact .deferredOf iha ihb
  | var i => exact .var i
  | union a b iha ihb =>
    apply normal_row
    · intro t ht
      rcases List.mem_append.mp ht with ha | hb
      · exact iha.members ha
      · exact ihb.members hb
    · intro t ht
      exact (List.mem_append.mp ht).elim members_isMember members_isMember
  | record fs ih =>
    refine .record (fun x hx => ?_) (ascending_normalizeFields fs)
    obtain ⟨p, hp, rfl⟩ := mem_normalizeFields hx
    exact ih p hp

theorem normalize_ofMembers_fixed (xs : List Ty)
    (ha : ∀ t ∈ xs, isMember t = true)
    (hf : ∀ t ∈ xs, normalize t = t)
    (hs : Effect4.Ascending xs)
    (hm : ∀ x ∈ xs, ∀ y ∈ xs, sub x y = true → sub y x = true) :
    normalize (ofMembers xs) = ofMembers xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact hf x List.mem_cons_self
    | cons y ys =>
      have haTail := fun t ht => ha t (List.mem_cons_of_mem x ht)
      have hfTail := fun t ht => hf t (List.mem_cons_of_mem x ht)
      have hmTail := fun x hx y hy => hm x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      have tail := ih haTail hfTail (List.Pairwise.tail hs) hmTail
      change ofMembers (normalizeRow
        ((normalize x).members ++ (normalize (ofMembers (y :: ys))).members)).elems = _
      rw [hf x List.mem_cons_self, tail, members_atom (ha x List.mem_cons_self),
        members_ofMembers _ haTail]
      change ofMembers (Effect4.Row.antichain sub (Effect4.Row.normalize (x :: y :: ys)).elems) = _
      rw [Effect4.Row.normalize_of_ascending _ hs,
        (Effect4.Row.antichain_eq_self_iff sub _).mpr hm]

/-- record: the original proof (`Ty.lean:740-749`), one case more. -/
theorem Normal.fixed {t : Ty} (h : Normal t) : normalize t = t := by
  induction h <;> try (simp only [normalize, *])
  case prod a b ha hb hfa hfb iha ihb =>
    simp only [productMembers, factors_singleton hfa, factors_singleton hfb,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
    change ofMembers (Effect4.Row.antichain sub [.prod a b]) = .prod a b
    rw [Effect4.Row.antichain_singleton]
    rfl
  case row r children atoms maximal ih =>
    exact normalize_ofMembers_fixed r.elems atoms ih r.ascending maximal
  case record fs hfs hasc ih =>
    exact congrArg Ty.record (normalizeFields_fixed fs ih hasc)

theorem normalize_idem (t : Ty) : normalize (normalize t) = normalize t :=
  (normal_normalize t).fixed

/-- unchanged: the top. -/
theorem sub_unknown (t : Ty) : sub t unknown = true := by
  induction t with
  | union a b iha ihb => unfold sub; simp [iha, ihb]
  | _ => unfold sub; simp

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  simp

-- record: width (a field dropped) and depth (a field narrowed) hold; a missing field refuses.
#guard sub (.record [("id", .nat), ("name", .string)]) (.record [("id", .nat)])
#guard sub (.record [("tag", .lit "A")]) (.record [("tag", .string)])
#guard !(sub (.record [("id", .nat)]) (.record [("id", .nat), ("name", .string)]))
#guard !(sub (.record [("tag", .string)]) (.record [("tag", .lit "A")]))

def Canonical (t : Ty) : Prop := normalize t = t

end Ty

abbrev CTy := {t : Ty // Ty.Canonical t}

def CTy.ofRaw (t : Ty) : CTy := ⟨t.normalize, Ty.normalize_idem t⟩

/-! ## The value judgment, world-free (record: one arm and one companion)

`Fits` (`Laws/Program/Typed/Membership.lean:87-148`) without the arms that read a world's
declaration tables (`handle`, `fiberOf`, `refOf`, `deferredOf`, the context) and without the
cause image (`exitOf`, `causeOf`): what remains is structural on `Ty`, and so is the record
arm, because a field's type is a subterm of the record type. -/

open Effect4.Store (Val)

mutual
def FitsV (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsV x a
    | _ => False
  | .list a =>
    match v with
    | .list values => ∀ x ∈ values, FitsV x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsV x a ∧ FitsV y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsV err e
    | .ctor 1 [val] => FitsV val a
    | _ => False
  | .union l r => FitsV v l ∨ FitsV v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .unknown => True
  | .handle _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .refOf _ | .deferredOf _ _
  | .var _ => False
  -- record: the structure rule, `ctor 0` with one argument per field, in field order
  | .record fs =>
    match v with
    | .ctor 0 args => FitsFields args fs
    | _ => False
/-- record: the companion, one argument per field, exact arity. -/
def FitsFields : List Val → List (String × Ty) → Prop
  | [], [] => True
  | x :: xs, (_, t) :: rest => FitsV x t ∧ FitsFields xs rest
  | _, _ => False
end

/-! The executable check beside it (`Val.hasTy`'s shape), record arm and companion. -/
mutual
def hasTyV (v : Val) : Ty → Bool
  | .never => false
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .int => false
  | .string => match v with | .str _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .option a =>
    match v with
    | .none => true
    | .some x => hasTyV x a
    | _ => false
  | .list a =>
    match v with
    | .list values => values.attach.all fun x => hasTyV x.1 a
    | _ => false
  | .prod a b =>
    match v with
    | .list [x, y] => hasTyV x a && hasTyV y b
    | _ => false
  | .except e a =>
    match v with
    | .ctor 0 [err] => hasTyV err e
    | .ctor 1 [val] => hasTyV val a
    | _ => false
  | .union l r => hasTyV v l || hasTyV v r
  | .lit s => match v with | .str s' => s' == s | _ => false
  | .unknown => true
  | .handle _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .refOf _ | .deferredOf _ _
  | .var _ => false
  | .record fs =>
    match v with
    | .ctor 0 args => hasTyFields args fs
    | _ => false
def hasTyFields : List Val → List (String × Ty) → Bool
  | [], [] => true
  | x :: xs, (_, t) :: rest => hasTyV x t && hasTyFields xs rest
  | _, _ => false
end

/-- The connecting lemma (host-boundary §4.4: one executable check and its proof-side mirror),
by the registered eliminator: the record arm uses the field hypothesis. -/
theorem fitsV_iff_hasTyV (t : Ty) : ∀ v, FitsV v t ↔ hasTyV v t = true := by
  induction t with
  | never => intro v; simp [FitsV, hasTyV]
  | unit => intro v; cases v <;> simp [FitsV, hasTyV]
  | nat => intro v; cases v <;> simp [FitsV, hasTyV]
  | int => intro v; simp [FitsV, hasTyV]
  | string => intro v; cases v <;> simp [FitsV, hasTyV]
  | bool => intro v; cases v <;> simp [FitsV, hasTyV]
  | handle s => intro v; simp [FitsV, hasTyV]
  | option a ih => intro v; cases v <;> simp [FitsV, hasTyV, ih]
  | list a ih =>
    intro v
    cases v <;> simp [FitsV, hasTyV, ih]
  | prod a b iha ihb =>
    intro v
    simp only [FitsV, hasTyV]
    split <;> simp [iha, ihb]
  | except e a ihe iha =>
    intro v
    simp only [FitsV, hasTyV]
    split <;> simp [ihe, iha]
  | exitOf a e _ _ => intro v; simp [FitsV, hasTyV]
  | causeOf e _ => intro v; simp [FitsV, hasTyV]
  | fiberOf a e _ _ => intro v; simp [FitsV, hasTyV]
  | union l r ihl ihr => intro v; simp [FitsV, hasTyV, ihl, ihr]
  | lit s => intro v; cases v <;> simp [FitsV, hasTyV]
  | refOf a _ => intro v; simp [FitsV, hasTyV]
  | deferredOf a e _ _ => intro v; simp [FitsV, hasTyV]
  | var i => intro v; simp [FitsV, hasTyV]
  | unknown => intro v; simp [FitsV, hasTyV]
  | record fs ih =>
    intro v
    have fields : ∀ (gs : List (String × Ty)), (∀ p ∈ gs, ∀ v, FitsV v p.2 ↔ hasTyV v p.2 = true) →
        ∀ args, FitsFields args gs ↔ hasTyFields args gs = true := by
      intro gs hgs
      induction gs with
      | nil => intro args; cases args <;> simp [FitsFields, hasTyFields]
      | cons p rest ihr =>
        intro args
        obtain ⟨n, u⟩ := p
        cases args with
        | nil => simp [FitsFields, hasTyFields]
        | cons x xs =>
          simp only [FitsFields, hasTyFields, Bool.and_eq_true]
          rw [hgs (n, u) List.mem_cons_self x,
            ihr (fun q hq => hgs q (List.mem_cons_of_mem _ hq)) xs]
    simp only [FitsV, hasTyV]
    split
    · exact fields fs ih _
    · simp

/-! ## A two-field record, end to end -/

/-- `{ readonly name: string; readonly id: number }`, written out of order. -/
def user : Ty := .record [("name", .string), ("id", .nat)]

/-- Its canonical form sorts the fields by name. -/
theorem user_normalize : Ty.normalize user = .record [("id", .nat), ("name", .string)] := by
  decide

#guard Ty.renderRaw (Ty.normalize user) = "{ readonly id: number; readonly name: string }"

/-- A value of it: `ctor 0` with one argument per canonical field. -/
def ada : Val := .ctor 0 [.nat 7, .str "Ada"]

theorem ada_fits : FitsV ada (Ty.normalize user) := by
  rw [user_normalize]
  exact ⟨trivial, trivial, trivial⟩

/-- Red controls: the fields swapped, one field missing, one extra: none fits. -/
theorem swapped_not_fits : ¬ FitsV (.ctor 0 [.str "Ada", .nat 7]) (Ty.normalize user) := by
  rw [user_normalize, fitsV_iff_hasTyV]
  decide

theorem short_not_fits : ¬ FitsV (.ctor 0 [.nat 7]) (Ty.normalize user) := by
  rw [user_normalize, fitsV_iff_hasTyV]
  decide

theorem long_not_fits : ¬ FitsV (.ctor 0 [.nat 7, .str "Ada", .unit]) (Ty.normalize user) := by
  rw [user_normalize, fitsV_iff_hasTyV]
  decide

/-- A union of two records discriminated by a literal tag field (the shape `select` reads). -/
def shape : Ty :=
  .union (.record [("_tag", .lit "Circle"), ("radius", .nat)])
         (.record [("_tag", .lit "Square"), ("side", .nat)])

theorem square_fits : FitsV (.ctor 0 [.str "Square", .nat 3]) shape := by
  rw [fitsV_iff_hasTyV]
  decide

-- The canonical union keeps both records (neither is below the other) in key order; the
-- membership check agrees on it. `sub` is well-founded, so these are evaluated, not reduced.
#guard Ty.normalize shape = shape
#guard hasTyV (.ctor 0 [.str "Square", .nat 3]) (Ty.normalize shape)
#guard !(hasTyV (.ctor 0 [.str "Square", .str "3"]) (Ty.normalize shape))
-- A record below another is absorbed by the union (the antichain keeps the maximal member).
#guard Ty.normalize (.union (.record [("id", .nat), ("name", .string)]) (.record [("id", .nat)]))
  = .record [("id", .nat)]


/-! ## Width subtyping against the value encoding

`Membership.lean:837` proves `fits_sub`: membership is closed under `Ty.sub`. Under the
positional structure rule (`ctor 0 [v₁, …, vₙ]`, exact arity) and TypeScript's width rule, that
theorem is **false** for records: a value of `{ id; name }` has two arguments, and `{ id }`
wants one. The red control below proves the failure; the name-carrying encoding after it makes
the law hold again, proved by `fun_induction Ty.sub` as the tree proves it. -/

/-- Red control: `sub` says yes, the positional judgment says no. -/
theorem positional_width_unsound :
    Ty.sub (.record [("id", .nat), ("name", .string)]) (.record [("id", .nat)]) = true ∧
      FitsV (.ctor 0 [.nat 7, .str "Ada"]) (.record [("id", .nat), ("name", .string)]) ∧
      ¬ FitsV (.ctor 0 [.nat 7, .str "Ada"]) (.record [("id", .nat)]) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Ty.sub
    simp [Ty.lookupField, Ty.sub_refl]
  · exact ⟨trivial, trivial, trivial⟩
  · rw [fitsV_iff_hasTyV]; decide

/-- A name-carrying record value: one `pair (str name) value` entry per field present. -/
def entryOf (name : String) (v : Val) : Val := .pair (.str name) v

mutual
/-- The world-free judgment with a name-carrying record arm: every field the type names has
an entry of that name whose value fits; entries the type does not name are allowed (an
object may carry more properties than its type mentions). -/
def FitsN (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsN x a
    | _ => False
  | .list a =>
    match v with
    | .list values => ∀ x ∈ values, FitsN x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsN x a ∧ FitsN y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsN err e
    | .ctor 1 [val] => FitsN val a
    | _ => False
  | .union l r => FitsN v l ∨ FitsN v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .unknown => True
  | .handle _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .refOf _ | .deferredOf _ _
  | .var _ => False
  | .record fs =>
    match v with
    | .ctor 0 entries => FieldsPresent entries fs
    | _ => False
/-- Every named field has a fitting entry. -/
def FieldsPresent (entries : List Val) : List (String × Ty) → Prop
  | [] => True
  | (n, t) :: rest => (∃ w, entryOf n w ∈ entries ∧ FitsN w t) ∧ FieldsPresent entries rest
end

theorem fieldsPresent_iff (entries : List Val) (fs : List (String × Ty)) :
    FieldsPresent entries fs ↔ ∀ p ∈ fs, ∃ w, entryOf p.1 w ∈ entries ∧ FitsN w p.2 := by
  induction fs with
  | nil => simp [FieldsPresent]
  | cons p rest ih =>
    obtain ⟨n, t⟩ := p
    simp only [FieldsPresent, ih, List.mem_cons, forall_eq_or_imp]

theorem lookupField_mem {n : String} {fs : List (String × Ty)} {s : Ty}
    {h : (n, s) ∈ fs} (_ : Ty.lookupField n fs = some ⟨s, h⟩) : (n, s) ∈ fs := h

/-- **Membership is closed under `Ty.sub`**, records included, by `fun_induction Ty.sub` as
`fits_sub` is (`Membership.lean:837-939`): the record case is the new one. -/
theorem fitsN_sub {a b : Ty} (hsub : Ty.sub a b = true) : ∀ v, FitsN v a → FitsN v b := by
  fun_induction Ty.sub a b
  case case1 => intro v h; exact h
  case case2 => intro v h; exact h.elim
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    exact h.elim (iha h1 v) (ihb h2 v)
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro v h
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v h))
      (fun hx => Or.inr (ihb hx v h))
  case case5 => intro v _; trivial
  case case6 =>
    intro v h
    simp only [FitsN] at h
    split at h
    · trivial
    · exact h.elim
  case case7 x y _ ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · trivial
    · rename_i z
      exact ih hsub z h
    · exact h.elim
  case case8 x y _ ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact fun z hz => ih hsub z (h z hz)
    · exact h.elim
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · exact ⟨iha h1 _ h.1, ihb h2 _ h.2⟩
    · exact h.elim
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · exact ihe h1 _ h
    · exact iha h2 _ h
    · exact h.elim
  case case11 => intro v h; exact h.elim
  case case12 => intro v h; exact h.elim
  case case13 => intro v h; exact h.elim
  case case14 => intro v h; exact h.elim
  case case15 => intro v h; exact h.elim
  case case16 fs gs _ ih =>
    intro v h
    simp only [FitsN] at h ⊢
    split at h
    · rename_i entries
      rw [fieldsPresent_iff] at h ⊢
      intro q hq
      obtain ⟨n, t⟩ := q
      have hall := List.all_eq_true.mp hsub ⟨(n, t), hq⟩ (List.mem_attach _ _)
      simp only at hall
      cases hlook : Ty.lookupField n fs with
      | none =>
        rw [hlook] at hall
        exact Bool.noConfusion hall
      | some r =>
        obtain ⟨s, hs⟩ := r
        rw [hlook] at hall
        simp only at hall
        obtain ⟨w, hw, hfit⟩ := h (n, s) hs
        exact ⟨w, hw, ih n t hq s hs hall w hfit⟩
    · exact h.elim
  case case17 => exact Bool.noConfusion hsub

/-- The positional counterexample, read in the name-carrying encoding: the wider value fits
the narrower record. -/
theorem named_width_sound :
    FitsN (.ctor 0 [entryOf "id" (.nat 7), entryOf "name" (.str "Ada")]) (.record [("id", .nat)]) :=
  ⟨⟨.nat 7, List.mem_cons_self, trivial⟩, trivial⟩

/-- The width rule's second consequence: an entry the type does not name is unconstrained, so a
value that fits a record type can carry a handle no declaration covers. The tree's `fits_live`
(`Membership.lean:520`, membership implies declared liveness, used by `fits_sub` at `unknown`)
needs the record arm to constrain the unnamed entries too (live, or handle-free as host replies
already are since `90df5d21`). -/
theorem width_admits_unnamed_handle :
    FitsN (.ctor 0 [entryOf "id" (.nat 7), entryOf "extra" (.handle 2 3)]) (.record [("id", .nat)]) ∧
      (Val.ctor 0 [entryOf "id" (.nat 7), entryOf "extra" (.handle 2 3)]).handles ≠ [] :=
  ⟨⟨⟨.nat 7, List.mem_cons_self, trivial⟩, trivial⟩, by decide⟩

/-- The other coherent choice, exact records (no width rule: the same names in the same
canonical order, each field below): the positional structure rule keeps `fits_sub`'s record
case, and it is this short lemma over the fields, given the per-field hypothesis
`fun_induction` supplies. -/
inductive FieldsBelow : List (String × Ty) → List (String × Ty) → Prop
  | nil : FieldsBelow [] []
  | cons {n m : String} {s t : Ty} {fs gs : List (String × Ty)} :
      n = m → (∀ v, FitsV v s → FitsV v t) → FieldsBelow fs gs →
      FieldsBelow ((n, s) :: fs) ((m, t) :: gs)

theorem fitsFields_exact_mono {fs gs : List (String × Ty)} (h : FieldsBelow fs gs) :
    ∀ args, FitsFields args fs → FitsFields args gs := by
  induction h with
  | nil => intro args hf; exact hf
  | cons _ hst _ ih =>
    intro args hf
    cases args with
    | nil => exact hf.elim
    | cons x xs => exact ⟨hst x hf.1, ih xs hf.2⟩

end DataProbe.Nested

#print axioms DataProbe.Nested.Ty.beq_iff
#print axioms DataProbe.Nested.Ty.ind
#print axioms DataProbe.Nested.Ty.key_injective
#print axioms DataProbe.Nested.Ty.normal_normalize
#print axioms DataProbe.Nested.Ty.Normal.fixed
#print axioms DataProbe.Nested.Ty.normalize_idem
#print axioms DataProbe.Nested.Ty.sub_unknown
#print axioms DataProbe.Nested.fitsV_iff_hasTyV
#print axioms DataProbe.Nested.user_normalize
#print axioms DataProbe.Nested.ada_fits
#print axioms DataProbe.Nested.swapped_not_fits
#print axioms DataProbe.Nested.square_fits
#print axioms DataProbe.Nested.positional_width_unsound
#print axioms DataProbe.Nested.fitsN_sub
#print axioms DataProbe.Nested.named_width_sound
#print axioms DataProbe.Nested.width_admits_unnamed_handle
#print axioms DataProbe.Nested.fitsFields_exact_mono
