import P1FieldOrder
import Effect4.Data.Row

/-!
# Seat P: the copied type language with `record` and `map` appended (type-language probe, 2026-10-01)

Research probe, outside every root. A copy of `src/Effect4/Program/Ty.lean` at `bff50631`
(the inductive and the algebra functions: `key`, `ltKey`'s order, `members`, `isMember`,
`ofMembers`, `isNever`, `closed`, `instantiate`, `renderRaw`, `sub`, `factors`, `normalizeRow`,
`productMembers`, `normalize`, `Normal` and its laws) in namespace `ProbeP`, with two
constructors appended:

    | record (fields : List (String × Bool × Ty))   -- name, optional, type
    | map (key value : Ty)                          -- a keyed collection, key type string or nat

The record's field list carries the optional-key modifier from the start (rc.112 `optionalKey`,
exact: the key absent, or present with a value of the type; `Schema.optional(S)` is
`optionalKey(UndefinedOr(S))`, `vendor/effect-4.0.0-rc.112/src/Schema.ts:2496`). Row 119 as ruled
(`List (String × Ty)`) is the fragment where every flag is `false`.

The field order is `canonF := Field.canonBy fieldKey`; `fieldKey` is the discriminant-first key
(`_tag` first, then UTF-8 bytes), which question 4(c) shows a tagged union of records needs
(`P7Tagged.lean`). Every field law is proved for any key in `P1FieldOrder.lean`, so a different
key is a one-line change.

Production text copied verbatim is marked "copied"; a declaration that gained an arm or a case is
marked "arm" or "case". Two production proofs used `simp_all`/`try`, which the estate's rule bars
in a touched proof; their copies are rewritten without them and marked "rewritten".
-/

set_option autoImplicit false

namespace ProbeP

open ProbeP.Field

/-! ## The type language -/

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
  /-- A record (decisions row 119, appended, wire tag 20): fields by name, an optional-key flag,
  and a type. Canonical when strictly ascending by `fieldKey` (so names are distinct). -/
  | record (fields : List (String × Bool × Ty))
  /-- A keyed collection (decisions row 125, appended, wire tag 21): `{ readonly [k: K]: V }`. -/
  | map (key value : Ty)

namespace Ty

/-! ## The single-motive eliminator (the shape of `Store.Val.ind`; generated in production) -/

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
    (record : ∀ fields, (∀ p ∈ fields, motive p.2.2) → motive (.record fields))
    (map : ∀ key value, motive key → motive value → motive (.map key value)) :
    ∀ t, motive t := fun t =>
  Ty.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2.2)
    (motive_3 := fun p => motive p.2.2) (motive_4 := fun q => motive q.2)
    never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union
    lit refOf deferredOf var unknown record map
    (fun _ h => nomatch h)
    (fun _ _ ihHead ihTail => fun p hp => by
      cases hp with
      | head => exact ihHead
      | tail _ h => exact ihTail p h)
    (fun _ _ ih => ih)
    (fun _ _ ih => ih)
    t

/-! ## The key (arm: two), its injectivity (case: two), equality from the key -/

mutual
/-- An injective structural key. record arm: code 20, then each field as a marker, its
length-prefixed name bytes, its flag, its length-prefixed type key; `0` closes the list.
map arm: code 21, as a two-argument head. -/
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
  | .map k v => 21 :: (key k).length :: key k ++ key v
/-- The field-list companion of `key`. -/
def keyFields : List (String × Bool × Ty) → List Nat
  | [] => [0]
  | (n, o, t) :: rest =>
    1 :: (bytesKey n).length :: bytesKey n ++ (if o then 1 else 0) :: (key t).length :: key t ++
      keyFields rest
end

private theorem utf8_key_injective {s t : String}
    (h : s.toUTF8.data.toList.map UInt8.toNat =
      t.toUTF8.data.toList.map UInt8.toNat) : s = t :=
  bytesKey_injective s t h

private theorem flag_inj {o p : Bool} (h : (if o then 1 else 0 : Nat) = (if p then 1 else 0)) : o = p := by
  cases o <;> cases p
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

/-- The companion's injectivity, from the types' (the eliminator's hypothesis). -/
private theorem keyFields_injective {fs : List (String × Bool × Ty)}
    (ih : ∀ p ∈ fs, ∀ {b : Ty}, key p.2.2 = key b → p.2.2 = b) :
    ∀ {gs : List (String × Bool × Ty)}, keyFields fs = keyFields gs → fs = gs := by
  induction fs with
  | nil =>
    intro gs h
    cases gs with
    | nil => rfl
    | cons q gs =>
      obtain ⟨m, p, u⟩ := q
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
  | cons q fs ihf =>
    intro gs h
    obtain ⟨n, o, t⟩ := q
    cases gs with
    | nil =>
      simp only [keyFields] at h
      exact absurd (List.cons.inj h).1 (by decide)
    | cons r gs =>
      obtain ⟨m, p, u⟩ := r
      simp only [keyFields, List.cons.injEq, List.append_assoc, List.cons_append] at h
      obtain ⟨hn, hrest⟩ := List.append_inj h.2.2 h.2.1
      simp only [List.cons.injEq] at hrest
      obtain ⟨ho, hrest⟩ := hrest
      obtain ⟨ht, hfs⟩ := List.append_inj hrest.2 hrest.1
      have hnm : n = m := bytesKey_injective n m hn
      have hop : o = p := flag_inj ho
      have htu : t = u := ih (n, o, t) List.mem_cons_self ht
      have hfg : fs = gs := ihf (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hfs
      rw [hnm, hop, htu, hfg]

/-- rewritten: the production proof's `try` closings replaced by one arm per head; each arm's
`simp only` closes the mismatched heads (their codes differ) and leaves the matched one. -/
theorem key_injective {a b : Ty} (h : key a = key b) : a = b := by
  induction a generalizing b with
  | never =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at h
    rfl
  | unit =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | nat =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | int =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | string =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | bool =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | unknown =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | handle s =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.handle (utf8_key_injective h)
  | lit s =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.lit (utf8_key_injective h)
  | var i =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.var h.1
  | option x ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.option (ih h)
  | list x ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.list (ih h)
  | causeOf x ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.causeOf (ih h)
  | refOf x ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.refOf (ih h)
  | prod x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | except x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | exitOf x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | fiberOf x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | union x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | deferredOf x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | map x y ihx ihy =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hl, hr⟩ := List.append_inj h.2 h.1
    rw [ihx hl, ihy hr]
  | record fs ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.record (keyFields_injective (fun p hp _ hb => ih p hp hb) h)

/-- Equality decided through the injective key (production derives it, row 119 generates it). -/
instance instDecidableEq : DecidableEq Ty := fun a b =>
  decidable_of_iff (key a = key b) ⟨key_injective, fun h => h ▸ rfl⟩

/-! ## The field order -/

/-- The key the record order reads: discriminant first, then the UTF-8 bytes (question 4(c)). -/
abbrev fieldKey : String → List Nat := tagFirstKey

theorem fieldKey_injective : ∀ a b, fieldKey a = fieldKey b → a = b := tagFirstKey_injective

/-- The canonical field order of a record (a notation, so every lemma about `canonBy` applies to
it syntactically). -/
notation "canonF" => ProbeP.Field.canonBy ProbeP.Ty.fieldKey

/-- A record's head: its canonical names with their optional flags. -/
def heads (fs : List (String × Bool × Ty)) : List (String × Bool) := fs.map (fun p => (p.1, p.2.1))

/-! ## The order on `Ty` (copied, `Ty.lean:318-400`) -/

instance instLT : LT Ty where
  lt a b := Effect4.Program.Ty.ltKey a.key b.key = true

instance instDecidableLT (a b : Ty) : Decidable (a < b) :=
  inferInstanceAs (Decidable (Effect4.Program.Ty.ltKey a.key b.key = true))

theorem lt_iff (a b : Ty) : a < b ↔ List.Lex (· < ·) a.key b.key :=
  Effect4.Program.Ty.ltKey_iff_lex a.key b.key

theorem lt_irrefl (a : Ty) : ¬ a < a := by
  intro h
  exact List.lex_irrefl Nat.lt_irrefl a.key ((lt_iff a a).mp h)

theorem lt_trans {a b c : Ty} (hab : a < b) (hbc : b < c) : a < c := by
  apply (lt_iff a c).mpr
  exact List.lex_trans Nat.lt_trans ((lt_iff a b).mp hab) ((lt_iff b c).mp hbc)

theorem lt_trichotomy (a b : Ty) : a < b ∨ a = b ∨ b < a := by
  by_cases hab : Effect4.Program.Ty.ltKey a.key b.key = true
  · exact Or.inl hab
  · by_cases he : a.key = b.key
    · exact Or.inr (Or.inl (key_injective he))
    · exact Or.inr (Or.inr (ltKey_total he (Bool.eq_false_iff.mpr hab)))

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

/-! ## Members (arm: two each) -/

/-- The members of a union, flattened at the top; `never` contributes none. -/
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
  | .map k v => [.map k v]

/-- copied. -/
def ofMembers : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: rest => .union t (ofMembers rest)

/-- arm: two. -/
def isNever : Ty → Bool
  | .never => true
  | .unknown | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .union _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .record _ | .map _ _ => false

/-- A union member has neither an empty nor a union head. arm: two. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown | .record _ | .map _ _ => true

/-- copied (its text is unchanged: the eliminator's two new cases fall to the wildcards). -/
theorem members_isMember {t x : Ty} (h : x ∈ members t) : isMember x = true := by
  induction t with
  | union a b iha ihb =>
    rcases List.mem_append.mp h with h | h
    · exact iha h
    · exact ihb h
  | never => exact absurd h List.not_mem_nil
  | _ =>
    simp only [members, List.mem_singleton] at h
    subst x
    rfl

/-- rewritten: the production proof is `cases t <;> simp_all [...]`. -/
theorem members_atom {t : Ty} (h : isMember t = true) : members t = [t] := by
  cases t
  case never => exact Bool.noConfusion h
  case union a b => exact Bool.noConfusion h
  all_goals rfl

/-- copied. -/
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

/-! ## Closedness, instantiation, spelling (arm: two each; a companion for the field list) -/

mutual
/-- No template parameter inside. -/
def closed : Ty → Bool
  | .var _ => false
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ => true
  | .option t | .list t | .causeOf t | .refOf t => closed t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b
  | .map a b => closed a && closed b
  | .record fs => closedFields fs
def closedFields : List (String × Bool × Ty) → Bool
  | [] => true
  | (_, _, t) :: rest => closed t && closedFields rest
end

/-- Bindings for a template's parameters, by index. -/
abbrev Subst := List (Nat × Ty)

mutual
/-- Each parameter replaced by its binding (an unbound one by `never`). -/
def instantiate (σ : Subst) : Ty → Ty
  | .var i => (σ.lookup i).getD .never
  | .option t => .option (instantiate σ t)
  | .list t => .list (instantiate σ t)
  | .prod a b => .prod (instantiate σ a) (instantiate σ b)
  | .except a b => .except (instantiate σ a) (instantiate σ b)
  | .exitOf a b => .exitOf (instantiate σ a) (instantiate σ b)
  | .causeOf t => .causeOf (instantiate σ t)
  | .fiberOf a b => .fiberOf (instantiate σ a) (instantiate σ b)
  | .refOf t => .refOf (instantiate σ t)
  | .deferredOf a b => .deferredOf (instantiate σ a) (instantiate σ b)
  | .union a b => .union (instantiate σ a) (instantiate σ b)
  | .map a b => .map (instantiate σ a) (instantiate σ b)
  | .record fs => .record (instantiateFields σ fs)
  | .never => .never
  | .unknown => .unknown
  | .unit => .unit
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .handle s => .handle s
  | .lit s => .lit s
def instantiateFields (σ : Subst) : List (String × Bool × Ty) → List (String × Bool × Ty)
  | [] => []
  | (n, o, t) :: rest => (n, o, instantiate σ t) :: instantiateFields σ rest
end

mutual
/-- The structural TypeScript spelling. record arm: `{ readonly a: A; readonly b?: B }` in the
order given (`render` normalizes first); map arm: an index signature. -/
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
  | .map k v => "{ readonly [key: " ++ renderRaw k ++ "]: " ++ renderRaw v ++ " }"
def renderFields : List (String × Bool × Ty) → String
  | [] => ""
  | [(n, o, t)] => "readonly " ++ n ++ (if o then "?: " else ": ") ++ renderRaw t
  | (n, o, t) :: rest =>
    "readonly " ++ n ++ (if o then "?: " else ": ") ++ renderRaw t ++ "; " ++ renderFields rest
end

/-! ## Subtyping (arm: two)

The record arm compares the **canonical** field lists: equal heads (names with flags), then each
field type below its partner (TY-10's acceptance item: a permuted record is raw-below its normal
form). Exact: no width rule, and an optional key is not above a required one (their slots are
encoded differently, `P5Fits.lean`). The map arm is exact in the key and covariant in the value.
The record arm reaches each field through `List.attach`, so the termination measure sees that a
field type is a subterm. -/

theorem sizeOf_field_lt {p : String × Bool × Ty} {fs : List (String × Bool × Ty)} (h : p ∈ fs) :
    sizeOf p.2.2 < 1 + sizeOf fs := by
  have hm := List.sizeOf_lt_of_mem h
  obtain ⟨n, o, t⟩ := p
  simp only [Prod.mk.sizeOf_spec] at hm ⊢
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
  | .record fs, .record gs =>
    decide (heads (canonF fs) = heads (canonF gs)) &&
      ((canonF fs).attach.zip (canonF gs).attach).all fun pq =>
        have := sizeOf_field_lt (mem_canonBy pq.1.2)
        have := sizeOf_field_lt (mem_canonBy pq.2.2)
        sub pq.1.1.2.2 pq.2.1.2.2
  | .map k1 v1, .map k2 v2 => sub k1 k2 && sub k2 k1 && sub v1 v2
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-! ## Normal forms (arm: two; records are factors, not distributed) -/

/-- copied. -/
def factors (t : Ty) : List Ty :=
  match t with
  | .never => [.never]
  | t => t.members

/-- copied: a record and a map are factors. -/
def isFactor : Ty → Bool
  | .union _ _ => false
  | _ => true

/-- rewritten: the production proof closes with `simp_all`. -/
theorem factors_isFactor {t x : Ty} (h : x ∈ factors t) : isFactor x = true := by
  cases t with
  | never => simp only [factors, List.mem_singleton] at h; subst x; rfl
  | union a b =>
    have hm := members_isMember (t := .union a b) h
    cases x
    case union => exact Bool.noConfusion hm
    all_goals rfl
  | _ =>
    simp only [factors, members, List.mem_singleton] at h
    subst x
    rfl

/-- rewritten: the production proof is `cases t <;> simp_all [...]`. -/
theorem factors_singleton {t : Ty} (h : isFactor t = true) : factors t = [t] := by
  cases t
  case union => exact Bool.noConfusion h
  all_goals rfl

/-- copied. -/
def normalizeRow (xs : List Ty) : Effect4.Row Ty :=
  ⟨Effect4.Row.antichain sub (Effect4.Row.normalize xs).elems,
    Effect4.Row.ascending_antichain sub (Effect4.Row.normalize xs).ascending⟩

/-- copied. -/
theorem mem_normalizeRow (x : Ty) (xs : List Ty) :
    x ∈ (normalizeRow xs).elems ↔
      x ∈ xs ∧ ∀ y ∈ xs, sub x y = true → sub y x = true := by
  simp only [normalizeRow, Effect4.Row.mem_antichain_iff]
  change (x ∈ Effect4.Row.normalize xs ∧
    ∀ y ∈ (Effect4.Row.normalize xs).elems, sub x y = true → sub y x = true) ↔ _
  simp only [Effect4.Row.mem_normalize, ← Effect4.Row.mem_def]

/-- copied. -/
def productMembers (a b : Ty) : List Ty :=
  a.factors.flatMap fun x => b.factors.map fun y => .prod x y

mutual
/-- Deep normalization. record arm: normalize each field type, then the canonical field order;
map arm: both arguments. -/
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
  | .record fs => .record (canonF (normalizeFields fs))
  | .map k v => .map (normalize k) (normalize v)
def normalizeFields : List (String × Bool × Ty) → List (String × Bool × Ty)
  | [] => []
  | (n, o, t) :: rest => (n, o, normalize t) :: normalizeFields rest
end

/-- A field's payload, normalized: the flag kept, the type normalized. -/
def normPayload (c : Bool × Ty) : Bool × Ty := (c.1, normalize c.2)

/-- The companion is a payload map, so `canonBy_map` applies to it. -/
theorem normalizeFields_eq_map (fs : List (String × Bool × Ty)) :
    normalizeFields fs = fs.map (fun q => (q.1, normPayload q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [normalizeFields, ih]
    rfl

/-- Proof-only construction invariant. record arm: the fields canonical and each normal. -/
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
  | record {fs : List (String × Bool × Ty)} :
      (∀ p ∈ fs, Normal p.2.2) → Ascending fieldKey fs → Normal (.record fs)
  | map {k v} : Normal k → Normal v → Normal (.map k v)

/-- copied (text unchanged). -/
theorem Normal.members {t x : Ty} (h : Normal t) (hx : x ∈ t.members) : Normal x := by
  cases h
  case never => exact absurd hx List.not_mem_nil
  case row r children atoms maximal =>
    rw [members_ofMembers r.elems atoms] at hx
    exact children x hx
  all_goals
    simp only [Ty.members, List.mem_singleton] at hx
    subst x
    constructor <;> assumption

/-- copied. -/
theorem Normal.factors {t x : Ty} (h : Normal t) (hx : x ∈ t.factors) : Normal x := by
  cases t with
  | never => simp only [Ty.factors, List.mem_singleton] at hx; subst x; exact h
  | _ => exact h.members hx

/-- copied. -/
theorem normal_row (xs : List Ty) (hn : ∀ t ∈ xs, Normal t)
    (ha : ∀ t ∈ xs, isMember t = true) : Normal (ofMembers (normalizeRow xs).elems) := by
  apply Normal.row
  · intro t ht; exact hn t ((mem_normalizeRow t xs).mp ht).1
  · intro t ht; exact ha t ((mem_normalizeRow t xs).mp ht).1
  · intro x hx y hy hxy
    exact ((mem_normalizeRow x xs).mp hx).2 y ((mem_normalizeRow y xs).mp hy).1 hxy

/-- case: two (the record case reads `canonBy_ascending`, `mem_canonBy`, the companion's map). -/
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
    refine .record (fun x hx => ?_) (canonBy_ascending _)
    have hx' := mem_canonBy hx
    rw [normalizeFields_eq_map] at hx'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
    exact ih p hp
  | map k v ihk ihv => exact .map ihk ihv

/-- copied. -/
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

/-- A canonical field list of normal types is its own normal form. -/
theorem normalizeFields_fixed (fs : List (String × Bool × Ty))
    (hf : ∀ p ∈ fs, normalize p.2.2 = p.2.2) : normalizeFields fs = fs := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [normalizeFields, hf (n, o, t) List.mem_cons_self,
      ih (fun q hq => hf q (List.mem_cons_of_mem _ hq))]

/-- case: two. -/
theorem Normal.fixed {t : Ty} (h : Normal t) : normalize t = t := by
  induction h
  case never => rfl
  case unknown => rfl
  case unit => rfl
  case nat => rfl
  case int => rfl
  case string => rfl
  case bool => rfl
  case handle => rfl
  case lit => rfl
  case var => rfl
  case option t _ ih => rw [normalize, ih]
  case list t _ ih => rw [normalize, ih]
  case except a b _ _ iha ihb => rw [normalize, iha, ihb]
  case exitOf a b _ _ iha ihb => rw [normalize, iha, ihb]
  case causeOf t _ ih => rw [normalize, ih]
  case fiberOf a b _ _ iha ihb => rw [normalize, iha, ihb]
  case refOf a _ ih => rw [normalize, ih]
  case deferredOf a b _ _ iha ihb => rw [normalize, iha, ihb]
  case map k v _ _ ihk ihv => rw [normalize, ihk, ihv]
  case prod a b ha hb hfa hfb iha ihb =>
    simp only [normalize, iha, ihb, productMembers, factors_singleton hfa, factors_singleton hfb,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
    change ofMembers (Effect4.Row.antichain sub [.prod a b]) = .prod a b
    rw [Effect4.Row.antichain_singleton]
    rfl
  case row r children atoms maximal ih =>
    exact normalize_ofMembers_fixed r.elems atoms ih r.ascending maximal
  case record fs hfs hasc ih =>
    rw [normalize, normalizeFields_fixed fs ih]
    exact congrArg Ty.record (canonBy_of_ascending fs hasc)

/-- copied. -/
theorem normalize_idem (t : Ty) : normalize (normalize t) = normalize t :=
  (normal_normalize t).fixed

/-! ## The order's first facts (copied) -/

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  rw [if_pos rfl]

theorem sub_union_right (a b1 b2 : Ty) (ha : isMember a = true) :
    sub a (.union b1 b2) = (sub a b1 || sub a b2) := by
  have hne : a ≠ .union b1 b2 := by
    rintro rfl
    exact Bool.noConfusion ha
  conv => lhs; unfold sub
  rw [if_neg hne]
  cases a
  case never => exact Bool.noConfusion ha
  case union => exact Bool.noConfusion ha
  all_goals rfl

theorem sub_union_left (a1 a2 b : Ty) (hne : union a1 a2 ≠ b) :
    sub (union a1 a2) b = (sub a1 b && sub a2 b) := by
  conv => lhs; unfold sub
  rw [if_neg hne]

theorem sub_lit_string (s : String) :
    sub (lit s) string = true := by
  have hne : lit s ≠ string := by intro h; exact Ty.noConfusion h
  conv => lhs; unfold sub
  rw [if_neg hne]

/-- The top: every type is below `unknown`, a union memberwise. -/
theorem sub_unknown (t : Ty) : sub t unknown = true := by
  induction t with
  | union a b iha ihb =>
    rw [sub_union_left a b .unknown (fun h => Ty.noConfusion h), iha, ihb]
    rfl
  | unknown => exact sub_refl _
  | never => unfold sub; rw [if_neg (fun h => Ty.noConfusion h)]
  | _ =>
    unfold sub
    rw [if_neg (fun h => Ty.noConfusion h)]

/-- The canonical union of two types (copied). -/
def join (a b : Ty) : Ty := normalize (.union a b)

/-! ## Formation: the located refusals a record and a map add (fold-shaped scans) -/

/-- A boundary field path. -/
abbrev Path := List String

/-- The first record anywhere in the type with a repeated field name, with its path. -/
def findRepeatedField (pos : Path) : Ty → Option (Path × String)
  | .record fs =>
    match firstRepeated fs with
    | some n => some (pos, n)
    | none => findRepeatedFields pos fs
  | .option t | .list t | .causeOf t | .refOf t => findRepeatedField (pos ++ ["inner"]) t
  | .prod a b | .union a b | .except a b | .exitOf a b | .fiberOf a b | .deferredOf a b =>
    findRepeatedField (pos ++ ["left"]) a <|> findRepeatedField (pos ++ ["right"]) b
  | .map k v => findRepeatedField (pos ++ ["key"]) k <|> findRepeatedField (pos ++ ["value"]) v
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ | .var _ => none
where
  findRepeatedFields (pos : Path) : List (String × Bool × Ty) → Option (Path × String)
    | [] => none
    | (n, _, t) :: rest => findRepeatedField (pos ++ [n]) t <|> findRepeatedFields pos rest

/-- A map's key type is an open key domain: `string` or `nat` (normalized). A literal key is a
record's property, not a map's (rc.112 `SchemaAST.record`, `SchemaAST.ts:3706-3712`: literal keys
become property signatures). -/
def mapKeyOk (k : Ty) : Bool :=
  match k.normalize with
  | .string | .nat => true
  | _ => false

end Ty

/-! ## Finite controls -/

-- TY-10's positive control: a permuted record is raw-below its normal form, both ways.
#guard Ty.sub (.record [("b", false, .nat), ("a", false, .string)])
  (Ty.normalize (.record [("b", false, .nat), ("a", false, .string)]))
#guard Ty.sub (Ty.normalize (.record [("b", false, .nat), ("a", false, .string)]))
  (.record [("b", false, .nat), ("a", false, .string)])
-- depth holds; width (a field dropped or added) does not; a flag must match
#guard Ty.sub (.record [("tag", false, .lit "A")]) (.record [("tag", false, .string)])
#guard !Ty.sub (.record [("a", false, .nat), ("b", false, .string)]) (.record [("a", false, .nat)])
#guard !Ty.sub (.record [("a", false, .nat)]) (.record [("a", false, .nat), ("b", false, .string)])
#guard !Ty.sub (.record [("a", false, .nat)]) (.record [("a", true, .nat)])
#guard !Ty.sub (.record [("a", true, .nat)]) (.record [("a", false, .nat)])
-- the canonical order puts `_tag` first
#guard Ty.normalize (.record [("X", false, .nat), ("_tag", false, .lit "A")]) =
  .record [("_tag", false, .lit "A"), ("X", false, .nat)]
-- a map: exact in the key, covariant in the value
#guard Ty.sub (.map .string (.lit "a")) (.map .string .string)
#guard !Ty.sub (.map .string .string) (.map .string (.lit "a"))
#guard !Ty.sub (.map (.lit "k") .nat) (.map .string .nat)
-- formation
#guard Ty.findRepeatedField [] (.record [("a", false, .nat), ("a", false, .string)]) = some ([], "a")
#guard Ty.findRepeatedField [] (.list (.record [("x", false, .record [("b", false, .nat), ("b", true, .nat)])])) =
  some (["inner", "x"], "b")
#guard Ty.findRepeatedField [] (.record [("a", false, .nat), ("b", false, .string)]) = none
#guard Ty.mapKeyOk .string && Ty.mapKeyOk .nat && !Ty.mapKeyOk (.lit "a") && !Ty.mapKeyOk (.union (.lit "a") (.lit "b"))



end ProbeP

#print axioms ProbeP.Ty.ind
#print axioms ProbeP.Ty.key_injective
#print axioms ProbeP.Ty.lt_trichotomy
#print axioms ProbeP.Ty.members_isMember
#print axioms ProbeP.Ty.members_atom
#print axioms ProbeP.Ty.members_ofMembers
#print axioms ProbeP.Ty.factors_isFactor
#print axioms ProbeP.Ty.factors_singleton
#print axioms ProbeP.Ty.mem_normalizeRow
#print axioms ProbeP.Ty.normalizeFields_eq_map
#print axioms ProbeP.Ty.Normal.members
#print axioms ProbeP.Ty.normal_normalize
#print axioms ProbeP.Ty.normalizeFields_fixed
#print axioms ProbeP.Ty.Normal.fixed
#print axioms ProbeP.Ty.normalize_idem
#print axioms ProbeP.Ty.sub_refl
#print axioms ProbeP.Ty.sub_union_right
#print axioms ProbeP.Ty.sub_union_left
#print axioms ProbeP.Ty.sub_lit_string
#print axioms ProbeP.Ty.sub_unknown
