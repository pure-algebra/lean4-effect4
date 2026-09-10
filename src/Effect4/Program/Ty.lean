import Effect4.Data.Row

/-!
# The inspectable type language and its canonical API

Raw `Ty` remains first-order program data. The order transcribes the existing structural
key exactly, with constructive laws allowing reuse of `Effect4.Row`. `Normal` is an erased
proof invariant, not another stored type representation. `CTy.ofRaw` is total because deep
normalization is proved idempotent here; value-membership laws belong to the Laws graph.
-/

namespace Effect4.Program

/-! ## The type language

`Ty` is the type language of the programs this tree prints: the wire types a service row
spells plus what an `Effect<A, E, R>` needs and a row never spells: `never`, the `Exit`,
`Cause` and `Fiber` handles, and unions of error types. `render` is its TypeScript spelling;
the codegen layer reads that and adds nothing. Deep normalization recurses through every constructor; unions have members
sorted by a structural key, no duplicates, right-nested, `never` the empty union. -/

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
  /-- `Exit.Exit<A, E>`: what `Effect.exit` and `Fiber.await` answer. -/
  | exitOf (value error : Ty)
  /-- `Cause.Cause<E>`: what a `catchCause` handler receives. -/
  | causeOf (error : Ty)
  /-- `Fiber.Fiber<A, E>`: what a fork answers. -/
  | fiberOf (value error : Ty)
  | union (left right : Ty)
  | lit (value : String)
deriving DecidableEq, Repr

namespace Ty

/-- The TypeScript spelling. rc.112 has no `Either`: an `except` answer is the data reading
`Result.Result<A, E>`; a `handle` is an opaque host type whose spelling is carried verbatim. -/
def render : Ty → String
  | .never => "never"
  | .unit => "void"
  | .nat | .int => "number"
  | .string => "string"
  | .bool => "boolean"
  | .handle target => target
  | .option inner => "Option.Option<" ++ render inner ++ ">"
  | .list inner => "ReadonlyArray<" ++ render inner ++ ">"
  | .prod left right => "readonly [" ++ render left ++ ", " ++ render right ++ "]"
  | .except error value => "Result.Result<" ++ render value ++ ", " ++ render error ++ ">"
  | .exitOf value error => "Exit.Exit<" ++ render value ++ ", " ++ render error ++ ">"
  | .causeOf error => "Cause.Cause<" ++ render error ++ ">"
  | .fiberOf value error => "Fiber.Fiber<" ++ render value ++ ", " ++ render error ++ ">"
  | .union left right => render left ++ " | " ++ render right
  | .lit value => "\"" ++ value ++ "\""

/-- The members of a union, flattened at the top; `never` contributes none. -/
def members : Ty → List Ty
  | .never => []
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

/-- An injective structural key, for ordering union members: a constructor code, then the
length-prefixed keys of the components; a handle's target by its UTF-8 bytes
(`String.toUTF8` is the representation; `String.toList` and the string order reach
`Classical.choice` on this toolchain, so no member is ordered by its rendering). -/
def key : Ty → List Nat
  | .never => [0]
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

/-- Lexicographic order on keys, as a Boolean. -/
def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

/-- Insert into a list sorted by key, without duplicates. -/
def insertMember (t : Ty) : List Ty → List Ty
  | [] => [t]
  | u :: rest =>
    if t = u then u :: rest
    else if ltKey t.key u.key then t :: u :: rest
    else u :: insertMember t rest

/-- A right-nested union of the given members; none is `never`. -/
def ofMembers : List Ty → Ty
  | [] => .never
  | [t] => t
  | t :: rest => .union t (ofMembers rest)


def isNever : Ty → Bool
  | .never => true
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .union _ _
  | .lit _ => false

/-- The `Scope` service handle; its spelling is written once, here. -/
def scopeTarget : String := "Scope.Scope"
def scope : Ty := .handle scopeTarget

/-- A context handle; its spelling is written once, here. -/
def contextTarget : String := "Context.Context<unknown>"
def context : Ty := .handle contextTarget


private theorem utf8_key_injective {s t : String}
    (h : s.toUTF8.data.toList.map UInt8.toNat =
      t.toUTF8.data.toList.map UInt8.toNat) : s = t := by
  have bytes : s.toUTF8.data.toList = t.toUTF8.data.toList :=
    List.map_inj_right (fun _ _ he => UInt8.toNat_inj.mp he) |>.mp h
  have arrays : s.toUTF8.data = t.toUTF8.data := Array.toList_inj.mp bytes
  apply String.toByteArray_inj.mp
  exact ByteArray.ext arrays

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

theorem le_iff (a b : Ty) : a ≤ b ↔ a < b ∨ a = b := Iff.rfl

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

/-- A union member has neither an empty nor a union head. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ => true

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

/-- Deep normalization uses the existing canonical finite-row algebra. -/
def normalize : Ty → Ty
  | .option t => .option (normalize t)
  | .list t => .list (normalize t)
  | .prod a b => .prod (normalize a) (normalize b)
  | .except a b => .except (normalize a) (normalize b)
  | .exitOf a b => .exitOf (normalize a) (normalize b)
  | .causeOf t => .causeOf (normalize t)
  | .fiberOf a b => .fiberOf (normalize a) (normalize b)
  | .union a b => ofMembers (Effect4.Row.normalize
      ((normalize a).members ++ (normalize b).members)).elems
  | .never => .never
  | .unit => .unit
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .handle s => .handle s
  | .lit s => .lit s

/-- Proof-only construction invariant. Its row case has canonical atomic members. -/
inductive Normal : Ty → Prop
  | never : Normal .never
  | unit : Normal .unit
  | nat : Normal .nat
  | int : Normal .int
  | string : Normal .string
  | bool : Normal .bool
  | handle (s : String) : Normal (.handle s)
  | lit (s : String) : Normal (.lit s)
  | option {t} : Normal t → Normal (.option t)
  | list {t} : Normal t → Normal (.list t)
  | prod {a b} : Normal a → Normal b → Normal (.prod a b)
  | except {a b} : Normal a → Normal b → Normal (.except a b)
  | exitOf {a b} : Normal a → Normal b → Normal (.exitOf a b)
  | causeOf {t} : Normal t → Normal (.causeOf t)
  | fiberOf {a b} : Normal a → Normal b → Normal (.fiberOf a b)
  | row (r : Effect4.Row Ty)
      (children : ∀ t ∈ r.elems, Normal t)
      (atoms : ∀ t ∈ r.elems, isMember t = true) : Normal (ofMembers r.elems)

theorem Normal.members {t x : Ty} (h : Normal t) (hx : x ∈ t.members) : Normal x := by
  cases h <;> try (simp only [Ty.members, List.mem_singleton] at hx; subst x; constructor <;> assumption)
  case never => exact False.elim (List.not_mem_nil hx)
  case row r children atoms =>
    rw [members_ofMembers r.elems atoms] at hx
    exact children x hx

theorem normal_normalize (t : Ty) : Normal (normalize t) := by
  induction t with
  | never => exact .never
  | unit => exact .unit
  | nat => exact .nat
  | int => exact .int
  | string => exact .string
  | bool => exact .bool
  | handle s => exact .handle s
  | lit s => exact .lit s
  | option t ih => exact .option ih
  | list t ih => exact .list ih
  | prod a b iha ihb => exact .prod iha ihb
  | except a b iha ihb => exact .except iha ihb
  | exitOf a b iha ihb => exact .exitOf iha ihb
  | causeOf t ih => exact .causeOf ih
  | fiberOf a b iha ihb => exact .fiberOf iha ihb
  | union a b iha ihb =>
    apply Normal.row
    · intro t ht
      have ht : t ∈ (normalize a).members ++ (normalize b).members :=
        (Effect4.Row.mem_normalize t _).mp ht
      rcases List.mem_append.mp ht with ha | hb
      · exact iha.members ha
      · exact ihb.members hb
    · intro t ht
      have ht : t ∈ (normalize a).members ++ (normalize b).members :=
        (Effect4.Row.mem_normalize t _).mp ht
      exact (List.mem_append.mp ht).elim members_isMember members_isMember

theorem normalize_ofMembers_fixed (xs : List Ty)
    (ha : ∀ t ∈ xs, isMember t = true)
    (hf : ∀ t ∈ xs, normalize t = t)
    (hs : Effect4.Ascending xs) : normalize (ofMembers xs) = ofMembers xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact hf x List.mem_cons_self
    | cons y ys =>
      have haTail := fun t ht => ha t (List.mem_cons_of_mem x ht)
      have hfTail := fun t ht => hf t (List.mem_cons_of_mem x ht)
      have tail := ih haTail hfTail (List.Pairwise.tail hs)
      change ofMembers (Effect4.Row.normalize
        ((normalize x).members ++ (normalize (ofMembers (y :: ys))).members)).elems = _
      rw [hf x List.mem_cons_self, tail, members_atom (ha x List.mem_cons_self),
        members_ofMembers _ haTail]
      change ofMembers (Effect4.Row.normalize (x :: y :: ys)).elems = _
      rw [Effect4.Row.normalize_of_ascending _ hs]

theorem Normal.fixed {t : Ty} (h : Normal t) : normalize t = t := by
  induction h <;> try (simp only [normalize, *])
  case row r children atoms ih =>
    exact normalize_ofMembers_fixed r.elems atoms ih r.ascending

/-- Construction is total; no checked partial constructor is needed. -/
theorem normalize_idem (t : Ty) : normalize (normalize t) = normalize t :=
  (normal_normalize t).fixed

/-- Canonical union includes deep normalization of both inputs. -/
def join (a b : Ty) : Ty := normalize (.union a b)

/-- The API witness means equality with the computed canonical representative. -/
def Canonical (t : Ty) : Prop := normalize t = t

/-- The subtype relation on `Ty` (DI-15). Covariant in structural constructors;
unions distribute on the left and are choices on the right; string literals are
subtypes of `string`. Reflexive. -/
def sub (a b : Ty) : Bool :=
  if a = b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  | .lit _, .string => true
  | .option a, .option b => sub a b
  | .list a, .list b => sub a b
  | .prod a1 a2, .prod b1 b2 => sub a1 b1 && sub a2 b2
  | .except e1 a1, .except e2 a2 => sub e1 e2 && sub a1 a2
  | .exitOf a1 e1, .exitOf a2 e2 => sub a1 a2 && sub e1 e2
  | .causeOf e1, .causeOf e2 => sub e1 e2
  | .fiberOf a1 e1, .fiberOf a2 e2 => sub a1 a2 && sub e1 e2
  | _, _ => false
termination_by sizeOf a + sizeOf b

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  simp

theorem sub_union_right (a b1 b2 : Ty) (ha : isMember a = true) :
    sub a (.union b1 b2) = (sub a b1 || sub a b2) := by
  have hne : a ≠ .union b1 b2 := by
    rintro rfl
    contradiction
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]
  cases a <;> try contradiction
  all_goals rfl

theorem sub_union_left (a1 a2 b : Ty) (hne : union a1 a2 ≠ b) :
    sub (union a1 a2) b = (sub a1 b && sub a2 b) := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_lit_string (s : String) :
    sub (lit s) string = true := by
  have hne : lit s ≠ string := by intro h; contradiction
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_option_of_ne (a b : Ty) (hne : option a ≠ option b) :
    sub (option a) (option b) = sub a b := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_list_of_ne (a b : Ty) (hne : list a ≠ list b) :
    sub (list a) (list b) = sub a b := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_prod_of_ne (a1 a2 b1 b2 : Ty) (hne : prod a1 a2 ≠ prod b1 b2) :
    sub (prod a1 a2) (prod b1 b2) = (sub a1 b1 && sub a2 b2) := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_exitOf_of_ne (a1 e1 a2 e2 : Ty) (hne : exitOf a1 e1 ≠ exitOf a2 e2) :
    sub (exitOf a1 e1) (exitOf a2 e2) = (sub a1 a2 && sub e1 e2) := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_causeOf_of_ne (e1 e2 : Ty) (hne : causeOf e1 ≠ causeOf e2) :
    sub (causeOf e1) (causeOf e2) = sub e1 e2 := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

theorem sub_fiberOf_of_ne (a1 e1 a2 e2 : Ty) (hne : fiberOf a1 e1 ≠ fiberOf a2 e2) :
    sub (fiberOf a1 e1) (fiberOf a2 e2) = (sub a1 a2 && sub e1 e2) := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]

end Ty
end Effect4.Program

namespace Effect4.Program

abbrev CTy := {t : Ty // Ty.Canonical t}

namespace CTy

def ofRaw (t : Ty) : CTy := ⟨t.normalize, Ty.normalize_idem t⟩

def toRaw (t : CTy) : Ty := t.val

/-- Canonical union on the witnessed API. -/
def join (a b : CTy) : CTy := ofRaw (.union a.val b.val)

/-- The empty canonical union. -/
def never : CTy := ofRaw .never

@[simp] theorem ofRaw_toRaw (t : CTy) : ofRaw t.toRaw = t := by
  apply Subtype.ext
  exact t.property

end CTy
end Effect4.Program

