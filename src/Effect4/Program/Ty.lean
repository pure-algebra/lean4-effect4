import Effect4.Data.Row
import Effect4.Data.FieldOrder
import Effect4.Program.TyEq
import Effect4.Program.TyVariance

/-!
# The inspectable type language and its canonical API

Raw `Ty` remains first-order program data; its declaration is `Effect4.Program.TyCore` and its
eliminator, equality and printer are generated (`Effect4.Program.TyEq`). Its key order supports
`Effect4.Row` sorting; `CTy` exposes the subtype order on canonical representatives. `Normal` is
an erased proof invariant, not another stored type representation. `CTy.ofRaw` is total because
deep normalization is proved idempotent here; value-membership laws belong to the Laws graph.

`render` is its TypeScript spelling; the codegen layer reads that and adds nothing. Deep
normalization recurses through every constructor; unions have members sorted by a structural key,
maximal under subtyping, right-nested, `never` the empty union. Products have no union child;
normalization distributes only products. A record's fields are in canonical order (`canon`, the
names' UTF-8 bytes), a tuple of two items is a product, and a reference with no argument is a
handle.

The order's rules between two different heads that are not congruences are one table of declared
edges on leaf heads (`leafEdges`, decisions row 177), consulted by `sub` before its rows.
-/

namespace Effect4.Program

namespace Ty

open Effect4.Field (ltKey ltKey_iff_lex lex_trichotomy bytesKey bytesKey_injective)

/-- Effect rc.112 `Result.Result<A, E>` (Result.ts:66). Value first, error second,
like `exitOf` and `fiberOf`. The existing constructor and its ordinal remain unchanged. -/
abbrev result (value error : Ty) : Ty := .except error value

/-- Suffix-free spelling of `Exit.Exit<A, E>` (rc.112 Exit.ts:59). -/
abbrev exit (value error : Ty) : Ty := .exitOf value error
/-- Suffix-free spelling of `Fiber.Fiber<A, E>` (rc.112 Fiber.ts:70). -/
abbrev fiber (value error : Ty) : Ty := .fiberOf value error
/-- Suffix-free spelling of `Cause.Cause<E>` (rc.112 Cause.ts:75). -/
abbrev cause (error : Ty) : Ty := .causeOf error
/-- Both array spellings retain the existing readonly array representation. -/
abbrev array (inner : Ty) : Ty := .list inner
abbrev readonlyArray (inner : Ty) : Ty := .list inner

mutual
/-- Structural spelling, used after normalization by the public renderer. rc.112 has no `Either`:
an `except` answer is the data reading `Result.Result<A, E>`; a `handle` is an opaque host type
whose spelling is carried verbatim. A record prints its fields in the order given (`render`
normalizes first), each `readonly` and an optional one with `?`; a map prints
`Readonly<Record<K, V>>` (decisions row 125). -/
def renderRaw : Ty → String
  | .never => "never"
  | .unknown => "unknown"
  | .unit => "void"
  | .nat | .int | .number => "number"
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
  -- a template parameter, in a row's declaration only: `A`, `E`, then `T2`, `T3`, …
  | .var 0 => "A"
  | .var 1 => "E"
  | .var index => "T" ++ toString index
  | .record fields =>
    match renderFields fields with
    | [] => "{}"
    | parts => "{ " ++ String.intercalate "; " parts ++ " }"
  | .map key value => "Readonly<Record<" ++ renderRaw key ++ ", " ++ renderRaw value ++ ">>"
  | .tuple items => "readonly [" ++ String.intercalate ", " (renderItems items) ++ "]"
  | .app name args =>
    match renderItems args with
    | [] => name
    | parts => name ++ "<" ++ String.intercalate ", " parts ++ ">"
  | .null => "null"
  | .undefined => "undefined"
  | .bytes => "Uint8Array"
/-- The item-list companion of `renderRaw`: each item's spelling. -/
def renderItems : List Ty → List String
  | [] => []
  | t :: rest => renderRaw t :: renderItems rest
/-- The field-list companion of `renderRaw`: each field's spelling. -/
def renderFields : List (String × Bool × Ty) → List String
  | [] => []
  | (n, o, t) :: rest =>
    ("readonly " ++ n ++ (if o then "?: " else ": ") ++ renderRaw t) :: renderFields rest
end

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
  | .map key value => [.map key value]
  | .tuple items => [.tuple items]
  | .app name args => [.app name args]
  | .null => [.null]
  | .undefined => [.undefined]
  | .number => [.number]
  | .bytes => [.bytes]

mutual
/-- An injective structural key, for ordering union members: a constructor code, then the
length-prefixed keys of the components; a handle's target by its UTF-8 bytes
(`String.toUTF8` is the representation; `String.toList` and the string order reach
`Classical.choice` on this toolchain, so no member is ordered by its rendering). A record: code
20, then each field as a marker, its length-prefixed name bytes, its flag and its
length-prefixed type key, `0` closing the list; a tuple and a reference's arguments likewise. -/
def key : Ty → List Nat
  | .never => [0]
  | .unknown => [19]
  | .unit => [1]
  | .nat => [2]
  | .int => [3]
  | .string => [4]
  | .bool => [5]
  | .handle target => 6 :: bytesKey target
  | .option inner => 7 :: key inner
  | .list inner => 8 :: key inner
  | .prod left right => 9 :: (key left).length :: key left ++ key right
  | .except error value => 10 :: (key error).length :: key error ++ key value
  | .exitOf value error => 11 :: (key value).length :: key value ++ key error
  | .causeOf error => 12 :: key error
  | .fiberOf value error => 13 :: (key value).length :: key value ++ key error
  | .union left right => 14 :: (key left).length :: key left ++ key right
  | .lit value => 15 :: bytesKey value
  | .refOf value => 16 :: key value
  | .deferredOf value error => 17 :: (key value).length :: key value ++ key error
  | .var index => [18, index]
  | .record fields => 20 :: keyFields fields
  | .map k v => 21 :: (key k).length :: key k ++ key v
  | .tuple items => 22 :: keyItems items
  | .app name args => 23 :: (bytesKey name).length :: bytesKey name ++ keyItems args
  | .null => [24]
  | .undefined => [25]
  | .number => [26]
  | .bytes => [27]
/-- The item-list companion of `key`. -/
def keyItems : List Ty → List Nat
  | [] => [0]
  | t :: rest => 1 :: (key t).length :: key t ++ keyItems rest
/-- The field-list companion of `key`. -/
def keyFields : List (String × Bool × Ty) → List Nat
  | [] => [0]
  | (n, o, t) :: rest =>
    1 :: (bytesKey n).length :: bytesKey n ++ (if o then 1 else 0) :: (key t).length :: key t ++
      keyFields rest
end

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
  | .unknown | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .union _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _
  | .record _ | .map _ _ | .tuple _ | .app _ _ | .null | .undefined | .number | .bytes => false

mutual
/-- No template parameter inside: a program's type. `schema` is exact on closed types only
(`Schema/Bridge.lean`); the checker instantiates every row it admits, so every type it gives
a program is closed. -/
def closed : Ty → Bool
  | .var _ => false
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _
  | .null | .undefined | .number | .bytes => true
  | .option t | .list t | .causeOf t | .refOf t => closed t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b
  | .map a b => closed a && closed b
  | .record fs => closedFields fs
  | .tuple ts | .app _ ts => closedItems ts
/-- The field-list companion of `closed`. -/
def closedFields : List (String × Bool × Ty) → Bool
  | [] => true
  | (_, _, t) :: rest => closed t && closedFields rest
/-- The item-list companion of `closed`. -/
def closedItems : List Ty → Bool
  | [] => true
  | t :: rest => closed t && closedItems rest
end

/-- The field companion of `closed` reads every field's type. -/
theorem closedFields_eq_all (fs : List (String × Bool × Ty)) :
    closedFields fs = fs.all fun p => closed p.2.2 := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [closedFields, ih]
    rfl

/-- The item companion of `closed` reads every item. -/
theorem closedItems_eq_all (ts : List Ty) : closedItems ts = ts.all closed := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [closedItems, ih, List.all_cons]

/-- The `Scope` service handle; its spelling is written once, here. -/
def scopeTarget : String := "Scope.Scope"
def scope : Ty := .handle scopeTarget

/-- A context handle; its spelling is written once, here. -/
def contextTarget : String := "Context.Context<unknown>"
def context : Ty := .handle contextTarget

/-- A layer memo map handle (`Layer.MemoMap`, `Layer.ts`), internal as the scope handle is: no
source type names it, and a store row that answers one is read through a guard, which keeps only
what its intermediate type says (decisions row 187). Its spelling is written once, here. -/
def memoMapTarget : String := "Layer.MemoMap"
def memoMap : Ty := .handle memoMapTarget

/-- Nullable spellings: the `null` and `undefined` leaves (decisions row 160) in a union. -/
abbrev undefinedOr (t : Ty) : Ty := .union t .undefined
abbrev nullOr (t : Ty) : Ty := .union t .null
abbrev nullable (t : Ty) : Ty := .union t (.union .null .undefined)

/-- Effect rc.112 `Duration.Duration` (Duration.ts:84), as an opaque host handle. -/
def durationTarget : String := "Duration.Duration"
def duration : Ty := .handle durationTarget

/-- Effect rc.112 `DateTime.DateTime` (DateTime.ts:37), as an opaque host handle. -/
def dateTimeTarget : String := "DateTime.DateTime"
def dateTime : Ty := .handle dateTimeTarget

/-- The batch-or-exit shape of rc.112 `Take<A, E, Done>` (Take.ts:29).
The existing list type admits empty lists; `Stream.chunk?` enforces the
nonempty batch requirement at the pull boundary. A successful exit carries `Done`. -/
def take (a : Ty) (e : Ty := .never) (done : Ty := .unit) : Ty :=
  .union (.list a) (.exitOf done e)


private theorem flag_inj {o p : Bool} (h : (if o then 1 else 0 : Nat) = (if p then 1 else 0)) :
    o = p := by
  cases o <;> cases p
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

/-- The field companion's injectivity, from the types' (the eliminator's hypothesis). -/
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

/-- The item companion's injectivity, from the items' (the eliminator's hypothesis). -/
private theorem keyItems_injective {ts : List Ty}
    (ih : ∀ t ∈ ts, ∀ {b : Ty}, key t = key b → t = b) :
    ∀ {us : List Ty}, keyItems ts = keyItems us → ts = us := by
  induction ts with
  | nil =>
    intro us h
    cases us with
    | nil => rfl
    | cons u us =>
      simp only [keyItems] at h
      exact absurd (List.cons.inj h).1 (by decide)
  | cons t ts iht =>
    intro us h
    cases us with
    | nil =>
      simp only [keyItems] at h
      exact absurd (List.cons.inj h).1 (by decide)
    | cons u us =>
      simp only [keyItems, List.cons.injEq, List.cons_append] at h
      obtain ⟨ht, hrest⟩ := List.append_inj h.2.2 h.2.1
      rw [ih t List.mem_cons_self ht, iht (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hrest]

/-- The key is injective: one arm per head, each `simp only` closing the mismatched heads (their
codes differ) and leaving the matched one. -/
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
    exact congrArg Ty.handle (bytesKey_injective _ _ h)
  | lit s =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.lit (bytesKey_injective _ _ h)
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
  | tuple ts ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    exact congrArg Ty.tuple (keyItems_injective (fun p hp _ hb => ih p hp hb) h)
  | app n ts ih =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and, true_and] at h
    obtain ⟨hn, hrest⟩ := List.append_inj h.2 h.1
    rw [bytesKey_injective _ _ hn, keyItems_injective (fun p hp _ hb => ih p hp hb) hrest]
  | null =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | undefined =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | number =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl
  | bytes =>
    cases b <;> simp only [key, List.cons_append, List.cons.injEq, Nat.reduceEqDiff, reduceCtorEq, false_and] at h
    rfl

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
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown
  | .record _ | .map _ _ | .tuple _ | .app _ _ | .null | .undefined | .number | .bytes => true

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

theorem members_atom {t : Ty} (h : isMember t = true) : members t = [t] := by
  cases t
  case never => exact Bool.noConfusion h
  case union a b => exact Bool.noConfusion h
  all_goals rfl

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

/-! ## The canonical field order of a record (decisions rows 119, 165)

A record's fields in canonical order: ascending by the name's UTF-8 bytes, the first occurrence of
a repeated name kept (`Effect4.Field`, where every law is proved once for any key). -/

/-- The canonical field order (`Field.canonBy` at the name's UTF-8 bytes). -/
abbrev canon {β : Type} (fs : List (String × β)) : List (String × β) :=
  Field.canonBy bytesKey fs

theorem mem_canon {β : Type} {x : String × β} {fs : List (String × β)} (h : x ∈ canon fs) :
    x ∈ fs :=
  Field.mem_canonBy h

theorem canon_eq_nil {β : Type} {fs : List (String × β)} (h : canon fs = []) : fs = [] :=
  (Field.canonBy_eq_nil_iff fs).mp h

/-- A record's head: its names with their optional flags. -/
def heads (fs : List (String × Bool × Ty)) : List (String × Bool) := fs.map fun p => (p.1, p.2.1)

/-- A list zipped with itself pairs each element with itself. -/
theorem mem_zip_self {α : Type} : ∀ {l : List α} {a b : α}, (a, b) ∈ l.zip l → a = b
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, a, b, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · exact mem_zip_self h

/-- Two field lists with equal heads (names and flags, in order) pair every field with a field of
the same flag, whatever their payloads. -/
theorem zip_flag {β γ : Type} {cf : List (String × Bool × β)} {cg : List (String × Bool × γ)}
    (hh : cf.map (fun p => (p.1, p.2.1)) = cg.map (fun p => (p.1, p.2.1)))
    {p : String × Bool × β} {q : String × Bool × γ} (hpq : (p, q) ∈ cf.zip cg) : p.2.1 = q.2.1 := by
  induction cf generalizing cg with
  | nil => exact absurd hpq (by rw [List.zip_nil_left]; exact List.not_mem_nil)
  | cons a cf ih =>
    cases cg with
    | nil => exact absurd hpq (by rw [List.zip_nil_right]; exact List.not_mem_nil)
    | cons b cg =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
      rw [List.zip_cons_cons, List.mem_cons] at hpq
      rcases hpq with hpq | hpq
      · simp only [Prod.mk.injEq] at hpq
        rw [hpq.1, hpq.2]
        exact hh.1.2
      · exact ih hh.2 hpq

/-! ## The leaf order: one table of declared edges, closed reflexively and transitively

Every rule of the order between two **different** heads that is not a congruence is one relation on
*leaf heads*, read from one table, `leafEdges` (decisions row 177). `sub` consults it
(`leafRule`) before its rows; the generated view (`Laws/Program/TyView.lean`) reads the same table
and emits its laws by `decide` over the finite head domain. Adding a rule is one list element; its
membership obligation is one inclusion per edge, and the images must nest (row 121). -/

/-- The heads the leaf order relates: childless heads. A literal's leaf head forgets its payload:
every literal is below `string`, and two different literals are related by `sub`'s reflexive line
only. -/
inductive LeafHead where
  | lit
  | string
  | nat
  | int
  | number
  | undefined
  | unit
deriving DecidableEq, Repr

/-- Every leaf head: the finite domain the closure's checks range over. -/
def LeafHead.all : List LeafHead := [.lit, .string, .nat, .int, .number, .undefined, .unit]

/-- A type's leaf head, when its head is one. -/
def leafHead : Ty → Option LeafHead
  | .lit _ => some .lit
  | .string => some .string
  | .nat => some .nat
  | .int => some .int
  | .number => some .number
  | .undefined => some .undefined
  | .unit => some .unit
  | _ => none

/-- **The declared edges** (one element per rule). The number tower is two edges: `nat` below
`number` is their composite, not an entry. -/
def leafEdges : List (LeafHead × LeafHead) :=
  [ (.lit, .string)        -- a literal below its base
  , (.nat, .int)           -- decisions row 121: the number tower, over nesting images
  , (.int, .number)
  , (.undefined, .unit) ]  -- decisions row 160: `undefined` below `void`

/-- Reachability in a table of edges, with fuel. -/
def leafReach (edges : List (LeafHead × LeafHead)) : Nat → LeafHead → LeafHead → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || edges.any fun e => decide (e.1 = x) && leafReach edges n e.2 y

/-- **The leaf order**: the table's reflexive-transitive closure. The fuel is the table's length,
which bounds a path in an acyclic table (`leafLe_iff_path`, the generated view). -/
def leafLe (x y : LeafHead) : Bool := leafReach leafEdges leafEdges.length x y

/-- **The rule `sub` consults before its rows**: two types whose leaf heads differ and are related
by the leaf order. -/
def leafRule (a b : Ty) : Bool :=
  match leafHead a, leafHead b with
  | some x, some y => !decide (x = y) && leafLe x y
  | _, _ => false

/-! ## Subtyping -/

/-- A field's type is smaller than its field list. -/
theorem sizeOf_field_lt {p : String × Bool × Ty} {fs : List (String × Bool × Ty)} (h : p ∈ fs) :
    sizeOf p.2.2 < sizeOf fs := by
  have hp : sizeOf p < sizeOf fs := List.sizeOf_lt_of_mem h
  obtain ⟨n, b, t⟩ := p
  simp only [Prod.mk.sizeOf_spec] at hp
  simp only
  omega

theorem sizeOf_lt_of_mem_zip_canon {fs gs : List (String × Bool × Ty)}
    {pq : (String × Bool × Ty) × (String × Bool × Ty)}
    (h : pq ∈ (canon fs).zip (canon gs)) :
    sizeOf pq.1.2.2 + sizeOf pq.2.2.2 < 1 + sizeOf fs + (1 + sizeOf gs) := by
  have h1 := sizeOf_field_lt (mem_canon (List.of_mem_zip h).1)
  have h2 := sizeOf_field_lt (mem_canon (List.of_mem_zip h).2)
  omega

theorem sizeOf_lt_of_mem_zip {xs ys : List Ty} {pq : Ty × Ty} (h : pq ∈ xs.zip ys) :
    sizeOf pq.1 + sizeOf pq.2 < 1 + sizeOf xs + (1 + sizeOf ys) := by
  have h1 : sizeOf pq.1 < sizeOf xs := List.sizeOf_lt_of_mem (List.of_mem_zip h).1
  have h2 : sizeOf pq.2 < sizeOf ys := List.sizeOf_lt_of_mem (List.of_mem_zip h).2
  omega

theorem sizeOf_lt_of_mem_zipIdx_zip {n1 n2 : String} {xs ys : List Ty}
    {pq : (Ty × Nat) × (Ty × Nat)} (h : pq ∈ xs.zipIdx.zip ys.zipIdx) :
    sizeOf pq.1.1 + sizeOf pq.2.1 < 1 + sizeOf n1 + sizeOf xs + (1 + sizeOf n2 + sizeOf ys) := by
  have h1 : sizeOf pq.1.1 < sizeOf xs :=
    List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx (List.of_mem_zip h).1)
  have h2 : sizeOf pq.2.1 < sizeOf ys :=
    List.sizeOf_lt_of_mem (List.fst_mem_of_mem_zipIdx (List.of_mem_zip h).2)
  omega

/-- The subtype relation on `Ty` (DI-15). Covariant in structural constructors and at the
fiber handle (`Fiber<out A, out E>`); invariant at the cell and promise handles
(`Ref<in out A>`, `Deferred<in out A, in out E>`, rc.112 `Ref.ts:59`, `Deferred.ts:58`), since
a cell is written through its handle and a widened handle would admit a write the other
alias reads at the narrower type (decisions row 55); unions distribute on the left and are
choices on the right; the leaf table (`leafRule`) before the rows: a literal below `string`, the
number tower `nat ⊑ int ⊑ number`, `undefined` below `void`. A record compares its canonical
field lists: equal heads (names with flags, exact: row 178 (a)), then each field type below its
partner, with no width rule; a map is exact in the key and covariant in the value; a tuple is
pointwise at exact arity; a reference compares its name and arity, then each argument at the
named declaration's variance (`argVariance`). Reflexive. The variable-arity arms are in the form
the generated view proves (`decide (head) && (zip).attach.all …`). -/
def sub (a b : Ty) : Bool :=
  if a = b then true
  else if leafRule a b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  -- the top (decisions row 46): every type is below `unknown`
  | _, .unknown => true
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
    decide ((canon fs).map (fun p => (p.1, p.2.1)) = (canon gs).map (fun p => (p.1, p.2.1))) &&
      ((canon fs).zip (canon gs)).attach.all fun ⟨pq, h⟩ =>
        have : sizeOf pq.1.2.2 + sizeOf pq.2.2.2 < 1 + sizeOf fs + (1 + sizeOf gs) :=
          sizeOf_lt_of_mem_zip_canon h
        sub pq.1.2.2 pq.2.2.2
  | .map k1 v1, .map k2 v2 => sub k1 k2 && sub k2 k1 && sub v1 v2
  | .tuple xs, .tuple ys =>
    decide (xs.length = ys.length) &&
      (xs.zip ys).attach.all fun ⟨pq, h⟩ =>
        have : sizeOf pq.1 + sizeOf pq.2 < 1 + sizeOf xs + (1 + sizeOf ys) := sizeOf_lt_of_mem_zip h
        sub pq.1 pq.2
  | .app n1 xs, .app n2 ys =>
    decide (n1 = n2) && decide (xs.length = ys.length) &&
      (xs.zipIdx.zip ys.zipIdx).attach.all fun ⟨pq, h⟩ =>
        have : sizeOf pq.1.1 + sizeOf pq.2.1 < 1 + sizeOf n1 + sizeOf xs + (1 + sizeOf n2 + sizeOf ys) :=
          sizeOf_lt_of_mem_zipIdx_zip h
        (argVariance n1 pq.1.2).select (sub pq.1.1 pq.2.1) (sub pq.2.1 pq.1.1)
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-! ### The table's line of `sub` (the four lemmas the generated view reads) -/

/-- The table is silent when the left side has no leaf head. -/
theorem leafRule_of_left_none (a b : Ty) (h : leafHead a = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]

/-- The table is silent when the right side has no leaf head. -/
theorem leafRule_of_right_none (a b : Ty) (h : leafHead b = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]
  cases leafHead a <;> rfl

/-- The table's line of `sub`, when the table is silent. -/
theorem ite_leafRule_false {a b : Ty} {r : Bool} (h : leafRule a b = false) :
    (if leafRule a b = true then true else r) = r := by
  rw [h]
  rfl

/-- Each rule of the table is in the order. -/
theorem sub_of_leafRule {a b : Ty} (h : leafRule a b = true) : sub a b = true := by
  unfold sub
  by_cases hab : a = b
  · rw [if_pos hab]
  · rw [if_neg hab, if_pos h]

/-! ## Row templates (decisions row 42)

A row's type columns may name template parameters (`var i`); the checker binds them from the
request and instantiates the answer and error columns (`rowTy`, `Typing/Rules.lean`). The
calculus is three functions: substitution, inference, and the match, whose law is its own
guard — a match answers bindings under which the request is a subtype of the instantiated
template (`matchTemplate_sound`, `Laws/Program/Template.lean`). The atom table's `poly`
schemes read the same three (`Program/NativeAtom.lean`), with the one choice the rows never
make: `join`, how a parameter repeated across an application's arguments binds. -/

/-- Bindings for a template's parameters, by index. -/
abbrev Subst := List (Nat × Ty)

mutual
/-- Each parameter replaced by its binding. A parameter no binding names is `never`: what
TypeScript infers for a parameter the arguments leave unconstrained, which happens only on a
branch a `never` request marks as dead. -/
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
  | .tuple ts => .tuple (instantiateItems σ ts)
  | .app n ts => .app n (instantiateItems σ ts)
  | .never => .never
  | .unknown => .unknown
  | .unit => .unit
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .handle s => .handle s
  | .lit s => .lit s
  | .null => .null
  | .undefined => .undefined
  | .number => .number
  | .bytes => .bytes
/-- The field-list companion of `instantiate`. -/
def instantiateFields (σ : Subst) : List (String × Bool × Ty) → List (String × Bool × Ty)
  | [] => []
  | (n, o, t) :: rest => (n, o, instantiate σ t) :: instantiateFields σ rest
/-- The item-list companion of `instantiate`. -/
def instantiateItems (σ : Subst) : List Ty → List Ty
  | [] => []
  | t :: rest => instantiate σ t :: instantiateItems σ rest
end

/-- The field companion of `instantiate` is a map. -/
theorem instantiateFields_eq_map (σ : Subst) (fs : List (String × Bool × Ty)) :
    instantiateFields σ fs = fs.map (fun q => (q.1, q.2.1, instantiate σ q.2.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [instantiateFields, ih]
    rfl

/-- The item companion of `instantiate` is a map. -/
theorem instantiateItems_eq_map (σ : Subst) (ts : List Ty) :
    instantiateItems σ ts = ts.map (instantiate σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [instantiateItems, ih, List.map_cons]

/-- The bindings a request fixes for a template, read structurally from the seed: a
parameter binds at its first occurrence, to the request's type at that position; shapes that
do not correspond bind nothing and are left to the check.

At a parameter already bound, `join` chooses between TypeScript's two rules. Without it the
first binding stays: the rows' rule (a row spells the handle before the value it writes, so
the invariant position binds) and TypeScript's at a `NoInfer` occurrence (`getOrElse`'s
fallback). With it the binding moves to the new candidate when the bound is below it, consed
in front where `lookup` reads it first: TypeScript's own inference at an unannotated
parameter, the common supertype of the candidates (`getCommonSupertype`). Two incomparable
candidates are never joined into a union — tsgo refuses `ite(b, n, s)` at `n: number`,
`s: string` with TS2345 — so the binding stays, and the guard refuses the application too. -/
def infer (σ : Subst) (template request : Ty) (join : Bool := false) : Subst :=
  match template, request with
  | .var i, r =>
    match σ.lookup i with
    | none => σ ++ [(i, r)]
    | some bound => if join && sub bound r then (i, r) :: σ else σ
  | .option t, .option r => infer σ t r join
  | .list t, .list r => infer σ t r join
  | .causeOf t, .causeOf r => infer σ t r join
  | .refOf t, .refOf r => infer σ t r join
  | .prod a b, .prod c d => infer (infer σ a c join) b d join
  | .except a b, .except c d => infer (infer σ a c join) b d join
  | .exitOf a b, .exitOf c d => infer (infer σ a c join) b d join
  | .fiberOf a b, .fiberOf c d => infer (infer σ a c join) b d join
  | .deferredOf a b, .deferredOf c d => infer (infer σ a c join) b d join
  | .union a b, .union c d => infer (infer σ a c join) b d join
  | _, _ => σ

/-- The match of a request against a template from a seed: the bindings inference reads,
kept exactly when the request is a subtype of the template instantiated at them. The guard is
the law, so inference can only lose completeness, never soundness — whichever rule `join`
picks. -/
def matchTemplate (σ : Subst) (template request : Ty) (join : Bool := false) : Option Subst :=
  let σ' := infer σ template request join
  if sub request (instantiate σ' template) then some σ' else none

/-- Match an argument list against a parameter template list, threading the bindings each
match reads. The list-level fold of `matchTemplate`, whose guard is its own law
(`matchTemplate_sound`, `Laws/Program/Template.lean`); a longer or shorter argument list is
refused, never padded. -/
def matchTemplateArgs (σ : Subst) (params requests : List Ty) (join : Bool := false) :
    Option Subst :=
  match params, requests with
  | [], [] => some σ
  | p :: ps, r :: rs => (matchTemplate σ p r join).bind fun σ' => matchTemplateArgs σ' ps rs join
  | [], _ :: _ => none
  | _ :: _, [] => none

/-- A match fixes the argument count. The two lists walk together, and only the empty pair
answers, so an argument list of another length is refused before any guard is read. -/
theorem matchTemplateArgs_length {σ σ' : Subst} {ps rs : List Ty} {join : Bool}
    (h : matchTemplateArgs σ ps rs join = some σ') : rs.length = ps.length := by
  induction ps generalizing rs σ with
  | nil =>
    cases rs with
    | nil => rfl
    | cons _ _ => exact nomatch h
  | cons p ps ih =>
    cases rs with
    | nil => exact nomatch h
    | cons r rs =>
      simp only [matchTemplateArgs, Option.bind_eq_some_iff] at h
      obtain ⟨σ'', _, hrest⟩ := h
      simp only [List.length_cons, ih hrest]

/-- Product distribution expands union factors. An explicit `never` factor stays
explicit: this operation does not add a product-annihilation rule to subtyping. -/
def factors (t : Ty) : List Ty :=
  match t with
  | .never => [.never]
  | t => t.members

/-- A factor has no union head; its children may still contain unions. -/
def isFactor : Ty → Bool
  | .union _ _ => false
  | _ => true

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

theorem factors_singleton {t : Ty} (h : isFactor t = true) : factors t = [t] := by
  cases t
  case union => exact Bool.noConfusion h
  all_goals rfl

/-- Sort, deduplicate and retain only maximal union members. -/
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

/-- All products of the two normalized factors, before union absorption. -/
def productMembers (a b : Ty) : List Ty :=
  a.factors.flatMap fun x => b.factors.map fun y => .prod x y

/-- A tuple of normal items: two items are a product (distributed, as `prod` normalizes), any
other arity stays a tuple. -/
def normTuple : List Ty → Ty
  | [a, b] => ofMembers (normalizeRow (productMembers a b)).elems
  | items => .tuple items

/-- A reference at normal arguments: with none it is the handle at its name. -/
def normApp (name : String) : List Ty → Ty
  | [] => .handle name
  | args => .app name args

mutual
/-- Deep normalization uses the existing canonical finite-row algebra. A record normalizes each
field type, then takes the canonical field order; a tuple of two items is a product (normalized as
one); a reference with no argument is a handle. -/
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
  | .record fs => .record (canon (normalizeFields fs))
  | .map k v => .map (normalize k) (normalize v)
  | .tuple items => normTuple (normalizeItems items)
  | .app name args => normApp name (normalizeItems args)
  | .null => .null
  | .undefined => .undefined
  | .number => .number
  | .bytes => .bytes
/-- The item-list companion of `normalize`. -/
def normalizeItems : List Ty → List Ty
  | [] => []
  | t :: rest => normalize t :: normalizeItems rest
/-- The field-list companion of `normalize`. -/
def normalizeFields : List (String × Bool × Ty) → List (String × Bool × Ty)
  | [] => []
  | (n, o, t) :: rest => (n, o, normalize t) :: normalizeFields rest
end

/-- A field's payload, normalized: the flag kept, the type normalized. -/
def normPayload (c : Bool × Ty) : Bool × Ty := (c.1, normalize c.2)

/-- The field companion is a payload map, so `Field.canonBy_map` applies to it. -/
theorem normalizeFields_eq_map (fs : List (String × Bool × Ty)) :
    normalizeFields fs = fs.map (fun q => (q.1, normPayload q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [normalizeFields, ih]
    rfl

/-- The item companion is a map. -/
theorem normalizeItems_eq_map (ts : List Ty) : normalizeItems ts = ts.map normalize := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [normalizeItems, ih, List.map_cons]

/-- A record normalizes to its canonical fields with normalized types. -/
theorem normalize_record (fs : List (String × Bool × Ty)) :
    normalize (.record fs) = .record ((canon fs).map (fun q => (q.1, normPayload q.2))) := by
  rw [normalize, normalizeFields_eq_map, canon, Field.canonBy_map]

/-- A payload map keeps the heads when it keeps every flag. -/
theorem heads_normPayload (l : List (String × Bool × Ty)) :
    heads (l.map (fun q => (q.1, normPayload q.2))) = heads l := by
  simp only [heads, List.map_map]
  rfl

/-- A tuple of any arity but two normalizes its items in place. -/
theorem normalize_tuple_of_ne (ts : List Ty) (h : ts.length ≠ 2) :
    normalize (.tuple ts) = .tuple (normalizeItems ts) := by
  rw [normalize, normalizeItems_eq_map]
  match ts, h with
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl

/-- A pair tuple normalizes as the product of its items. -/
theorem normalize_tuple_pair (a b : Ty) : normalize (.tuple [a, b]) = normalize (.prod a b) := by
  rw [normalize, normalize, normalizeItems_eq_map]
  rfl

/-- A reference with arguments normalizes them in place. -/
theorem normalize_app_of_ne (n : String) (ts : List Ty) (h : ts ≠ []) :
    normalize (.app n ts) = .app n (normalizeItems ts) := by
  rw [normalize, normalizeItems_eq_map]
  match ts, h with
  | _ :: _, _ => rfl

/-- A reference with no argument is the handle at its name. -/
theorem normalize_app_nil (n : String) : normalize (.app n []) = .handle n := by
  rw [normalize]
  rfl

/-- Proof-only construction invariant. Its row case has canonical atomic members; a record's
fields are canonical (strictly ascending by name) and each normal; a tuple's arity is not two; a
reference has an argument. -/
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
      (∀ p ∈ fs, Normal p.2.2) → Field.Ascending bytesKey fs → Normal (.record fs)
  | map {k v} : Normal k → Normal v → Normal (.map k v)
  | tuple {ts : List Ty} : (∀ t ∈ ts, Normal t) → ts.length ≠ 2 → Normal (.tuple ts)
  | app {n : String} {ts : List Ty} : (∀ t ∈ ts, Normal t) → ts ≠ [] → Normal (.app n ts)
  | null : Normal .null
  | undefined : Normal .undefined
  | number : Normal .number
  | bytes : Normal .bytes

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

/-- A tuple of normal items normalizes to a normal form: a product row at arity two. -/
theorem normal_normTuple : ∀ (xs : List Ty), (∀ t ∈ xs, Normal t) → Normal (normTuple xs)
  | [a, b], h => by
    have iha := h a List.mem_cons_self
    have ihb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    apply normal_row
    · intro t ht
      obtain ⟨x, hx, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      exact .prod (iha.factors hx) (ihb.factors hy) (factors_isFactor hx) (factors_isFactor hy)
    · intro t ht
      obtain ⟨x, hx, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      rfl
  | [], h => .tuple h (by simp only [List.length_nil]; omega)
  | [_], h => .tuple h (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _ :: _, h => .tuple h (by simp only [List.length_cons]; omega)

/-- A reference at normal arguments is a normal form. -/
theorem normal_normApp (n : String) : ∀ (xs : List Ty), (∀ t ∈ xs, Normal t) → Normal (normApp n xs)
  | [], _ => .handle n
  | _ :: _, h => .app h (List.cons_ne_nil _ _)

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
    refine .record (fun x hx => ?_) (Field.canonBy_ascending _)
    have hx' := Field.mem_canonBy hx
    rw [normalizeFields_eq_map] at hx'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
    exact ih p hp
  | map k v ihk ihv => exact .map ihk ihv
  | tuple ts ih =>
    rw [normalize, normalizeItems_eq_map]
    exact normal_normTuple _ fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih u hu
  | app n ts ih =>
    rw [normalize, normalizeItems_eq_map]
    exact normal_normApp n _ fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih u hu
  | null => exact .null
  | undefined => exact .undefined
  | number => exact .number
  | bytes => exact .bytes

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
    exact congrArg Ty.record (Field.canonBy_of_ascending fs hasc)
  case tuple ts _ hlen ih =>
    rw [normalize_tuple_of_ne ts hlen, normalizeItems_eq_map]
    exact congrArg Ty.tuple ((List.map_congr_left ih).trans (List.map_id ts))
  case app n ts _ hne ih =>
    rw [normalize_app_of_ne n ts hne, normalizeItems_eq_map]
    exact congrArg (Ty.app n) ((List.map_congr_left ih).trans (List.map_id ts))
  case null => rfl
  case undefined => rfl
  case number => rfl
  case bytes => rfl

/-- Construction is total; no checked partial constructor is needed. -/
theorem normalize_idem (t : Ty) : normalize (normalize t) = normalize t :=
  (normal_normalize t).fixed

/-- Public TypeScript spelling uses the canonical type at entry. -/
def render (t : Ty) : String := renderRaw t.normalize

/-- Effect rc.112 `Chunk.Chunk<A>` (Chunk.ts:51), with its exact rendered host target.
The existing handle constructor owns identity; this is not a structural list type. -/
def chunkTarget (inner : Ty) : String := "Chunk.Chunk<" ++ render inner ++ ">"
def chunk (inner : Ty) : Ty := .handle (chunkTarget inner)

/-- Canonical union includes deep normalization of both inputs. -/
def join (a b : Ty) : Ty := normalize (.union a b)

/-- A member the tag test `tagIs tag` can be true on: a pair whose first component is the
literal `tag` (DI-39). A bare `lit tag` is not one — the atom is false on a bare string. -/
def isTagged (tag : String) : Ty → Bool
  | .prod (.lit t) _ => t == tag
  | _ => false

/-- The tag residual (DI-39, part 4 commit 3): drop every member `prod (lit tag) _`, keep
every other member, a bare `lit tag` included. On a canonical form (no union under a `prod`
head) this is a member filter and the result is canonical (`diffTag_canonical`,
`Laws/Program/Residual.lean`); `diffTag_sub` and `diffTag_sound` hold on every type. -/
def diffTag (tag : String) (t : Ty) : Ty :=
  ofMembers (t.members.filter fun m => !isTagged tag m)

/-- A column a tag decision can select on: every member is a literal-tagged pair or a
scalar (`unit`, `nat`, `int`, `string`, `bool`, a literal). Nothing else, so that a two-cell
list value can inhabit only the tagged pairs (`payload_hasTy`, `Laws/Program/Decision.lean`)
and the host's `Extract`/`Exclude` narrowing agrees with `payloadTy` and `diffTag` exactly on
these columns (`select` packet §1.8). -/
def taggedColumn (t : Ty) : Bool :=
  t.members.all fun m =>
    match m with
    | .prod (.lit _) _ => true
    | .unit | .nat | .int | .string | .bool | .lit _ => true
    | _ => false

/-- The payload of a member carrying `tag`; `none` for every other member. -/
def payloadOf (tag : String) : Ty → Option Ty
  | .prod (.lit t) p => if t = tag then some p else none
  | _ => none

/-- The union of the payloads of the members carrying `tag`, canonical; `none` when no
member does. What child 0 of a tag decision binds; `diffTag` is what child 1 binds. -/
def payloadTy (tag : String) (t : Ty) : Option Ty :=
  match t.members.filterMap (payloadOf tag) with
  | [] => none
  | ps => some (normalize (ofMembers ps))

/-- The API witness means equality with the computed canonical representative. -/
def Canonical (t : Ty) : Prop := normalize t = t

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  rw [if_pos rfl]

theorem sub_union_right (a b1 b2 : Ty) (ha : isMember a = true) :
    sub a (.union b1 b2) = (sub a b1 || sub a b2) := by
  have hne : a ≠ .union b1 b2 := by
    rintro rfl
    exact Bool.noConfusion ha
  conv => lhs; unfold sub
  rw [if_neg hne, ite_leafRule_false (leafRule_of_right_none a (.union b1 b2) rfl)]
  cases a
  case never => exact Bool.noConfusion ha
  case union => exact Bool.noConfusion ha
  all_goals rfl

theorem sub_union_left (a1 a2 b : Ty) (hne : union a1 a2 ≠ b) :
    sub (union a1 a2) b = (sub a1 b && sub a2 b) := by
  conv => lhs; unfold sub
  rw [if_neg hne, ite_leafRule_false (leafRule_of_left_none (.union a1 a2) b rfl)]

/-- The top (decisions row 46): every type is below `unknown`, a union memberwise. -/
theorem sub_unknown (t : Ty) : sub t unknown = true := by
  induction t with
  | union a b iha ihb =>
    rw [sub_union_left a b .unknown (fun h => Ty.noConfusion h), iha, ihb]
    rfl
  | unknown => exact sub_refl _
  | _ =>
    unfold sub
    rw [if_neg (fun h => Ty.noConfusion h), ite_leafRule_false (leafRule_of_right_none _ .unknown rfl)]

/-- A literal is below `string`: the leaf table's first edge. -/
theorem sub_lit_string (s : String) :
    sub (lit s) string = true :=
  sub_of_leafRule rfl

/-! ## Formation: the located refusals a record and a map add -/

/-- A boundary field path. -/
abbrev Path := List String

mutual
/-- The first record anywhere in the type with a repeated field name, with its path (decisions
row 119: repeated names refused at formation; `Field.firstRepeated_eq_none_iff`). -/
def findRepeatedField (pos : Path) : Ty → Option (Path × String)
  | .record fs =>
    match Field.firstRepeated fs with
    | some n => some (pos, n)
    | none => findRepeatedFields pos fs
  | .option t | .list t | .causeOf t | .refOf t => findRepeatedField (pos ++ ["inner"]) t
  | .prod a b | .union a b | .except a b | .exitOf a b | .fiberOf a b | .deferredOf a b =>
    findRepeatedField (pos ++ ["left"]) a <|> findRepeatedField (pos ++ ["right"]) b
  | .map k v => findRepeatedField (pos ++ ["key"]) k <|> findRepeatedField (pos ++ ["value"]) v
  | .tuple ts | .app _ ts => findRepeatedItems pos 0 ts
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ | .var _
  | .null | .undefined | .number | .bytes => none
/-- The field-list companion of `findRepeatedField`. -/
def findRepeatedFields (pos : Path) : List (String × Bool × Ty) → Option (Path × String)
  | [] => none
  | (n, _, t) :: rest => findRepeatedField (pos ++ [n]) t <|> findRepeatedFields pos rest
/-- The item-list companion of `findRepeatedField`. -/
def findRepeatedItems (pos : Path) (i : Nat) : List Ty → Option (Path × String)
  | [] => none
  | t :: rest => findRepeatedField (pos ++ [toString i]) t <|> findRepeatedItems pos (i + 1) rest
end

/-- A map's key type is `string` (decisions row 125 as ruled: string-keyed maps in the wave). A
literal key is a record's property, not a map's (rc.112 `SchemaAST.record`, literal keys become
property signatures); any other key type is refused until DI-78 freezes its contract. -/
def mapKeyOk (k : Ty) : Bool := decide (k.normalize = .string)

end Ty
end Effect4.Program

namespace Effect4.Program

abbrev CTy := {t : Ty // Ty.Canonical t}

namespace CTy

def ofRaw (t : Ty) : CTy := ⟨t.normalize, Ty.normalize_idem t⟩

def toRaw (t : CTy) : Ty := t.val

/-- Type identity keys use the canonical representative. Raw `Ty.key` remains injective. -/
def key : CTy → List Nat := Ty.key ∘ toRaw

/-- Public type order is structural subtyping between canonical representatives. -/
instance : LE CTy := ⟨fun a b => Ty.sub a.toRaw b.toRaw = true⟩
instance : DecidableRel (fun a b : CTy => a ≤ b) := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))
instance : LT CTy := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableRel (fun a b : CTy => a < b) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ ¬ _))

/-- Canonical union on the witnessed API. -/
def join (a b : CTy) : CTy := ofRaw (.union a.val b.val)

instance : Max CTy := ⟨join⟩

/-- The empty canonical union. -/
def never : CTy := ofRaw .never
def unknown : CTy := ofRaw .unknown

@[simp] theorem ofRaw_toRaw (t : CTy) : ofRaw t.toRaw = t := by
  apply Subtype.ext
  exact t.property

theorem key_injective {a b : CTy} (h : key a = key b) : a = b :=
  Subtype.ext (Ty.key_injective h)

/-- Printing observes the canonical representative. -/
def render (t : CTy) : String := Ty.render t.toRaw

theorem render_toRaw (t : CTy) : render t = Ty.renderRaw t.toRaw := by
  exact congrArg Ty.renderRaw t.property

end CTy
end Effect4.Program
