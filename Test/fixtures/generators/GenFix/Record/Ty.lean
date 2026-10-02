import GenFix.Record.TyEq

/-!
# GenFix.Record.Ty — the functions the generators read, over the record fixture (a generator fixture)

Copied from `src/Effect4/Program/Ty.lean` at `74dae8d2`, each with a record arm; probe Q's
`Q/probe/ProbeQ/Ty.lean`, renamed and with every proof written without `simp_all` or `try`.
What is here is what the generated groups and the `fold_of` scan read:

* `canon` (generic in the value), `mem_canon`, `canon_eq_nil`: the canonical field order the view
  reads a field-list head through (`tools/Effect4Gen/View.lean` refuses a field-list head when
  they are missing);
* `sub` with the record arm in the form the generated arm lemma proves
  (`decide (names) && (zip).attach.all …`, termination by an in-body `have`);
* `members`, `isNever`, `isMember`, `renderRaw`/`renderFields`, `closed`/`closedFields`: the
  traversals `fold_of` is run on (`GenFix.Record.FoldOfScan`), two of them through a sibling over
  the field list `List (String × Ty)`.

`DecidableEq Ty` and `Repr Ty` are the generated ones (`GenFix.Record.TyEq`).
-/

set_option autoImplicit false

namespace GenFix.Record
namespace Ty

mutual
/-- Structural spelling; the record arm prints TypeScript's object type literal in written order. -/
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
  | .record fields => "{ " ++ renderFields fields ++ "}"
/-- The record arm's sibling over the field list: `readonly a: A; ` per field. -/
def renderFields : List (String × Ty) → String
  | [] => ""
  | (n, t) :: rest => "readonly " ++ n ++ ": " ++ renderRaw t ++ "; " ++ renderFields rest
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

/-- Lexicographic order on keys, as a Boolean. -/
def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

/-- A field name's order key: its UTF-8 bytes. -/
def nameKey (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

/-- Insert a field by its name's key; an existing equal name wins (a left fold keeps the first). -/
def insertField {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs =>
    if ltKey (nameKey p.1) (nameKey q.1) then p :: q :: qs
    else if p.1 = q.1 then q :: qs
    else q :: insertField p qs

/-- Canonical field order: ascending by the name's UTF-8 key, the first of a repeated name kept.
Generic in the value, so an algebra's carriers are ordered by the same rule. -/
def canon {α : Type} (fs : List (String × α)) : List (String × α) :=
  fs.foldl (fun acc p => insertField p acc) []

theorem mem_insertField {α : Type} {p x : String × α} {l : List (String × α)}
    (h : x ∈ insertField p l) : x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [insertField, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    unfold insertField at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem q h)

theorem mem_foldl_insertField {α : Type} {x : String × α} :
    ∀ (fs acc : List (String × α)), x ∈ fs.foldl (fun acc p => insertField p acc) acc →
      x ∈ fs ∨ x ∈ acc
  | [], _, h => Or.inr h
  | f :: fs, acc, h => by
    rcases mem_foldl_insertField fs (insertField f acc) h with h | h
    · exact Or.inl (List.mem_cons_of_mem f h)
    · rcases mem_insertField h with h | h
      · exact Or.inl (h ▸ List.mem_cons_self)
      · exact Or.inr h

/-- Every field of the canonical order is a field of the record. -/
theorem mem_canon {α : Type} {x : String × α} {fs : List (String × α)} (h : x ∈ canon fs) :
    x ∈ fs := by
  rcases mem_foldl_insertField fs [] h with h | h
  · exact h
  · exact absurd h List.not_mem_nil

theorem insertField_ne_nil {α : Type} (p : String × α) (l : List (String × α)) :
    insertField p l ≠ [] := by
  cases l with
  | nil => exact List.cons_ne_nil p []
  | cons q qs =>
    unfold insertField
    split
    · exact List.cons_ne_nil _ _
    · split
      · exact List.cons_ne_nil _ _
      · exact List.cons_ne_nil _ _

theorem foldl_insertField_ne_nil {α : Type} :
    ∀ (fs acc : List (String × α)), acc ≠ [] → fs.foldl (fun acc p => insertField p acc) acc ≠ []
  | [], _, h => h
  | f :: fs, acc, _ => foldl_insertField_ne_nil fs (insertField f acc) (insertField_ne_nil f acc)

/-- Only the empty record has no canonical field. -/
theorem canon_eq_nil {α : Type} {fs : List (String × α)} (h : canon fs = []) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs => exact absurd h (foldl_insertField_ne_nil fs (insertField f []) (insertField_ne_nil f []))

/-- A field's type is smaller than its record: the measure `sub`'s record arm decreases by. -/
theorem sizeOf_snd_lt_of_mem {x : String × Ty} {fs : List (String × Ty)} (h : x ∈ fs) :
    sizeOf x.2 < sizeOf fs := by
  have hx : sizeOf x < sizeOf fs := List.sizeOf_lt_of_mem h
  obtain ⟨n, t⟩ := x
  simp only [Prod.mk.sizeOf_spec] at hx
  simp only
  omega

theorem sizeOf_lt_of_mem_zip_canon {fs gs : List (String × Ty)} {pq : (String × Ty) × (String × Ty)}
    (h : pq ∈ (canon fs).zip (canon gs)) :
    sizeOf pq.1.2 + sizeOf pq.2.2 < 1 + sizeOf fs + (1 + sizeOf gs) := by
  have h1 := sizeOf_snd_lt_of_mem (mem_canon (List.of_mem_zip h).1)
  have h2 := sizeOf_snd_lt_of_mem (mem_canon (List.of_mem_zip h).2)
  omega

def isNever : Ty → Bool
  | .never => true
  | .unknown | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .union _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .record _ => false

mutual
/-- No template parameter inside. -/
def closed : Ty → Bool
  | .var _ => false
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ => true
  | .option t | .list t | .causeOf t | .refOf t => closed t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b =>
    closed a && closed b
  | .record fields => closedFields fields
/-- The record arm's sibling over the field list. -/
def closedFields : List (String × Ty) → Bool
  | [] => true
  | (_, t) :: rest => closed t && closedFields rest
end

mutual
/-- The field types a record carries, outermost first; a paramorphism through the field list
(its sibling keeps each field's type as a value and recurses into it). -/
def fieldTys : Ty → List Ty
  | .record fields => fieldTysOf fields
  | .option t | .list t => fieldTys t
  | _ => []
/-- The record arm's sibling over the field list. -/
def fieldTysOf : List (String × Ty) → List Ty
  | [] => []
  | (_, t) :: rest => t :: (fieldTys t ++ fieldTysOf rest)
end

/-- A union member has neither an empty nor a union head. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown | .record _ => true

/-- The subtype relation of `Ty.lean:437`, with the record arm: exact (the canonical name lists
equal, each field below its partner); width is not a rule. -/
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
    decide ((canon fs).map Prod.fst = (canon gs).map Prod.fst) &&
      ((canon fs).zip (canon gs)).attach.all fun ⟨pq, h⟩ =>
        have : sizeOf pq.1.2 + sizeOf pq.2.2 < 1 + sizeOf fs + (1 + sizeOf gs) :=
          sizeOf_lt_of_mem_zip_canon h
        sub pq.1.2 pq.2.2
  | _, _ => false
termination_by sizeOf a + sizeOf b

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  rw [if_pos rfl]

/-! Finite controls on the record arm: TY-10's positive control (a permuted record is
raw-below its canonical order, both ways), depth, the exact rule's refusals. -/

#guard sub (.record [("a", .lit "x"), ("b", .nat)]) (.record [("b", .nat), ("a", .lit "x")])
#guard sub (.record [("b", .nat), ("a", .lit "x")]) (.record [("a", .lit "x"), ("b", .nat)])
#guard sub (.record [("a", .lit "x"), ("b", .nat)]) (.record [("b", .nat), ("a", .string)])
#guard !sub (.record [("a", .string)]) (.record [("a", .lit "x")])
#guard !sub (.record [("a", .lit "x"), ("b", .nat)]) (.record [("a", .lit "x")])
#guard !sub (.record [("a", .nat)]) (.record [("c", .nat)])
#guard canon [("b", 1), ("a", 2), ("b", 3)] = [("a", 2), ("b", 1)]
#guard renderRaw (.record [("a", .lit "x"), ("b", .nat)]) = "{ readonly a: \"x\"; readonly b: number; }"

end Ty
end GenFix.Record
