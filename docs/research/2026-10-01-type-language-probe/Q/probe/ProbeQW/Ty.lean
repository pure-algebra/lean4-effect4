import ProbeQW.TyEq
import ProbeQW.TyVariance

/-!
# ProbeQW.Ty — the functions the generated folds and view read, over the whole wave append

Seat Q probe (2026-10-01). As `ProbeQ.Ty`, for the wave family: `canon` (generic in the value),
its membership facts, `isMember`, `members`, and `sub` with one arm per new congruence head, each
written in the form the generated view's arm lemma reads (seat P owns the rules themselves):

* `record`: the canonical payloads `(name, optional)` equal, each field below, in canonical
  order (exact; a modifier is payload, so a required field is not below an optional one);
* `map`: key invariant, value covariant (the variance row `[inv, co]`);
* `tuple`: the arities equal, each item below, by position;
* `app`: the names equal, the arities equal, each argument at the name's declared variance
  (`argVariance`, generated from rc.112's declarations), through `Variance.select`.
-/

set_option autoImplicit false

namespace ProbeQW
namespace Ty

def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

def nameKey (s : String) : List Nat := s.toUTF8.data.toList.map UInt8.toNat

def insertField {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs =>
    if ltKey (nameKey p.1) (nameKey q.1) then p :: q :: qs
    else if p.1 = q.1 then q :: qs
    else q :: insertField p qs

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

theorem canon_eq_nil {α : Type} {fs : List (String × α)} (h : canon fs = []) : fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs => exact absurd h (foldl_insertField_ne_nil fs (insertField f []) (insertField_ne_nil f []))

/-! The measures the well-founded arms decrease by. -/

theorem sizeOf_field_lt {p : String × Ty × Bool} {fs : List (String × Ty × Bool)} (h : p ∈ fs) :
    sizeOf p.2.1 < sizeOf fs := by
  have hp : sizeOf p < sizeOf fs := List.sizeOf_lt_of_mem h
  obtain ⟨n, t, b⟩ := p
  simp only [Prod.mk.sizeOf_spec] at hp
  simp only
  omega

theorem sizeOf_lt_of_mem_zip_canon {fs gs : List (String × Ty × Bool)}
    {pq : (String × Ty × Bool) × (String × Ty × Bool)}
    (h : pq ∈ (canon fs).zip (canon gs)) :
    sizeOf pq.1.2.1 + sizeOf pq.2.2.1 < 1 + sizeOf fs + (1 + sizeOf gs) := by
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

def members : Ty → List Ty
  | .never => []
  | .union left right => members left ++ members right
  | t => [t]

/-- A union member has neither an empty nor a union head. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown
  | .record _ | .map _ _ | .tuple _ | .app _ _ | .null | .undefined | .number | .bytes => true

/-- `Ty.lean:437` with the wave's four congruence arms and the order's leaf edges as data: the
five structural rules in the rule table's order, the congruences, then the catch-all answers the
generated `edgeRule` (`ProbeQW.TyVariance`), so `lit ⊑ string` is a row of the table, not an arm,
and a new edge (`undefined ⊑ unit`, the number tower) is a row too. -/
def sub (a b : Ty) : Bool :=
  if a = b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
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
    decide ((canon fs).map (fun p => (p.1, p.2.2)) = (canon gs).map (fun p => (p.1, p.2.2))) &&
      ((canon fs).zip (canon gs)).attach.all fun ⟨pq, h⟩ =>
        have : sizeOf pq.1.2.1 + sizeOf pq.2.2.1 < 1 + sizeOf fs + (1 + sizeOf gs) :=
          sizeOf_lt_of_mem_zip_canon h
        sub pq.1.2.1 pq.2.2.1
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
  | _, _ => edgeRule a b
termination_by sizeOf a + sizeOf b

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  simp

/-- `Ty.lean:767`, text unchanged, on the whole wave. -/
theorem sub_unknown (t : Ty) : sub t unknown = true := by
  induction t with
  | union a b iha ihb => unfold sub; simp [iha, ihb]
  | _ => unfold sub; simp

#guard sub (.record [("b", .nat, false), ("a", .bool, true)]) (.record [("a", .bool, true), ("b", .nat, false)])
#guard !sub (.record [("a", .nat, false)]) (.record [("a", .nat, true)])
#guard sub (.tuple [.lit "x", .nat]) (.tuple [.string, .nat])
#guard !sub (.tuple [.nat]) (.tuple [.nat, .nat])
#guard sub (.app "Fiber.Fiber" [.lit "x", .never]) (.app "Fiber.Fiber" [.string, .nat])
#guard !sub (.app "Ref.Ref" [.lit "x"]) (.app "Ref.Ref" [.string])
#guard sub (.app "Layer.Layer" [.string, .never, .never]) (.app "Layer.Layer" [.lit "x", .never, .never])
#guard !sub (.app "Undeclared.Name" [.lit "x"]) (.app "Undeclared.Name" [.string])
#guard !sub (.app "Fiber.Fiber" [.nat, .nat]) (.app "Exit.Exit" [.nat, .nat])
#guard sub (.map .string (.lit "v")) (.map .string .string)
-- the leaf edges, from the table: accepted, converse refused, and through a leaf
#guard sub (.lit "a") .string && !sub .string (.lit "a")
#guard sub .undefined .unit && !sub .unit .undefined
#guard sub .nat .int && sub .int .number && sub .nat .number && !sub .number .nat && !sub .int .nat
#guard !sub .number .string
#guard !sub (.map (.lit "k") .nat) (.map .string .nat)

end Ty
end ProbeQW

#print axioms ProbeQW.Ty.mem_canon
#print axioms ProbeQW.Ty.canon_eq_nil
#print axioms ProbeQW.Ty.sub_refl
#print axioms ProbeQW.Ty.sub_unknown
