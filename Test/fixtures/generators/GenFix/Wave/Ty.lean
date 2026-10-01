import GenFix.Wave.TyEq
import GenFix.Wave.TyVariance

/-!
# GenFix.Wave.Ty — the order over the wave fixture: variable-arity arms and the leaf-order table

The functions the generated view reads, over the whole wave (probe Q's `ProbeQW.Ty`, with probe
P's table in place of probe Q's `edgeRule`; decisions rows 171 and 177):

* `canon` (generic in the value), `mem_canon`, `canon_eq_nil`: the canonical field order;
* the leaf-order table of probe P (`P/probes/P2Ty.lean:666-722`) with the wave's four declared
  edges, `lit < string`, `nat < int`, `int < number`, `undefined < unit` (`nat ⊑ number` derived,
  never an entry), consulted by `sub` before its rows;
* `sub`: the reflexive line, the table's line, the structural arms, the fixed congruences, and the
  variable-arity arms in the form the generated arm lemma proves (`decide (head) &&
  (zip).attach.all …`); the literal arm `.lit _, .string` is gone (it is the table's first row);
* the four `sub` lemmas the table's laws read, and a `normalize` whose leaves are fixed by `rfl`
  (the real one is commit 4's; the view emits the `normalize` facts when the core declares it).

Read by `scripts/test-generators.py`; not a battery module.
-/

set_option autoImplicit false

namespace GenFix.Wave
namespace Ty

/-! ## The canonical field order -/

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

/-! ## The measures the well-founded arms decrease by -/

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

/-- A union member has neither an empty nor a union head. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown
  | .record _ | .map _ _ | .tuple _ | .app _ _ | .null | .undefined | .number | .bytes => true

/-- A stand-in normaliser (commit 4 lands the real one): unions rebuilt, every other head fixed. -/
def normalize : Ty → Ty
  | .union a b => .union (normalize a) (normalize b)
  | t => t

/-! ## The leaf-order table (decisions row 177; probe P, `P2Ty.lean:666-722`) -/

/-- The heads the leaf order relates: childless heads. -/
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
  [ (.lit, .string)
  , (.nat, .int)
  , (.int, .number)
  , (.undefined, .unit) ]

/-- Reachability in a table of edges, with fuel. -/
def leafReach (edges : List (LeafHead × LeafHead)) : Nat → LeafHead → LeafHead → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || edges.any fun e => decide (e.1 = x) && leafReach edges n e.2 y

/-- The leaf order: the table's reflexive-transitive closure. -/
def leafLe (x y : LeafHead) : Bool := leafReach leafEdges leafEdges.length x y

/-- The rule `sub` consults before its rows. -/
def leafRule (a b : Ty) : Bool :=
  match leafHead a, leafHead b with
  | some x, some y => !decide (x = y) && leafLe x y
  | _, _ => false

/-! ## The order -/

/-- `Ty.lean:437` with the table before its rows (the literal arm is the table's first row) and the
wave's four congruence arms, the variable-arity ones in the form the generated view proves. -/
def sub (a b : Ty) : Bool :=
  if a = b then true
  else if leafRule a b then true
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
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-! ## The four `sub` lemmas the table's laws read (probe P, `P2Ty.lean:1140-1160`) -/

theorem leafRule_of_left_none (a b : Ty) (h : leafHead a = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]

theorem leafRule_of_right_none (a b : Ty) (h : leafHead b = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]
  cases leafHead a <;> rfl

theorem ite_leafRule_false {a b : Ty} {r : Bool} (h : leafRule a b = false) :
    (if leafRule a b = true then true else r) = r := by
  rw [h]
  rfl

theorem sub_of_leafRule {a b : Ty} (h : leafRule a b = true) : sub a b = true := by
  unfold sub
  by_cases hab : a = b
  · rw [if_pos hab]
  · rw [if_neg hab, if_pos h]

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  rw [if_pos rfl]

/-! Finite controls on the arms. -/

#guard sub (.record [("b", .nat, false), ("a", .bool, true)]) (.record [("a", .bool, true), ("b", .nat, false)])
#guard !sub (.record [("a", .nat, false)]) (.record [("a", .nat, true)])
#guard sub (.tuple [.lit "x", .nat]) (.tuple [.string, .nat])
#guard !sub (.tuple [.nat]) (.tuple [.nat, .nat])
#guard sub (.app "Fiber.Fiber" [.lit "x", .never]) (.app "Fiber.Fiber" [.string, .nat])
#guard !sub (.app "Ref.Ref" [.lit "x"]) (.app "Ref.Ref" [.string])
#guard sub (.map .string (.lit "v")) (.map .string .string)

end Ty
end GenFix.Wave
