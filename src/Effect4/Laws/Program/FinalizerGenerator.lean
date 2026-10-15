import Effect4.Laws.Program.FinalizerLayerBody
import Init.Data.List.Lex

/-!
Concept: scope-lifetime-finalization R11.
Question: generator continuations of `once_placed_outside_census`.
Consumer: selected-source debit through the existing statement walker.
A program counter reserves later enclosing continuations as well as its current block.
These path facts establish no history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerGenerator
open Effect4 Effect4.Machine Effect4.Program
open SourceScope.Opportunities

/-- Constructive prefix order avoids a classical order-instance dependency.
Consumer: selected generator continuation reservations. -/
private theorem prefix_le (base tail : List Nat) : base ≤ base ++ tail := by
  induction base with
  | nil => intro impossible; cases impossible
  | cons head rest ih =>
    intro impossible
    cases impossible with
    | rel less => exact Nat.lt_irrefl head less
    | cons less => exact ih less

private theorem prefix_order (base q : List Nat) (held : base.isPrefixOf q = true) : base ≤ q := by
  obtain ⟨tail, equal⟩ := List.isPrefixOf_iff_prefix.mp held
  rw [← equal]
  exact prefix_le base tail

private theorem append_order (base left right : List Nat) (held : left ≤ right) :
    base ++ left ≤ base ++ right := by
  induction base with
  | nil => exact held
  | cons head rest ih =>
    intro impossible
    cases impossible with
    | rel less => exact Nat.lt_irrefl head less
    | cons less => exact ih less

private theorem order_trans (first middle last : List Nat)
    (left : first ≤ middle) (right : middle ≤ last) : first ≤ last := by
  by_cases forward : first < middle
  · intro reverse
    exact right (List.lex_trans Nat.lt_trans reverse forward)
  · have equal : first = middle := List.lex_trichotomous
      (fun _ _ h₁ h₂ => by omega) left forward
    cases equal
    exact right

/-- A selected source remains available while its path follows the current generator counter. -/
def remaining (q base pc : List Nat) : Nat :=
  if base.isPrefixOf q = true ∧ base ++ pc ≤ q then 1 else 0

/-- A generator reservation stays within its enclosing source body. -/
theorem remaining_le (q base pc : List Nat) : remaining q base pc ≤ below q base := by
  unfold remaining below
  split
  · rename_i held
    rw [if_pos held.1]
    exact Nat.le_refl 1
  · exact Nat.zero_le _

/-- Entering a generator reserves its whole source body. -/
theorem remaining_start (q base : List Nat) : remaining q base [] = below q base := by
  unfold remaining below
  simp only [List.append_nil]
  cases prefixed : base.isPrefixOf q with
  | false => simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  | true =>
    have ordered := prefix_order base q prefixed
    rw [if_pos ⟨rfl, ordered⟩, if_pos rfl]

/-- Advancing a counter cannot create a later selected opportunity. -/
theorem remaining_mono (q base pc next : List Nat) (advance : pc ≤ next) :
    remaining q base next ≤ remaining q base pc := by
  unfold remaining
  split
  · rename_i held
    have ordered : base ++ pc ≤ q := order_trans _ _ _ (append_order base pc next advance) held.2
    rw [if_pos ⟨held.1, ordered⟩]
    exact Nat.le_refl 1
  · exact Nat.zero_le _

/-- Entering a child counter cannot create a later selected opportunity.
Consumer: actual generator conditionals and while-body entries. -/
theorem remaining_descend (q base pc suffix : List Nat) :
    remaining q base (pc ++ suffix) ≤ remaining q base pc :=
  remaining_mono q base pc (pc ++ suffix) (prefix_le pc suffix)

/-- Yielding separates the current source child from its later continuation.
Consumer: the actual yielded code and saved generator callback debit. -/
theorem yield_split (q base pc : List Nat) :
    below q (base ++ pc ++ [0, 0]) + remaining q base (pc ++ [1]) ≤
      remaining q base pc := by
  cases selected : (base ++ pc ++ [0, 0]).isPrefixOf q with
  | false =>
    simp only [below, selected, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact remaining_mono q base pc (pc ++ [1]) (prefix_le pc [1])
  | true =>
    obtain ⟨suffix, equal⟩ := List.isPrefixOf_iff_prefix.mp selected
    have before : q < base ++ (pc ++ [1]) := by
      rw [← equal]
      have ordered : (0 :: 0 :: suffix : List Nat) < [1] := by
        exact List.Lex.rel (by decide)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (List.append_left_lt (l₁ := base ++ pc) ordered)
    have basePrefix : base.isPrefixOf q = true := List.isPrefixOf_iff_prefix.mpr
      (List.IsPrefix.trans (List.prefix_append base (pc ++ [0, 0]))
        (by simpa only [List.append_assoc] using List.isPrefixOf_iff_prefix.mp selected))
    have currentPrefix : (base ++ pc).isPrefixOf q = true := List.isPrefixOf_iff_prefix.mpr
      (List.IsPrefix.trans (List.prefix_append (base ++ pc) [0, 0])
        (List.isPrefixOf_iff_prefix.mp selected))
    have currentOrder := prefix_order (base ++ pc) q currentPrefix
    simp only [below, selected, ↓reduceIte, remaining]
    rw [if_neg (fun held => held.2 before), if_pos ⟨basePrefix, currentOrder⟩]
    exact Nat.le_refl 1

/-- A path between adjacent child addresses lies below the earlier child.
Consumer: repeated while-body exclusion when a generator counter returns to its head. -/
theorem between_prefix (base q : List Nat) (lower : base ++ [0] ≤ q)
    (upper : q < base ++ [1]) : (base ++ [0]).isPrefixOf q = true := by
  induction base generalizing q with
  | nil =>
    cases q with
    | nil => exact False.elim (lower (List.nil_lt_cons 0 []))
    | cons head tail =>
      have high := List.cons_lt_cons_iff.mp upper
      have headZero : head = 0 := by
        cases high with
        | inl less => omega
        | inr equal => exact False.elim (List.not_lt_nil tail equal.2)
      cases headZero
      exact List.isPrefixOf_iff_prefix.mpr ⟨tail, rfl⟩
  | cons head base ih =>
    cases q with
    | nil =>
      apply False.elim
      apply lower
      exact List.Lex.nil
    | cons next tail =>
      have high := List.cons_lt_cons_iff.mp upper
      cases high with
      | inl less => exact False.elim (lower (List.Lex.rel less))
      | inr equal =>
        obtain ⟨equal, highTail⟩ := equal
        cases equal
        have lowTail : base ++ [0] ≤ tail := fun less => lower (List.Lex.cons less)
        obtain ⟨suffix, tailEq⟩ := List.isPrefixOf_iff_prefix.mp (ih tail lowTail highTail)
        exact List.isPrefixOf_iff_prefix.mpr ⟨suffix, by rw [← tailEq]; rfl⟩

/-- A source subtree forms an interval in the constructive path order.
Consumer: generator loop-return reservations outside the excluded while body. -/
theorem prefix_interval (base suffix q : List Nat) (lower : base ≤ q)
    (upper : q ≤ base ++ suffix) : base.isPrefixOf q = true := by
  induction base generalizing q with
  | nil => rfl
  | cons head base ih =>
    cases q with
    | nil => exact False.elim (lower List.Lex.nil)
    | cons next tail =>
      have equal : head = next := by
        have notForward : ¬ head < next := fun less => upper (List.Lex.rel less)
        have notBackward : ¬ next < head := fun less => lower (List.Lex.rel less)
        omega
      cases equal
      have lowTail : base ≤ tail := fun less => lower (List.Lex.cons less)
      have highTail : tail ≤ base ++ suffix := fun less => upper (List.Lex.cons less)
      obtain ⟨rest, equal⟩ := List.isPrefixOf_iff_prefix.mp (ih tail lowTail highTail)
      exact List.isPrefixOf_iff_prefix.mpr ⟨rest, by rw [← equal]; rfl⟩

/-- Returning within an excluded subtree creates no later selected opportunity.
Consumer: the actual generator while-body return and break transitions. -/
theorem excluded_return (q base current next : List Nat)
    (inside : (base ++ next).isPrefixOf (base ++ current) = true)
    (excluded : below q (base ++ next) = 0) :
    remaining q base next ≤ remaining q base current := by
  unfold remaining
  split
  · rename_i held
    have ordered : base ++ current ≤ q := by
      intro reverse
      obtain ⟨suffix, equal⟩ := List.isPrefixOf_iff_prefix.mp inside
      have upper : q ≤ base ++ current := fun contrary =>
        List.lex_irrefl Nat.lt_irrefl q (List.lex_trans Nat.lt_trans reverse contrary)
      have prefixed := prefix_interval (base ++ next) suffix q held.2 (by rw [equal]; exact upper)
      unfold below at excluded
      rw [prefixed] at excluded
      cases excluded
    rw [if_pos ⟨held.1, ordered⟩]
    exact Nat.le_refl 1
  · exact Nat.zero_le _

end Effect4.Program.FinalizerGenerator
