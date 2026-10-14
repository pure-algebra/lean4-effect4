import Whatwg.Svg.Scene.Extent
import Lean.Elab.Tactic.Omega

/-!
# Finite node-box clearance and explicit relocation phases

`checkClear` observes kit `IBox.Disjoint` over allocated box occurrences.
`firstFrameOverlap` checks only the supplied moments.
Movement envelopes require bounded origins and sizes; they may refuse a safe direct move.
The fallback selects one endpoint family while visible and no family during relocation.
The producer must apply that phase to the whole scene, not just its node boxes.

Placement: `docs/research/2026-10-13-graph-separation-plan.md`, concept 7, R14, row 334 (3).
The consumer is the graph transition policy in `GraphMotion.prepare`.
No declaration claims route clearance, scheduler behavior or unrestricted easing safety.
-/

namespace Tools.View.GraphSeparation

open Whatwg.Svg.Scene

/-- Two box occurrences in their supplied order. -/
structure Pair where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

private def firstAgainst (a : IBox) : Nat → List IBox → Option Nat
  | _, [] => none
  | j, b :: bs => if a.Disjoint b then firstAgainst a (j + 1) bs else some j

/-- Helper of `checkClear_iff`: no conflicting later occurrence. -/
private theorem firstAgainst_none_iff (a : IBox) : ∀ j bs,
    firstAgainst a j bs = none ↔ ∀ b ∈ bs, a.Disjoint b := by
  intro j bs
  induction bs generalizing j with
  | nil => exact ⟨fun _ _ h => False.elim (List.not_mem_nil h), fun _ => rfl⟩
  | cons b bs ih =>
      by_cases h : a.Disjoint b
      · rw [firstAgainst, if_pos h, ih]
        exact ⟨fun tail c hc => (List.mem_cons.mp hc).elim (fun e => e ▸ h) (tail c),
          fun all c hc => all c (List.mem_cons_of_mem b hc)⟩
      · rw [firstAgainst, if_neg h]
        constructor
        · intro impossible
          cases impossible
        · intro all
          exact False.elim (h (all b List.mem_cons_self))

private def firstOverlapFrom : Nat → List IBox → Option Pair
  | _, [] => none
  | i, a :: bs =>
      match firstAgainst a (i + 1) bs with
      | some j => some ⟨i, j⟩
      | none => firstOverlapFrom (i + 1) bs

/-- Helper of `checkClear_iff`: the search observes each ordered pair. -/
private theorem firstOverlapFrom_none_iff : ∀ i bs,
    firstOverlapFrom i bs = none ↔ List.Pairwise IBox.Disjoint bs := by
  intro i bs
  induction bs generalizing i with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons a bs ih =>
      unfold firstOverlapFrom
      cases found : firstAgainst a (i + 1) bs with
      | none =>
          change firstOverlapFrom (i + 1) bs = none ↔ _
          rw [ih, List.pairwise_cons]
          have all := (firstAgainst_none_iff a _ bs).mp found
          exact ⟨fun tail => ⟨all, tail⟩, fun both => both.2⟩
      | some j =>
          change some (Pair.mk i j) = none ↔ _
          constructor
          · intro impossible; cases impossible
          · intro pairwise
            have absent := (firstAgainst_none_iff a (i + 1) bs).mpr
              (List.pairwise_cons.mp pairwise).1
            rw [found] at absent
            cases absent

/-- The first conflicting pair, with touching boxes accepted as disjoint. -/
def firstOverlap (boxes : List IBox) : Option Pair := firstOverlapFrom 0 boxes

/-- Whether every pair of allocated boxes is disjoint. -/
def checkClear (boxes : List IBox) : Bool := (firstOverlap boxes).isNone

/-- The graph policy consumes exactly the supplied box-separation observation. -/
theorem checkClear_iff (boxes : List IBox) :
    checkClear boxes = true ↔ List.Pairwise IBox.Disjoint boxes := by
  rw [checkClear, Option.isNone_iff_eq_none, firstOverlap, firstOverlapFrom_none_iff]

/-- A failing supplied frame and its conflicting pair. -/
structure FrameOverlap where
  frame : Nat
  pair : Pair
  deriving DecidableEq, Repr

private def firstFrameFrom : Nat → List (List IBox) → Option FrameOverlap
  | _, [] => none
  | i, boxes :: rest =>
      match firstOverlap boxes with
      | some pair => some ⟨i, pair⟩
      | none => firstFrameFrom (i + 1) rest

/-- Inspect a finite profile in order; no conclusion concerns missing moments. -/
def firstFrameOverlap (frames : List (List IBox)) : Option FrameOverlap := firstFrameFrom 0 frames

/-- Helper of the finite profile law; each frame supplies its own box family. -/
private theorem firstFrameFrom_none_iff : ∀ i frames,
    firstFrameFrom i frames = none ↔ ∀ boxes ∈ frames, List.Pairwise IBox.Disjoint boxes := by
  intro i frames
  induction frames generalizing i with
  | nil => exact ⟨fun _ _ h => False.elim (List.not_mem_nil h), fun _ => rfl⟩
  | cons boxes frames ih =>
      unfold firstFrameFrom
      cases found : firstOverlap boxes with
      | none =>
          change firstFrameFrom (i + 1) frames = none ↔ _
          rw [ih]
          have clear := (firstOverlapFrom_none_iff 0 boxes).mp found
          exact ⟨fun tail b hb => (List.mem_cons.mp hb).elim (fun e => e ▸ clear) (tail b),
            fun all b hb => all b (List.mem_cons_of_mem boxes hb)⟩
      | some pair =>
          change some (FrameOverlap.mk i pair) = none ↔ _
          constructor
          · intro impossible; cases impossible
          · intro all
            have absent := (firstOverlapFrom_none_iff 0 boxes).mpr (all boxes List.mem_cons_self)
            change firstOverlap boxes = none at absent
            rw [found] at absent
            cases absent

/-- The supplied finite profile passes exactly when every supplied frame is pairwise disjoint. -/
theorem firstFrameOverlap_none_iff (frames : List (List IBox)) :
    firstFrameOverlap frames = none ↔ ∀ boxes ∈ frames, List.Pairwise IBox.Disjoint boxes :=
  firstFrameFrom_none_iff 0 frames

/-- A conservative origin sweep, allowing either endpoint's full width and height throughout. -/
def movingEnvelope (a b : IBox) : IBox :=
  ⟨min a.x0 b.x0, min a.y0 b.y0,
    max a.x0 b.x0 + max a.width b.width, max a.y0 b.y0 + max a.height b.height⟩

/-- The envelope contains a current box under explicit origin and size bounds. -/
theorem movingEnvelope_contains (a b current : IBox)
    (hx0 : min a.x0 b.x0 ≤ current.x0) (hx1 : current.x0 ≤ max a.x0 b.x0)
    (hy0 : min a.y0 b.y0 ≤ current.y0) (hy1 : current.y0 ≤ max a.y0 b.y0)
    (hw : current.width ≤ max a.width b.width)
    (hh : current.height ≤ max a.height b.height) : current.Inside (movingEnvelope a b) := by
  simp only [IBox.Inside, movingEnvelope, IBox.width, IBox.height] at *
  exact ⟨hx0, by omega, hy0, by omega⟩

/-- A conservative conflict selector; overlap can be a false positive. -/
def firstSweptOverlap (moves : List (IBox × IBox)) : Option Pair :=
  firstOverlap (moves.map fun (a, b) => movingEnvelope a b)

/-- Explicit whole-scene policy metadata; growth is in per mille. -/
inductive FallbackPhase where
  | old (grow : Nat)
  | hidden
  | new (grow : Nat)
  deriving DecidableEq, Repr

/-- Shrink at the old endpoint, relocate hidden, then grow at the new endpoint. -/
def fallback (t : Nat) : FallbackPhase :=
  if t < 400 then .old (1000 - t * 1000 / 400)
  else if t ≤ 600 then .hidden
  else .new (min 1000 ((t - 600) * 1000 / 400))

/-- Growth cannot overshoot the selected endpoint family's allocated envelope. -/
theorem fallback_growth_le (t : Nat) :
    match fallback t with
    | .old g | .new g => g ≤ 1000
    | .hidden => True := by
  by_cases h : t < 400
  · rw [fallback, if_pos h]
    exact Nat.sub_le _ _
  · by_cases h' : t ≤ 600
    · rw [fallback, if_neg h, if_pos h']
      trivial
    · rw [fallback, if_neg h, if_neg h']
      exact Nat.min_le_left _ _

/-- Conservative visible node envelopes; the integration must hide all other scene content too. -/
def FallbackPhase.envelopes (phase : FallbackPhase) (old new : List IBox) : List IBox :=
  match phase with
  | .old g => if g = 0 then [] else old
  | .hidden => []
  | .new g => if g = 0 then [] else new

/-- Visible envelopes come from one endpoint family, never a mixture of the two. -/
theorem fallback_endpoint_family (phase : FallbackPhase) (old new : List IBox) :
    phase.envelopes old new = [] ∨ phase.envelopes old new = old ∨
      phase.envelopes old new = new := by
  cases phase with
  | old g =>
      change (if g = 0 then [] else old) = [] ∨ (if g = 0 then [] else old) = old ∨ _
      by_cases h : g = 0
      · exact .inl (if_pos h)
      · exact .inr (.inl (if_neg h))
  | hidden => exact .inl rfl
  | new g =>
      change (if g = 0 then [] else new) = [] ∨ _ ∨ (if g = 0 then [] else new) = new
      by_cases h : g = 0
      · exact .inl (if_pos h)
      · exact .inr (.inr (if_neg h))

/-- Disjoint endpoint envelope families give disjoint visible fallback envelopes. -/
theorem fallback_clear (phase : FallbackPhase) (old new : List IBox)
    (ho : List.Pairwise IBox.Disjoint old) (hn : List.Pairwise IBox.Disjoint new) :
    List.Pairwise IBox.Disjoint (phase.envelopes old new) := by
  rcases fallback_endpoint_family phase old new with empty | oldFamily | newFamily
  · rw [empty]; exact .nil
  · rw [oldFamily]; exact ho
  · rw [newFamily]; exact hn

end Tools.View.GraphSeparation
