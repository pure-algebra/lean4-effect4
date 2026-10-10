import Tools.Graph.Path
import Tools.View.FlowLaws

/-!
# On-demand Flow explanations

These named tool laws serve `initial-algebras-folds`, R14, and decisions row 336(8).
The placement is `docs/research/2026-10-10-checked-graph-tools/PLAN.md`.
The consumer requests the cycle reason for one candidate in `acceptWaits`.
It supplies the exact accumulated edge list used by that query.
The explanation follows the existing bounded search, including its zero-fuel behavior.
An unsuccessful query establishes no absence of an unbounded path.
No scheduler observation or graph admission follows from these laws.
-/

namespace Tools.View.Flow

/-- Edge identities are positions in the supplied snapshot, including parallel occurrences. -/
abbrev EdgeOccurrence (es : List Edge) := Fin es.length

/-- Interpret an occurrence using the original directed edge. -/
def occurrenceEndpoints (es : List Edge) (i : EdgeOccurrence es) : Nat × Nat :=
  (es[i].fr, es[i].to)

private def predecessor (frontier seen : List Nat) (target : Nat) (e : Edge) : Bool :=
  (frontier.contains e.fr && !seen.contains e.to) && (e.to == target)

/-- A next-frontier member has an original edge occurrence to reconstruct.
This helper serves bounded explanation agreement. -/
private theorem predecessor_ne_none (es : List Edge) (frontier seen : List Nat)
    (target : Nat) (member : target ∈ searchNext es frontier seen) :
    es.findFinIdx? (predecessor frontier seen target) ≠ none := by
  intro missing
  have missingEdge : es.find? (predecessor frontier seen target) = none := by
    rw [List.find?_eq_map_findFinIdx?_getElem, missing]
    rfl
  have absent := List.find?_eq_none.mp missingEdge
  have filtered := List.mem_eraseDups.mp member
  obtain ⟨e, he, selected⟩ := List.mem_filterMap.mp filtered
  split at selected
  next eligible =>
    have same : e.to = target := Option.some.inj selected
    have positive : predecessor frontier seen target e = true :=
      Bool.and_eq_true_iff.mpr ⟨eligible, beq_iff_eq.mpr same⟩
    exact absent e he positive
  next => cases selected

/-- Internal successful search carries its frontier origin and its original occurrences. -/
private structure FrontierExplanation (es : List Edge) (frontier : List Nat) (target : Nat) where
  start : Nat
  member : start ∈ frontier
  path : Tools.Graph.Walk (occurrenceEndpoints es) start target

/-- Reconstruct backward through the same frontier and seen lists as `reaches`. -/
private def explainFrontier (es : List Edge) : (fuel : Nat) → (frontier seen : List Nat) →
    (target : Nat) → Option (FrontierExplanation es frontier target)
  | 0, _, _, _ => none
  | fuel + 1, frontier, seen, target =>
    if hit : frontier.contains target then
      some ⟨target, List.contains_iff_mem.mp hit, .refl target⟩
    else
      let next := searchNext es frontier seen
      if next.isEmpty then none else
      match explainFrontier es fuel next (seen ++ next) target with
      | none => none
      | some found =>
        match selected : es.findFinIdx? (predecessor frontier seen found.start) with
        | none => False.elim (predecessor_ne_none es frontier seen found.start found.member selected)
        | some i =>
          have selectedEdge : es.find? (predecessor frontier seen found.start) = some es[i] := by
            rw [List.find?_eq_map_findFinIdx?_getElem, selected]
            rfl
          have positive := List.find?_some selectedEdge
          have parts := Bool.and_eq_true_iff.mp positive
          have origin : frontier.contains (occurrenceEndpoints es i).1 = true :=
            (Bool.and_eq_true_iff.mp parts.1).1
          have destination : (occurrenceEndpoints es i).2 = found.start := beq_iff_eq.mp parts.2
          some ⟨(occurrenceEndpoints es i).1, List.contains_iff_mem.mp origin,
            .cons i (destination.symm ▸ found.path)⟩

/-- Bounded explanation agreement for any frontier; helper for `explainReaches_isSome`. -/
private theorem explainFrontier_isSome (es : List Edge) (fuel : Nat)
    (frontier seen : List Nat) (target : Nat) :
    (explainFrontier es fuel frontier seen target).isSome =
      reaches es fuel frontier seen target := by
  induction fuel generalizing frontier seen with
  | zero => rfl
  | succ fuel ih =>
    simp only [explainFrontier, reaches]
    split
    next hit => simp only [Option.isSome_some]
    next miss =>
      change (if (searchNext es frontier seen).isEmpty then none else _).isSome =
        if (searchNext es frontier seen).isEmpty then false else _
      split
      next => rfl
      next nonempty =>
        have agreement := ih (searchNext es frontier seen) (seen ++ searchNext es frontier seen)
        cases recursive : explainFrontier es fuel (searchNext es frontier seen)
            (seen ++ searchNext es frontier seen) target with
        | none =>
          simp only [recursive, Option.isSome_none] at agreement
          exact agreement
        | some found =>
          simp only [recursive, Option.isSome_some] at agreement
          dsimp only
          split
          next selected =>
            exact False.elim (predecessor_ne_none es frontier seen found.start found.member selected)
          next => exact agreement

/-- Explain precisely the existing bounded query, retaining its edge snapshot in the type. -/
def explainReaches (es : List Edge) (fuel source target : Nat) :
    Option (Tools.Graph.Walk (occurrenceEndpoints es) source target) :=
  match explainFrontier es fuel [source] [source] target with
  | none => none
  | some found =>
    have same : found.start = source := List.mem_singleton.mp found.member
    some (same ▸ found.path)

/-- Bounded Flow explanation agreement; `none` leaves unbounded reachability open. -/
theorem explainReaches_isSome (es : List Edge) (fuel source target : Nat) :
    (explainReaches es fuel source target).isSome =
      reaches es fuel [source] [source] target := by
  have agreement := explainFrontier_isSome es fuel [source] [source] target
  unfold explainReaches
  cases recursive : explainFrontier es fuel [source] [source] target with
  | none => simp only [recursive, Option.isSome_none] at agreement; exact agreement
  | some found => simp only [recursive, Option.isSome_some] at agreement; exact agreement

/-- Every occurrence path implies the existing directed Flow judgment.
This helper serves the positive explanation connector. -/
theorem occurrenceWalk_reach (es : List Edge) {source target : Nat}
    (path : Tools.Graph.Walk (occurrenceEndpoints es) source target) :
    Reach es source target := by
  exact Tools.Graph.Walk.fold (endpoints := occurrenceEndpoints es) (Reach es) (fun v => .refl v)
    (fun (i : EdgeOccurrence es) _ ih => .step es[i] (List.getElem_mem i.isLt) ih) path

/-- A successful existing bounded query implies the existing directed Flow judgment. -/
theorem reaches_reach (es : List Edge) (fuel source target : Nat)
    (reached : reaches es fuel [source] [source] target = true) :
    Reach es source target := by
  have successful := (explainReaches_isSome es fuel source target).trans reached
  cases answer : explainReaches es fuel source target with
  | none =>
      rw [answer] at successful
      cases successful
  | some path => exact occurrenceWalk_reach es path

/-- Explain a candidate exit-to-await wait using the existing await-to-exit cycle query.
The caller supplies the exact current accumulated constraints. -/
def explainWait (n : Nat) (es : List Edge) (candidate : Nat × Nat) :
    Option (Tools.Graph.Walk (occurrenceEndpoints es) candidate.2 candidate.1) :=
  explainReaches es (n + 1) candidate.2 candidate.1

/-- The on-demand wait explanation selects precisely the existing cycle branch. -/
theorem explainWait_isSome (n : Nat) (es : List Edge) (candidate : Nat × Nat) :
    (explainWait n es candidate).isSome =
      reaches es (n + 1) [candidate.2] [candidate.2] candidate.1 :=
  explainReaches_isSome es (n + 1) candidate.2 candidate.1

end Tools.View.Flow
