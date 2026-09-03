/-
Independent breaker packet: test/contracts/structure-computed.contract.md.
The computed facts concern the actual pinned algorithm, not a supplied table
or a graph record carrying the answer as an assumption.
-/

import Effect4.Target.TypeScript.StructureDominators
import Effect4Test.Counterexamples.Target.BreakScoped
import Effect4Test.Target.TypeScript.StructuredLowerContract

set_option autoImplicit false

open TypeScript Effects Effect4.Target.EffectV4 Effect4.Target.Structured

namespace Effect4Test.Target.TypeScript.StructureComputedContract

private abbrev diamond := Effect4Test.Counterexamples.Target.BreakScoped.diamond

-- A merge whose computed parent is not the entry. Replacing every parent
-- with the entry would satisfy several weak order tests, but fails this one.
private def nestedDiamond : Structure.Graph :=
  { size := 6, entry := 0, succs := fun node => match node with
      | 0 => [1] | 1 => [2, 3] | 2 => [4] | 3 => [4] | 4 => [5] | _ => [] }

-- Node identifiers are not reverse-postorder positions.
private def reordered : Structure.Graph :=
  { size := 3, entry := 2, succs := fun node => match node with
      | 2 => [0] | 0 => [1] | _ => [] }

/-! Existing-meaning controls, independent of every new declaration. -/

#guard Structure.rpo diamond = [0, 2, 1, 3]
#guard Structure.idoms diamond = [some 0, some 0, some 0, some 0]
#guard (List.range 4).map (Structure.idom diamond) = [none, some 0, some 0, some 0]
#guard Structure.reducible diamond = true
#guard Structure.isMerge diamond 3 = true
#guard Structure.isBackEdge diamond 1 3 = false
#guard Structure.dominates diamond 0 1 = true
#guard Structure.dominates diamond 0 2 = true

#guard Structure.rpo nestedDiamond = [0, 1, 3, 2, 4, 5]
#guard (List.range 6).map (Structure.idom nestedDiamond) =
  [none, some 0, some 1, some 1, some 1, some 4]
#guard Structure.reducible nestedDiamond = true
#guard Structure.isMerge nestedDiamond 4 = true
#guard Structure.dominates nestedDiamond 1 2 && Structure.dominates nestedDiamond 1 3

#guard Structure.rpo reordered = [2, 0, 1]
#guard (List.range 3).map (Structure.idom reordered) = [some 2, some 0, none]
#guard Structure.index reordered 2 = 0 && Structure.index reordered 0 = 1
#guard Structure.reducible reordered = true

-- CE-018 still refutes the old body premise, even when graph facts are now
-- computed. The corrected edge-local premise must remain necessary.
#check Effect4Test.Counterexamples.Target.BreakScoped.frozen_statement_false
#check Effect4Test.Counterexamples.Target.BreakScoped.illicit_body_not_edge_scoped
example : Structuring.emitWith diamond structuredShapes
    Effect4Test.Counterexamples.Target.BreakScoped.illicitBody =
      some Effect4Test.Counterexamples.Target.BreakScoped.emitted := rfl
#guard Skel.wellScopedList [] [] Effect4Test.Counterexamples.Target.BreakScoped.emitted = false

private theorem diamond_sourceBounded :
    ∀ source target, target ∈ diamond.succs source → source < diamond.size := by
  intro source target member
  cases source with
  | zero => decide
  | succ n => cases n with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ n => simp [diamond, Effect4Test.Counterexamples.Target.BreakScoped.diamond] at member

open Effect4Test.Target.TypeScript.StructuredLowerContract (swapRaw swapTable)

#guard ((Flow.skeletonBody swapTable false swapRaw.blocks swapRaw.entry).map
  (Skel.wellScopedList [] [])) = some true
#guard ((Flow.skeletonBody swapTable true swapRaw.blocks swapRaw.entry).map
  (Skel.wellScopedList [] [])) = some true

/- BEGIN COMPUTED-SURFACE -/

-- Unconditional over every raw graph and every pair of node identifiers.
#check (@Effect4.Target.Structured.idom_index_le :
  (g : Structure.Graph) → (parent child : Nat) →
  Structure.idom g child = some parent → Structure.index g parent ≤ Structure.index g child)

-- No supplied DomFacts, forest, ancestry, convergence, entry-bound, or
-- precomputed-table premise may be added to this statement.
#check (@Effect4.Target.Structured.computed_dominatorFacts :
  (g : Structure.Graph) → GraphClosed g →
  (∀ source target, target ∈ g.succs source → source < g.size) →
  Structure.reducible g = true → Effect4.Target.Structured.DominatorFacts g)

#check (@Effect4.Target.Structured.emitWith_wellScoped_computed :
  {g : Structure.Graph} →
  {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)} →
  GraphClosed g → (∀ source target, target ∈ g.succs source → source < g.size) →
  Effect4.Target.Structured.BodyScopedOnEdges g body → {out : List Skeleton} →
  Structuring.emitWith g structuredShapes body = some out →
  Skel.wellScopedList [] [] out = true)

#check (@Effect4.Target.Structured.skeletonBody_wellScoped_computed :
  (table : List OpSpec) → (interrupts : Bool) → (blocks : List (RawBlock String)) →
  (entry : BlockId) → {out : List Skeleton} →
  Flow.skeletonBody table interrupts blocks entry = some out →
  Skel.wellScopedList [] [] out = true)

-- The computed record is inhabited on a real merge with two forward
-- predecessors. Both nontrivial field applications must elaborate.
example : Effect4.Target.Structured.DominatorFacts diamond :=
  computed_dominatorFacts diamond
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_closed diamond_sourceBounded
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_reducible

example : Structure.index reordered 2 ≤ Structure.index reordered 0 :=
  idom_index_le reordered 2 0 rfl

example : ∃ parent, Structure.idom diamond 3 = some parent ∧
    Structure.dominates diamond parent 1 = true :=
  (computed_dominatorFacts diamond
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_closed diamond_sourceBounded
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_reducible).forwardJoinParent
      1 3 (by decide) (by decide) (by decide)

example : ∃ parent, Structure.idom diamond 3 = some parent ∧
    Structure.dominates diamond parent 2 = true :=
  (computed_dominatorFacts diamond
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_closed diamond_sourceBounded
    Effect4Test.Counterexamples.Target.BreakScoped.diamond_reducible).forwardJoinParent
      2 3 (by decide) (by decide) (by decide)

example : ¬ Effect4.Target.Structured.BodyScopedOnEdges diamond
    Effect4Test.Counterexamples.Target.BreakScoped.illicitBody :=
  Effect4Test.Counterexamples.Target.BreakScoped.illicit_body_not_edge_scoped

-- Universal actual-body use: no graph-fact hypothesis is smuggled into this
-- bridge, and true interrupts are in scope for lexical binding only.
example (table : List OpSpec) (interrupts : Bool) (blocks : List (RawBlock String))
    (entry : BlockId) {out : List Skeleton}
    (emitted : Flow.skeletonBody table interrupts blocks entry = some out) :
    Skel.wellScopedList [] [] out = true :=
  skeletonBody_wellScoped_computed table interrupts blocks entry emitted

/- END COMPUTED-SURFACE -/

end Effect4Test.Target.TypeScript.StructureComputedContract
