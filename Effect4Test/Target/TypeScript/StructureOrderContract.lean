/-
Independent breaker packet: test/contracts/structure-order.contract.md.
General ascriptions are separated from finite controls so the missing-surface
red state can be checked without disguising an import failure as evidence.
-/

import Effect4.Target.TypeScript.StructureOrder
import Effect4Test.Counterexamples.Target.BreakScoped
import Effect4Test.Target.TypeScript.StructuredLowerContract

set_option autoImplicit false

open TypeScript Effects Effect4.Target.EffectV4 Effect4.Target.Structured

namespace Effect4Test.Target.TypeScript.StructureOrderContract

abbrev CE := Effect4Test.Counterexamples.Target.BreakScoped.diamond

/-! ## Existing-meaning controls: nonempty graph/body examples -/

#guard Structure.rpo CE = [0, 2, 1, 3]
#guard Structure.children CE 0 = [2, 1, 3]
#guard Structure.reducible CE = true

-- The old illicit body still emits an orphan break. Its preserved kernel
-- theorem rejects the proposed edge-local premise; it is not relabelled valid.
#check Effect4Test.Counterexamples.Target.BreakScoped.frozen_statement_false
#check Effect4Test.Counterexamples.Target.BreakScoped.illicit_body_not_edge_scoped
example : Structuring.emitWith CE structuredShapes
    Effect4Test.Counterexamples.Target.BreakScoped.illicitBody =
      some Effect4Test.Counterexamples.Target.BreakScoped.emitted := rfl
#guard Skel.wellScopedList [] [] Effect4Test.Counterexamples.Target.BreakScoped.emitted = false

-- The real lowerer emits a merge/loop with parameter moves, both with and
-- without interrupt points. Scoping is independent of interrupt denotation.
open Effect4Test.Target.TypeScript.StructuredLowerContract (swapRaw swapTable)

#guard ((Flow.skeletonBody swapTable false swapRaw.blocks swapRaw.entry).map
  (Skel.wellScopedList [] [])) = some true
#guard ((Flow.skeletonBody swapTable true swapRaw.blocks swapRaw.entry).map
  (Skel.wellScopedList [] [])) = some true

-- A concrete nonempty domain for the graph premises. No extra hidden field
-- of DominatorFacts may make the later universal theorem vacuous.
def terminalGraph : Structure.Graph := { size := 1, entry := 0, succs := fun _ => [] }

theorem terminal_childIndex :
    ∀ parent child, Structure.idom terminalGraph child = some parent →
      Structure.index terminalGraph parent ≤ Structure.index terminalGraph child := by
  intro parent child up
  cases child <;> change (none : Option Nat) = some parent at up
  all_goals exact False.elim (Option.noConfusion rfl (heq_of_eq up))

theorem terminal_forwardJoinParent :
    ∀ source target, target ∈ terminalGraph.succs source →
      Structure.isBackEdge terminalGraph source target = false →
      (Structure.isMerge terminalGraph target || Structure.isLoopHeader terminalGraph target) = true →
      ∃ parent, Structure.idom terminalGraph target = some parent ∧
        Structure.dominates terminalGraph parent source = true := by
  intro source target edge
  exact False.elim (List.not_mem_nil edge)

example : Structuring.emitWith terminalGraph structuredShapes (fun _ _ => some []) = some [] := rfl

/- BEGIN ORDER-SURFACE -/

#check (@Effect4.Target.Structured.rpo_nodup :
  (g : Structure.Graph) → (Structure.rpo g).Nodup)

#check (@Effect4.Target.Structured.rpo_index_order :
  (g : Structure.Graph) →
    (Structure.rpo g).Pairwise (fun a b => Structure.index g a < Structure.index g b))

#check (@Effect4.Target.Structured.children_index_order :
  (g : Structure.Graph) → (node : Nat) →
    (Structure.children g node).Pairwise (fun a b => Structure.index g a < Structure.index g b))

#check (@Effect4.Target.Structured.BodyScopedOnEdges :
  Structure.Graph → (Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) → Prop)

-- Exact corrected premise, linked definitionally to the retained CE-018 seat.
example (g : Structure.Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) :
    Effect4.Target.Structured.BodyScopedOnEdges g body =
      Effect4Test.Counterexamples.Target.BreakScoped.BodyScopedOnEdges g body := rfl

#check (@Effect4.Target.Structured.DominatorFacts.mk :
  (g : Structure.Graph) →
  (∀ parent child, Structure.idom g child = some parent →
    Structure.index g parent ≤ Structure.index g child) →
  (∀ source target, target ∈ g.succs source → Structure.isBackEdge g source target = false →
    (Structure.isMerge g target || Structure.isLoopHeader g target) = true →
    ∃ parent, Structure.idom g target = some parent ∧
      Structure.dominates g parent source = true) →
  Effect4.Target.Structured.DominatorFacts g)

#check (@Effect4.Target.Structured.DominatorFacts.childIndex :
  {g : Structure.Graph} → Effect4.Target.Structured.DominatorFacts g →
  ∀ parent child, Structure.idom g child = some parent →
    Structure.index g parent ≤ Structure.index g child)

#check (@Effect4.Target.Structured.DominatorFacts.forwardJoinParent :
  {g : Structure.Graph} → Effect4.Target.Structured.DominatorFacts g →
  ∀ source target, target ∈ g.succs source → Structure.isBackEdge g source target = false →
    (Structure.isMerge g target || Structure.isLoopHeader g target) = true →
    ∃ parent, Structure.idom g target = some parent ∧ Structure.dominates g parent source = true)

example : Effect4.Target.Structured.DominatorFacts terminalGraph :=
  ⟨terminal_childIndex, terminal_forwardJoinParent⟩

-- These are quantified over every graph/body, not only a finite fixture set.
-- Successful emitWith already entails its existing reducibility guard.
#check (@Effect4.Target.Structured.emitWith_wellScoped_of_dominators :
  {g : Structure.Graph} →
  {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)} →
  GraphClosed g → (∀ source target, target ∈ g.succs source → source < g.size) →
  Effect4.Target.Structured.DominatorFacts g →
  Effect4.Target.Structured.BodyScopedOnEdges g body → {out : List Skeleton} →
  Structuring.emitWith g structuredShapes body = some out →
  Skel.wellScopedList [] [] out = true)

#check (@Effect4.Target.Structured.skeletonBody_wellScoped_of_dominators :
  (table : List OpSpec) → (interrupts : Bool) → (blocks : List (RawBlock String)) →
  (entry : BlockId) → Effect4.Target.Structured.DominatorFacts (Flow.graphOf blocks entry) →
  {out : List Skeleton} → Flow.skeletonBody table interrupts blocks entry = some out →
  Skel.wellScopedList [] [] out = true)

-- The actual body satisfies the new predicate for every table, block list,
-- entry and interrupt setting; the previous kernel receipt remains reusable.
example (table : List OpSpec) (interrupts : Bool) (blocks : List (RawBlock String))
    (entry : BlockId) :
    Effect4.Target.Structured.BodyScopedOnEdges (Flow.graphOf blocks entry)
      (Effect4Test.Counterexamples.Target.BreakScoped.actualBody table interrupts blocks) :=
  Effect4Test.Counterexamples.Target.BreakScoped.actualBody_scoped_on_edges
    table interrupts blocks entry

example : ¬ Effect4.Target.Structured.BodyScopedOnEdges CE
    Effect4Test.Counterexamples.Target.BreakScoped.illicitBody :=
  Effect4Test.Counterexamples.Target.BreakScoped.illicit_body_not_edge_scoped

/- END ORDER-SURFACE -/

end Effect4Test.Target.TypeScript.StructureOrderContract
