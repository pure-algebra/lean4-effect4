import Effect4.Target.TypeScript.StructureLaws

/-!
Kernel witnesses for `E4-TARGET-CE-018`.

`frozen_statement_false` refutes the existing quantified
`Effect4.Target.Structured.BreakScopedStatement`: `BodyScoped` allows a body
to request a transfer that is absent from the graph. The four-node diamond
emits a final `break L3` outside its binder.

`BodyScopedOnEdges` and `CorrectedBreakScopedStatement` record a proposed
contract correction in this test module only. The actual body of
`Flow.skeletonBody` satisfies the stronger hypothesis for every table, block
list and interrupt setting. No theorem here proves the corrected generic
statement or the intended full structured/dispatch agreement.

Pinned algorithm: lean4-typescript v0.4.1,
`cc62799055b1af7ce22b083afcfb30155c1ed4d0`.
-/

set_option autoImplicit false

open TypeScript Effects Effect4.Target.EffectV4 Effect4.Target.Structured

namespace Effect4Test.Counterexamples.Target.BreakScoped

def diamond : Structure.Graph :=
  { size := 4, entry := 0,
    succs := fun n => match n with
      | 0 => [1, 2]
      | 1 => [3]
      | 2 => [3]
      | _ => [] }

/-- A body allowed by the frozen hypothesis, even at node 3 with no successors. -/
def illicitBody (_ : Nat) (transfer : Nat → Option (List Skeleton)) :
    Option (List Skeleton) := transfer 3

def emitted : List Skeleton :=
  [Skeleton.labelled "L3" [Skeleton.breakTo "L3"], Skeleton.breakTo "L3"]

theorem diamond_closed : GraphClosed diamond := by
  intro source target member
  cases source with
  | zero => simp [diamond] at member ⊢; omega
  | succ n => cases n with
    | zero => simp [diamond] at member ⊢; omega
    | succ n => cases n with
      | zero => simp [diamond] at member ⊢; omega
      | succ n => simp [diamond] at member

theorem illicit_body_scoped : BodyScoped illicitBody := by
  intro node transfer blocks loops own transferScoped lowered
  exact transferScoped 3 own lowered

theorem diamond_reducible : Structure.reducible diamond = true := by decide

theorem illicit_emitted :
    Structuring.emitWith diamond structuredShapes illicitBody = some emitted := by rfl

theorem illicit_not_scoped : Skel.wellScopedList [] [] emitted = false := by decide

theorem frozen_statement_false : ¬ BreakScopedStatement := by
  intro alleged
  have hscoped := alleged diamond illicitBody emitted diamond_closed illicit_body_scoped
    diamond_reducible illicit_emitted
  rw [illicit_not_scoped] at hscoped
  contradiction

#print axioms diamond_closed
#print axioms illicit_body_scoped
#print axioms diamond_reducible
#print axioms illicit_emitted
#print axioms illicit_not_scoped
#print axioms frozen_statement_false


/-- A body needs scoped transfers only for the current node's declared edges. -/
def BodyScopedOnEdges (g : Structure.Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) : Prop :=
  ∀ (node : Nat) (transfer : Nat → Option (List Skeleton)) (blocks loops : List String)
    (own : List Skeleton),
    (∀ target control, target ∈ g.succs node → transfer target = some control →
      Skel.wellScopedList blocks loops control = true) →
    body node transfer = some own → Skel.wellScopedList blocks loops own = true

/-- Proposed replacement obligation; intentionally stated without a proof. -/
def CorrectedBreakScopedStatement : Prop :=
  ∀ (g : Structure.Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (out : List Skeleton),
    GraphClosed g → BodyScopedOnEdges g body → Structure.reducible g = true →
    Structuring.emitWith g structuredShapes body = some out →
    Skel.wellScopedList [] [] out = true

def edgeMove (block : RawBlock String)
    (move : BlockId → List Slot → Option (List Skeleton))
    (target : BlockId) (values : List Slot) : Option (List Skeleton) :=
  if target ∈ block.term.successors then move target values else none

theorem skeletonBlockWith_edgeMove (table : List OpSpec) (interrupts : Bool)
    (block : RawBlock String) (move : BlockId → List Slot → Option (List Skeleton)) :
    Flow.skeletonBlockWith table interrupts block (edgeMove block move) =
      Flow.skeletonBlockWith table interrupts block move := by
  cases h : block.term <;> simp [Flow.skeletonBlockWith, h, edgeMove, RawTerm.successors]

theorem skeletonBlockWith_scoped_on_edges (table : List OpSpec) (interrupts : Bool)
    (block : RawBlock String)
    (move : BlockId → List Slot → Option (List Skeleton)) (blocks loops : List String)
    (moveScoped : ∀ target values control, target ∈ block.term.successors →
      move target values = some control → Skel.wellScopedList blocks loops control = true)
    {own : List Skeleton}
    (lowered : Flow.skeletonBlockWith table interrupts block move = some own) :
    Skel.wellScopedList blocks loops own = true := by
  apply skeletonBlockWith_wellScoped table interrupts block (edgeMove block move) blocks loops
  · intro target values control produced
    unfold edgeMove at produced
    split at produced
    · next declared => exact moveScoped target values control declared produced
    · cases produced
  · rw [skeletonBlockWith_edgeMove]
    exact lowered

def actualBody (table : List OpSpec) (interrupts : Bool) (blocks : List (RawBlock String))
    (i : Nat) (transfer : Nat → Option (List Skeleton)) : Option (List Skeleton) := do
  let block ← blocks[i]?
  Flow.skeletonBlockWith table interrupts block fun target values => do
    let t ← Flow.position blocks target
    let control ← transfer t
    pure (Lowering.paramMove block.id target values ++ control)

/-- The real lowerer satisfies the proposed hypothesis, including interrupts. -/
theorem actualBody_scoped_on_edges (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId) :
    BodyScopedOnEdges (Flow.graphOf blocks entry) (actualBody table interrupts blocks) := by
  intro node transfer scopeBlocks scopeLoops own transferScoped lowered
  obtain ⟨block, found, lowered⟩ := Option.bind_eq_some_iff.mp lowered
  refine skeletonBlockWith_scoped_on_edges table interrupts block _ scopeBlocks scopeLoops ?_ lowered
  intro target values control edge moved
  obtain ⟨position, positioned, moved⟩ := Option.bind_eq_some_iff.mp moved
  obtain ⟨transferred, transferredEq, moved⟩ := Option.bind_eq_some_iff.mp moved
  injection moved with moved
  subst moved
  rw [Skel.wellScopedList_append]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨paramMove_wellScoped _ _ _ _ _, transferScoped position transferred ?_ transferredEq⟩
  change position ∈ match blocks[node]? with
    | some block => block.term.successors.filterMap (Flow.position blocks)
    | none => []
  rw [found]
  exact List.mem_filterMap.mpr ⟨target, edge, positioned⟩

theorem actualBody_exact (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId) :
    Flow.skeletonBody table interrupts blocks entry =
      Structuring.emitWith (Flow.graphOf blocks entry) structuredShapes
        (actualBody table interrupts blocks) := by rfl

theorem illicit_body_not_edge_scoped :
    ¬ BodyScopedOnEdges diamond illicitBody := by
  intro alleged
  have hbad := alleged 3 (fun _ => some [Skeleton.breakTo "L3"]) [] []
    [Skeleton.breakTo "L3"]
    (by intro target control edge; simp [diamond] at edge) rfl
  contradiction

#print axioms skeletonBlockWith_edgeMove
#print axioms skeletonBlockWith_scoped_on_edges
#print axioms actualBody_scoped_on_edges
#print axioms actualBody_exact
#print axioms illicit_body_not_edge_scoped

end Effect4Test.Counterexamples.Target.BreakScoped
