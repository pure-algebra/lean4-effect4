import Effect4.Target.TypeScript.StructureLaws

/-!
# Graph order and conditional strict scoping

The contract is `test/contracts/structure-order.contract.md`. This module
proves order properties of the pinned `TypeScript.Structure` algorithms and
uses them to prove strict lexical scoping for the existing skeleton emitter.
The corrected body premise rules out undeclared transfers, as required by
`E4-TARGET-CE-018`.

`DominatorFacts` names the two computation obligations still owed by the
pinned immediate-dominator algorithm. Both remain hypotheses of the public
scoping theorems. No theorem here establishes them for every reducible graph,
and lexical scoping does not establish full structured/dispatch denotation
agreement, loop fuel sufficiency or interrupt-point meaning.

The `Graph`, graph algorithms, emitter, skeleton and scoping judgment keep
their existing owners. TypeScript is pinned at
`cc62799055b1af7ce22b083afcfb30155c1ed4d0`; its pure order facts are candidates
for upstreaming through a later dependency update. This module changes no
algorithm, lowering bytes, existing statement or host boundary.
-/

set_option autoImplicit false
open TypeScript Effects Effect4.Target.EffectV4 Effect4.Target.Structured

namespace Effect4.Target.Structured

private structure VisitExtends (before after : List Nat × List Nat) : Prop where
  seen : ∀ n, n ∈ before.1 → n ∈ after.1
  fresh : ∀ n, n ∈ after.2 → n ∈ before.2 ∨ n ∉ before.1
  orderSeen : ∀ n, n ∈ after.2 → n ∈ after.1
  nodup : after.2.Nodup

private theorem VisitExtends.refl (state : List Nat × List Nat)
    (orderSeen : ∀ n, n ∈ state.2 → n ∈ state.1) (nodup : state.2.Nodup) :
    VisitExtends state state :=
  ⟨fun _ h => h, fun _ h => Or.inl h, orderSeen, nodup⟩

private theorem VisitExtends.trans {a b c : List Nat × List Nat}
    (ab : VisitExtends a b) (bc : VisitExtends b c) : VisitExtends a c := by
  refine ⟨fun n h => bc.seen n (ab.seen n h), ?_, bc.orderSeen, bc.nodup⟩
  intro n member
  rcases bc.fresh n member with prior | fresh
  · exact ab.fresh n prior
  · exact Or.inr (fun h => fresh (ab.seen n h))

private theorem visit_extends (g : Structure.Graph) :
    ∀ (fuel : Nat) (seen order : List Nat) (node : Nat),
      (∀ n, n ∈ order → n ∈ seen) → order.Nodup →
      VisitExtends (seen, order) (Structure.postorder.visit g fuel seen order node) := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen order node orderSeen nodup
      exact VisitExtends.refl _ orderSeen nodup
  | succ fuel ih =>
      intro seen order node orderSeen nodup
      rw [Structure.postorder.visit]
      by_cases visited : seen.contains node = true
      · rw [if_pos visited]
        exact VisitExtends.refl _ orderSeen nodup
      · rw [if_neg visited]
        have freshNode : node ∉ seen := by simpa only [List.contains_iff_mem] using visited
        have fold_extends : ∀ (nexts : List Nat) (state : List Nat × List Nat),
            (∀ n, n ∈ state.2 → n ∈ state.1) → state.2.Nodup →
            VisitExtends state (nexts.foldl
              (fun (acc : List Nat × List Nat) next =>
                Structure.postorder.visit g fuel acc.1 acc.2 next) state) := by
          intro nexts
          induction nexts with
          | nil => intro state hOrder hNodup; exact VisitExtends.refl _ hOrder hNodup
          | cons next rest ihRest =>
              intro state hOrder hNodup
              have step := ih state.1 state.2 next hOrder hNodup
              exact step.trans (ihRest _ step.orderSeen step.nodup)
        have expanded := fold_extends (g.succs node) (node :: seen, order)
          (fun n h => List.mem_cons_of_mem node (orderSeen n h)) nodup
        dsimp only at expanded ⊢
        generalize heq : List.foldl
          (fun (acc : List Nat × List Nat) next =>
            Structure.postorder.visit g fuel acc.1 acc.2 next)
          (node :: seen, order) (g.succs node) = after at expanded ⊢
        obtain ⟨seenAfter, orderAfter⟩ := after
        dsimp only at expanded ⊢
        have nodeNotOrdered : node ∉ orderAfter := by
          intro member
          rcases expanded.fresh node member with old | notSeen
          · exact freshNode (orderSeen node old)
          · exact notSeen List.mem_cons_self
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n h
          exact expanded.seen n (List.mem_cons_of_mem node h)
        · intro n h
          rcases List.mem_append.mp h with prior | last
          · rcases expanded.fresh n prior with old | fresh
            · exact Or.inl old
            · exact Or.inr (fun h => fresh (List.mem_cons_of_mem node h))
          · have eq : n = node := by simpa using last
            subst n
            exact Or.inr freshNode
        · intro n h
          rcases List.mem_append.mp h with prior | last
          · exact expanded.orderSeen n prior
          · have eq : n = node := by simpa using last
            subst n
            exact expanded.seen node List.mem_cons_self
        · exact List.nodup_append.mpr ⟨expanded.nodup, by simp,
            by intro n member m last eq
               have same : m = node := by simpa using last
               subst m; subst n; exact nodeNotOrdered member⟩

private theorem postorder_nodup (g : Structure.Graph) : (Structure.postorder g).Nodup := by
  exact (visit_extends g (g.size + 1) [] [] g.entry (by simp) (by simp)).nodup

/-- The pinned traversal never places a node twice in reverse postorder. -/
theorem rpo_nodup (g : Structure.Graph) : (Structure.rpo g).Nodup := by
  exact List.pairwise_reverse.mpr ((postorder_nodup g).imp (fun h => Ne.symm h))

private theorem findIdx_at_of_nodup : ∀ (xs : List Nat) (i : Nat) (hi : i < xs.length),
    xs.Nodup → xs.findIdx? (· = xs[i]) = some i := by
  intro xs
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
      intro i hi nodup
      obtain ⟨notMem, tailNodup⟩ := List.nodup_cons.mp nodup
      cases i with
      | zero => simp [List.findIdx?_cons]
      | succ i =>
          have tailBound : i < xs.length := by simpa using hi
          have headNe : x ≠ xs[i] := by
            intro same
            exact notMem (same ▸ List.getElem_mem tailBound)
          simpa [List.findIdx?_cons, headNe] using
            ih i tailBound tailNodup

private theorem index_rpo_at (g : Structure.Graph) (i : Nat) (hi : i < (Structure.rpo g).length) :
    Structure.index g (Structure.rpo g)[i] = i := by
  unfold Structure.index
  rw [findIdx_at_of_nodup _ i hi (rpo_nodup g)]

/-- Each node's computed index agrees with its unique position in reverse postorder. -/
theorem rpo_index_order (g : Structure.Graph) :
    (Structure.rpo g).Pairwise (fun a b => Structure.index g a < Structure.index g b) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ordered
  rw [index_rpo_at _ _ hi, index_rpo_at _ _ hj]
  exact ordered

/-- Filtering the computed order into dominator children retains strict index order. -/
theorem children_index_order (g : Structure.Graph) (node : Nat) :
    (Structure.children g node).Pairwise
      (fun a b => Structure.index g a < Structure.index g b) := by
  exact List.Pairwise.filter _ (rpo_index_order g)

private def mergeChildren (g : Structure.Graph) (node : Nat) : List Nat :=
  (Structure.children g node).filter fun c => Structure.isMerge g c || Structure.isLoopHeader g c

private theorem mergeChildren_index_order (g : Structure.Graph) (node : Nat) :
    (mergeChildren g node).Pairwise
      (fun a b => Structure.index g a < Structure.index g b) := by
  exact List.Pairwise.filter _ (children_index_order g node)

private theorem forward_target_later (g : Structure.Graph) (source target : Nat)
    (forward : Structure.isBackEdge g source target = false) :
    Structure.index g source < Structure.index g target := by
  simpa [Structure.isBackEdge] using forward

/-- The remaining graph-only obligations, independent of a body or its output. -/
private structure PlacementFacts (g : Structure.Graph) : Prop where
  childIndex : ∀ parent child, Structure.idom g child = some parent →
    Structure.index g parent ≤ Structure.index g child
  breakParent : ∀ source target, target ∈ g.succs source →
    (Structure.isBackEdge g source target && Structure.isLoopHeader g target &&
      Structure.dominates g target source) ≠ true →
    (Structure.isMerge g target || Structure.isLoopHeader g target) = true →
    ∃ parent, target ∈ mergeChildren g parent ∧
      Structure.dominates g parent source = true ∧
      Structure.index g source < Structure.index g target

def BodyScopedOnEdges (g : Structure.Graph)
    (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) : Prop :=
  ∀ (node : Nat) (transfer : Nat → Option (List Skeleton)) (blocks loops : List String)
    (own : List Skeleton),
    (∀ target control, target ∈ g.succs node → transfer target = some control →
      Skel.wellScopedList blocks loops control = true) →
    body node transfer = some own → Skel.wellScopedList blocks loops own = true

/-- Pending merge targets owned by proper dominator ancestors of this node. -/
private def OuterScope (g : Structure.Graph) (node : Nat) (blocks : List String) : Prop :=
  ∀ target parent, target ∈ mergeChildren g parent →
    Structure.dominates g parent node = true → parent ≠ node →
    Structure.index g node < Structure.index g target → Structure.blockLabel target ∈ blocks

private theorem outerScope_child {g : Structure.Graph} (facts : PlacementFacts g)
    {node child : Nat} {blocks childBlocks : List String}
    (up : Structure.idom g child = some node)
    (outer : OuterScope g node blocks)
    (inherited : ∀ label, label ∈ blocks → label ∈ childBlocks)
    (localTargets : ∀ target, target ∈ mergeChildren g node →
      Structure.index g child < Structure.index g target →
      Structure.blockLabel target ∈ childBlocks) :
    OuterScope g child childBlocks := by
  intro target parent member dom proper later
  rcases dominates_step up dom with same | parentDom
  · exact False.elim (proper same)
  · by_cases same : parent = node
    · subst parent
      exact localTargets target member later
    · apply inherited
      apply outer target parent member parentDom same
      exact Nat.lt_of_le_of_lt (facts.childIndex node child up) later

private theorem later_in_tail {g : Structure.Graph} {node target child : Nat}
    {before rest : List Nat}
    (split : mergeChildren g node = before ++ child :: rest)
    (member : target ∈ mergeChildren g node)
    (later : Structure.index g child < Structure.index g target) : target ∈ rest := by
  have ordered := mergeChildren_index_order g node
  rw [split] at ordered member
  rcases List.mem_append.mp member with early | remaining
  · have backward := (List.pairwise_append.mp ordered).2.2 target early child List.mem_cons_self
    omega
  · rcases List.mem_cons.mp remaining with same | tail
    · subst target
      omega
    · exact tail

private theorem emitNode_scoped_of_placement {g : Structure.Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (facts : PlacementFacts g) (scopedBody : BodyScopedOnEdges g body) :
    ∀ (fuel node : Nat) (blocks loops : List String) (out : List Skeleton),
      OuterScope g node blocks →
      (∀ target, Structure.dominates g target node = true →
        Structure.isLoopHeader g target = true → Structure.loopLabel target ∈ loops) →
      Structuring.emitNode g structuredShapes body fuel node = some out →
      Skel.wellScopedList blocks loops out = true := by
  intro fuel
  induction fuel with
  | zero => intro node blocks loops out _ _ emitted; simp [Structuring.emitNode] at emitted
  | succ fuel ih =>
      intro node blocks loops out hBlocks hLoops emitted
      rw [Structuring.emitNode] at emitted
      obtain ⟨own, hown, hfold⟩ := Option.bind_eq_some_iff.mp emitted
      -- Every merge child is a dominator-tree child of `node`.
      have mergeChild : ∀ m,
          m ∈ List.filter (fun c => Structure.isMerge g c || Structure.isLoopHeader g c)
            (Structure.children g node) → Structure.idom g m = some node := by
        intro m mem
        have inChildren := (List.mem_filter.mp mem).1
        unfold Structure.children at inChildren
        exact eq_of_beq (List.mem_filter.mp inChildren).2
      generalize mergesEq :
          List.filter (fun c => Structure.isMerge g c || Structure.isLoopHeader g c)
            (Structure.children g node) = merges at hfold mergeChild
      have mergeChildrenEq : mergeChildren g node = merges := mergesEq
      -- The fold: each merge child wraps everything emitted before it.
      have fold : ∀ (ms : List Nat) (acc result : List Skeleton),
          (∀ m, m ∈ ms → Structure.idom g m = some node) →
          (∃ before, mergeChildren g node = before ++ ms) →
          Skel.wellScopedList (ms.map Structure.blockLabel ++ blocks) loops acc = true →
          List.foldlM (fun acc m => do
              let inner ← Structuring.emitNode g structuredShapes body fuel m
              have placed : List Skeleton :=
                if Structure.isLoopHeader g m = true then
                  [structuredShapes.loop (Structure.loopLabel m) inner]
                else inner
              pure ([structuredShapes.merge (Structure.blockLabel m) acc] ++ placed))
            acc ms = some result →
          Skel.wellScopedList blocks loops result = true := by
        intro ms
        induction ms with
        | nil =>
            intro acc result _ _ scopedAcc folded
            simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at folded
            simpa [← folded] using scopedAcc
        | cons m rest ihFold =>
            intro acc result children suffix scopedAcc folded
            obtain ⟨before, split⟩ := suffix
            simp only [List.foldlM_cons] at folded
            obtain ⟨acc', step, rest'⟩ := Option.bind_eq_some_iff.mp folded
            obtain ⟨inner, hinner, hacc'⟩ := Option.bind_eq_some_iff.mp step
            simp only [Option.pure_def, Option.some.injEq] at hacc'
            subst hacc'
            refine ihFold _ result (fun m' mem => children m' (List.mem_cons_of_mem _ mem))
              ⟨before ++ [m], by simpa [List.append_assoc] using split⟩ ?_ rest'
            have upM : Structure.idom g m = some node := children m List.mem_cons_self
            have innerScoped :
                Skel.wellScopedList (rest.map Structure.blockLabel ++ blocks)
                  (if Structure.isLoopHeader g m = true then Structure.loopLabel m :: loops
                   else loops) inner = true :=
              ih m _ _ inner
                (outerScope_child facts upM hBlocks
                  (fun label h => List.mem_append_right _ h)
                  (fun target member later => List.mem_append_left _
                    (List.mem_map_of_mem (later_in_tail split member later))))
                (loops_of_child upM hLoops) hinner
            rw [Skel.wellScopedList_append]
            refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
            · simpa [Skel.wellScopedList, Skel.wellScoped, structuredShapes,
                Lowering.structuredMerge] using scopedAcc
            · by_cases header : Structure.isLoopHeader g m = true
              · rw [if_pos header] at innerScoped ⊢
                simpa [Skel.wellScopedList, Skel.wellScoped, structuredShapes,
                  Lowering.structuredLoop] using innerScoped
              · rw [if_neg header] at innerScoped ⊢
                exact innerScoped
      refine fold _ own out mergeChild ⟨[], by simpa using mergeChildrenEq⟩ ?_ hfold
      -- The body: its own statements are scoped once its transfers are.
      refine scopedBody node _ _ loops own ?_ hown
      intro target control edge transferred
      by_cases b1 : (Structure.isBackEdge g node target && Structure.isLoopHeader g target &&
          Structure.dominates g target node) = true
      · rw [if_pos b1] at transferred
        obtain ⟨headerPart, dom⟩ := Bool.and_eq_true_iff.mp b1
        obtain ⟨_, header⟩ := Bool.and_eq_true_iff.mp headerPart
        cases transferred
        simp only [Skel.wellScopedList, Skel.wellScoped, structuredShapes,
          Lowering.structuredContinue, Bool.and_true]
        exact List.contains_iff_mem.mpr (hLoops target dom header)
      · rw [if_neg b1] at transferred
        by_cases b2 : (Structure.isMerge g target || Structure.isLoopHeader g target) = true
        · rw [if_pos b2] at transferred
          cases transferred
          obtain ⟨parent, localMember, domParent, later⟩ :=
            facts.breakParent node target edge b1 b2
          have member : Structure.blockLabel target ∈
              List.map Structure.blockLabel merges ++ blocks := by
            by_cases same : parent = node
            · subst parent
              rw [mergeChildrenEq] at localMember
              exact List.mem_append_left _ (List.mem_map_of_mem localMember)
            · exact List.mem_append_right _ (hBlocks target parent localMember domParent same later)
          simp only [Skel.wellScopedList, Skel.wellScoped, structuredShapes,
            Lowering.structuredBreak, Bool.and_true]
          exact List.contains_iff_mem.mpr member
        · rw [if_neg b2] at transferred
          by_cases b3 : (Structure.idom g target == some node) = true
          · rw [if_pos b3] at transferred
            have notHeader : Structure.isLoopHeader g target = false := by
              simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at b2
              exact b2.2
            have scopedInner :=
              ih target (List.map Structure.blockLabel merges ++ blocks)
                (if Structure.isLoopHeader g target = true then
                   Structure.loopLabel target :: loops else loops) control
                (outerScope_child facts (eq_of_beq b3) hBlocks
                  (fun label h => List.mem_append_right _ h)
                  (fun target member _ => List.mem_append_left _
                    (List.mem_map_of_mem (mergeChildrenEq ▸ member))))
                (loops_of_child (eq_of_beq b3) hLoops) transferred
            rw [if_neg (by simp [notHeader])] at scopedInner
            exact scopedInner
          · rw [if_neg b3] at transferred
            cases transferred

private theorem emitWith_scoped_of_placement {g : Structure.Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (facts : PlacementFacts g) (scopedBody : BodyScopedOnEdges g body) {out : List Skeleton}
    (emitted : Structuring.emitWith g structuredShapes body = some out) :
    Skel.wellScopedList [] [] out = true := by
  unfold Structuring.emitWith at emitted
  obtain ⟨_, _, emitted⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨inner, hinner, hout⟩ := Option.bind_eq_some_iff.mp emitted
  simp only [Option.pure_def, Option.some.injEq] at hout
  have hLoops : ∀ target, Structure.dominates g target g.entry = true →
      Structure.isLoopHeader g target = true →
      Structure.loopLabel target ∈
        (if Structure.isLoopHeader g g.entry = true then [Structure.loopLabel g.entry] else []) := by
    intro target dom header
    have targetEq := dominates_entry dom
    subst targetEq
    rw [if_pos header]
    exact List.mem_cons_self
  have innerScoped := emitNode_scoped_of_placement facts scopedBody (g.size + 1) g.entry []
    (if Structure.isLoopHeader g g.entry = true then [Structure.loopLabel g.entry] else []) inner
    (fun _ parent _ dom proper _ => False.elim (proper (dominates_entry dom))) hLoops hinner
  by_cases header : Structure.isLoopHeader g g.entry = true
  · rw [if_pos header] at hout innerScoped
    subst hout
    simpa [Skel.wellScopedList, Skel.wellScoped, structuredShapes, Lowering.structuredLoop]
      using innerScoped
  · rw [if_neg header] at hout innerScoped
    subst hout
    exact innerScoped

private def edgeMove (block : RawBlock String)
    (move : BlockId → List Slot → Option (List Skeleton))
    (target : BlockId) (values : List Slot) : Option (List Skeleton) :=
  if target ∈ block.term.successors then move target values else none

private theorem skeletonBlockWith_edgeMove (table : List OpSpec) (interrupts : Bool)
    (block : RawBlock String) (move : BlockId → List Slot → Option (List Skeleton)) :
    Flow.skeletonBlockWith table interrupts block (edgeMove block move) =
      Flow.skeletonBlockWith table interrupts block move := by
  cases h : block.term <;> simp [Flow.skeletonBlockWith, h, edgeMove, RawTerm.successors]

private theorem skeletonBlockWith_scoped_on_edges (table : List OpSpec) (interrupts : Bool)
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

private def actualBody (table : List OpSpec) (interrupts : Bool) (blocks : List (RawBlock String))
    (i : Nat) (transfer : Nat → Option (List Skeleton)) : Option (List Skeleton) := do
  let block ← blocks[i]?
  Flow.skeletonBlockWith table interrupts block fun target values => do
    let t ← Flow.position blocks target
    let control ← transfer t
    pure (Lowering.paramMove block.id target values ++ control)

/-- The real lowerer satisfies the proposed hypothesis, including interrupts. -/
private theorem actualBody_scoped_on_edges (table : List OpSpec) (interrupts : Bool)
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

private theorem actualBody_exact (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId) :
    Flow.skeletonBody table interrupts blocks entry =
      Structuring.emitWith (Flow.graphOf blocks entry) structuredShapes
        (actualBody table interrupts blocks) := by rfl

private theorem skeletonBody_scoped_of_placement (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId)
    (facts : PlacementFacts (Flow.graphOf blocks entry)) {out : List Skeleton}
    (emitted : Flow.skeletonBody table interrupts blocks entry = some out) :
    Skel.wellScopedList [] [] out = true := by
  rw [actualBody_exact] at emitted
  exact emitWith_scoped_of_placement facts (actualBody_scoped_on_edges table interrupts blocks entry)
    emitted

private def SourceClosed (g : Structure.Graph) : Prop :=
  ∀ source target, target ∈ g.succs source → source < g.size

/-- The remaining computed-dominator obligations; this record is a premise,
not a claim that the algorithm establishes either field. -/
structure DominatorFacts (g : Structure.Graph) : Prop where
  childIndex : ∀ parent child, Structure.idom g child = some parent →
    Structure.index g parent ≤ Structure.index g child
  forwardJoinParent : ∀ source target, target ∈ g.succs source →
    Structure.isBackEdge g source target = false →
    (Structure.isMerge g target || Structure.isLoopHeader g target) = true →
    ∃ parent, Structure.idom g target = some parent ∧
      Structure.dominates g parent source = true

private theorem reachable_of_reducible {g : Structure.Graph} (reducible : Structure.reducible g = true)
    {node : Nat} (bound : node < g.size) : node ∈ Structure.rpo g := by
  have nodeChecks := List.all_eq_true.mp reducible node (List.mem_range.mpr bound)
  exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp nodeChecks).1

private theorem backward_dominates_of_reducible {g : Structure.Graph}
    (reducible : Structure.reducible g = true) {source target : Nat}
    (bound : source < g.size) (edge : target ∈ g.succs source)
    (backward : Structure.isBackEdge g source target = true) :
    Structure.dominates g target source = true := by
  have nodeChecks := List.all_eq_true.mp reducible source (List.mem_range.mpr bound)
  have edgeCheck := List.all_eq_true.mp (Bool.and_eq_true_iff.mp nodeChecks).2 target edge
  simpa [backward] using edgeCheck

private theorem backward_target_header {g : Structure.Graph} {source target : Nat}
    (reachable : source ∈ Structure.rpo g) (edge : target ∈ g.succs source)
    (backward : Structure.isBackEdge g source target = true) :
    Structure.isLoopHeader g target = true := by
  apply List.any_eq_true.mpr
  refine ⟨source, ?_, backward⟩
  exact List.mem_filter.mpr ⟨reachable, List.contains_iff_mem.mpr edge⟩

private theorem break_target_forward {g : Structure.Graph} (reducible : Structure.reducible g = true)
    {source target : Nat} (bound : source < g.size) (edge : target ∈ g.succs source)
    (notContinue : (Structure.isBackEdge g source target && Structure.isLoopHeader g target &&
      Structure.dominates g target source) ≠ true) :
    Structure.isBackEdge g source target = false := by
  apply Bool.eq_false_iff.mpr
  intro backward
  have header := backward_target_header (reachable_of_reducible reducible bound) edge backward
  have dom := backward_dominates_of_reducible reducible bound edge backward
  exact notContinue (by simp [backward, header, dom])

private theorem placementFacts_of_reducible {g : Structure.Graph} (closed : GraphClosed g)
    (sources : SourceClosed g) (reducible : Structure.reducible g = true)
    (dominators : DominatorFacts g) : PlacementFacts g := by
  refine ⟨dominators.childIndex, ?_⟩
  intro source target edge notContinue join
  have forward := break_target_forward reducible (sources source target edge) edge notContinue
  obtain ⟨parent, up, dom⟩ := dominators.forwardJoinParent source target edge forward join
  refine ⟨parent, ?_, dom, forward_target_later g source target forward⟩
  apply List.mem_filter.mpr
  refine ⟨?_, join⟩
  apply List.mem_filter.mpr
  refine ⟨reachable_of_reducible reducible (closed source target edge), ?_⟩
  show (Structure.idom g target == some parent) = true
  rw [up]
  change decide (parent = parent) = true
  exact decide_eq_true rfl

private theorem graphOf_sourceClosed (blocks : List (RawBlock String)) (entry : BlockId) :
    SourceClosed (Flow.graphOf blocks entry) := by
  intro source target member
  unfold Flow.graphOf at member ⊢
  dsimp only at member ⊢
  cases found : blocks[source]? with
  | none => rw [found] at member; simp at member
  | some block =>
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
      exact bound

private theorem emitWith_reducible {α : Type} (g : Structure.Graph) (shapes : Structuring.Shapes α)
    (body : Nat → (Nat → Option (List α)) → Option (List α)) {out : List α}
    (emitted : Structuring.emitWith g shapes body = some out) : Structure.reducible g = true := by
  cases h : Structure.reducible g with
  | false =>
      have never : Structuring.emitWith g shapes body = none := by
        unfold Structuring.emitWith
        rw [h]
        rfl
      rw [never] at emitted
      contradiction
  | true => rfl

/-- Successful emission is strictly scoped under the corrected edge-local body
premise and the two explicit computed-dominator obligations. -/
theorem emitWith_wellScoped_of_dominators {g : Structure.Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (closed : GraphClosed g)
    (sourceBounded : ∀ source target, target ∈ g.succs source → source < g.size)
    (dominators : DominatorFacts g) (scopedBody : BodyScopedOnEdges g body)
    {out : List Skeleton}
    (emitted : Structuring.emitWith g structuredShapes body = some out) :
    Skel.wellScopedList [] [] out = true := by
  exact emitWith_scoped_of_placement
    (placementFacts_of_reducible closed sourceBounded (emitWith_reducible _ _ _ emitted) dominators)
    scopedBody emitted

/-- The actual structured body has every break and continue inside its binder,
conditional on the two computed-dominator facts. Interrupt nodes do not change
this lexical property; their denotation remains a separate obligation. -/
theorem skeletonBody_wellScoped_of_dominators (table : List OpSpec) (interrupts : Bool)
    (blocks : List (RawBlock String)) (entry : BlockId)
    (dominators : DominatorFacts (Flow.graphOf blocks entry)) {out : List Skeleton}
    (emitted : Flow.skeletonBody table interrupts blocks entry = some out) :
    Skel.wellScopedList [] [] out = true := by
  have emitted' := emitted
  rw [actualBody_exact] at emitted'
  have reducible := emitWith_reducible _ _ _ emitted'
  exact skeletonBody_scoped_of_placement table interrupts blocks entry
    (placementFacts_of_reducible (graphOf_closed blocks entry) (graphOf_sourceClosed blocks entry)
      reducible dominators) emitted

end Effect4.Target.Structured
