import Effect4.Target.TypeScript.StructuredLower

/-!
# Target.TypeScript.StructureLaws

Owner: what Effect4 can prove about the emitted structured form (plan packet
P-T9b, `docs/TRACE-DAG.md` edge `structured-agreement`).

`TypeScript.Structure.emitWith` is owned by the pinned `typescript` package
and cannot be edited from here, so its laws are stated in Effect4 over the
package's graph analysis, Effect4's `Structuring.emitWith` (the same algorithm
with the statement type as a parameter, pinned to the package's emitter at
`Stmt` by `Structuring.emitWith_eq`) and Effect4's own `structuredShapes`.

The property proved here is *label well-scoping*: a `continue l` must sit
inside a `while l`, and a `break l` inside a `label l:` block. Row
`E4-TARGET-CE-013` was exactly a violation of the first half — the entry
block, when it was a loop header, was not wrapped in its own loop, so the
`continue W<entry>` that `emitNode` emits for the back edge had no binder.
`emitWith` now wraps it, and `emitWith_wellScoped` below is the theorem that
makes that wrapping load-bearing.

Since packet D3 the law is stated twice, over the two carriers, and the second
follows from the first:

* over `Skeleton` (`Skel.wellScoped`), because that is what the structured
  lowering now emits and what the agreement theorems are stated over; and
* over `Stmt` (`wellScoped`), the property of the *printed* program, reached
  from the skeleton by `render_wellScoped`: `render` maps each labelled control
  shape to its spelling and introduces no label of its own, so scoping is
  preserved on the nose.

What is proved and what is not:

* the `continue` half is proved outright, and needs neither reducibility nor
  the correctness of the dominator computation: `emitNode` guards every
  `continue` with `Structure.dominates g target current`, and `dominates` is
  by definition a walk up the `idom` chain — the same chain `emitNode`'s own
  recursion descends;
* the `break` half is proved only up to *naming*: every emitted `break` names
  `blockLabel t` for a node `t` of the graph. Proving that the enclosing
  `label L<t>:` is always present needs two facts about the package's
  algorithms that Effect4 cannot establish — that `idom t` dominates every
  predecessor of `t` (correctness of the Cooper–Harvey–Kennedy iteration) and
  that a forward edge's target comes later in reverse postorder. Both are owed
  by `lean4-typescript`; `BreakScopedStatement` records the exact statement.
-/

set_option autoImplicit false

open TypeScript
open Effects
open Effect4.Target.EffectV4

namespace Effect4.Target.Structured

/-! ## Label well-scoping of a statement list

`blocks` are the labels a `break` may name (introduced by `label l: { … }`);
`loops` are the labels a `continue` may name (introduced by
`l: while (true) { … }`). A nested generator (`scopedGen`) is a function
boundary: no labelled jump crosses it, so both lists reset. `Stmt` is a nested
inductive, so the three recursions are mutual and structural, exactly as the
package's own `BEq` is. -/

mutual

/-- Every labelled jump in a statement names a label its binder is in scope for. -/
def wellScoped (blocks loops : List String) (stmt : Stmt) : Bool :=
  match stmt with
  | .whileTrue (some label) body => wellScopedList blocks (label :: loops) body
  | .whileTrue none body => wellScopedList blocks loops body
  | .labelled label body => wellScopedList (label :: blocks) loops body
  | .ifElse _ thenBranch elseBranch =>
      wellScopedList blocks loops thenBranch && wellScopedList blocks loops elseBranch
  | .switch _ cases => wellScopedCases blocks loops cases
  | .scopedGen _ body _ => wellScopedList [] [] body
  | .breakTo (some label) => blocks.contains label
  | .continueTo (some label) => loops.contains label
  | _ => true
termination_by structural stmt

/-- `wellScoped` over a statement list. -/
def wellScopedList (blocks loops : List String) (stmts : List Stmt) : Bool :=
  match stmts with
  | [] => true
  | s :: rest => wellScoped blocks loops s && wellScopedList blocks loops rest
termination_by structural stmts

/-- `wellScoped` over the arms of a `switch`. -/
def wellScopedCases (blocks loops : List String) (cases : List (Nat × List Stmt)) : Bool :=
  match cases with
  | [] => true
  | (_, body) :: rest => wellScopedList blocks loops body && wellScopedCases blocks loops rest
termination_by structural cases

end

/-! ## Label well-scoping of a control skeleton

The same predicate one level up. A `dispatchLoop` binds no label — the
`gotoBlock` inside it is an unlabelled `continue`, always in scope — and
`enterScoped` is the function boundary. -/

namespace Skel

mutual

/-- Every labelled jump in a skeleton names a label its binder is in scope for. -/
def wellScoped (blocks loops : List String) (node : Skeleton) : Bool :=
  match node with
  | .loop label body => wellScopedList blocks (label :: loops) body
  | .labelled label body => wellScopedList (label :: blocks) loops body
  | .dispatchLoop _ cases => wellScopedCases blocks loops cases
  | .decide _ _ onTrue onFalse =>
      wellScopedList blocks loops onTrue && wellScopedList blocks loops onFalse
  | .enterScoped _ body => wellScopedList [] [] body
  | .breakTo label => blocks.contains label
  | .continueTo label => loops.contains label
  | _ => true
termination_by structural node

/-- `Skel.wellScoped` over a skeleton list. -/
def wellScopedList (blocks loops : List String) (nodes : List Skeleton) : Bool :=
  match nodes with
  | [] => true
  | node :: rest => wellScoped blocks loops node && wellScopedList blocks loops rest
termination_by structural nodes

/-- `Skel.wellScoped` over the arms of a dispatch switch. -/
def wellScopedCases (blocks loops : List String) (cases : List (Nat × List Skeleton)) : Bool :=
  match cases with
  | [] => true
  | (_, body) :: rest => wellScopedList blocks loops body && wellScopedCases blocks loops rest
termination_by structural cases

end

/-- `Skel.wellScopedList` distributes over `++`. -/
theorem wellScopedList_append (blocks loops : List String) :
    ∀ (left right : List Skeleton),
      wellScopedList blocks loops (left ++ right) =
        (wellScopedList blocks loops left && wellScopedList blocks loops right)
  | [], right => by simp [wellScopedList]
  | s :: rest, right => by
      simp [wellScopedList, wellScopedList_append blocks loops rest right, Bool.and_assoc]

theorem wellScopedList_of_forall {blocks loops : List String} :
    ∀ (nodes : List Skeleton), (∀ s, s ∈ nodes → wellScoped blocks loops s = true) →
      wellScopedList blocks loops nodes = true
  | [], _ => by simp [wellScopedList]
  | s :: rest, all => by
      rw [wellScopedList]
      exact Bool.and_eq_true_iff.mpr
        ⟨all s List.mem_cons_self,
         wellScopedList_of_forall rest fun t mem => all t (List.mem_cons_of_mem _ mem)⟩

end Skel

/-! ## `dominates` is a walk up the `idom` chain

`Structure.dominates g a b` is *defined* as a fuel-bounded walk from `b` up the
`idom` chain looking for `a`. That is the same chain `emitNode`'s recursion
descends, so the `continue` half needs no theorem about what the chain means —
only these two facts about the walk. -/

private theorem walk_mono (g : Structure.Graph) (a : Nat) :
    ∀ (fuel node : Nat), Structure.dominates.walk g a fuel node = true →
      Structure.dominates.walk g a (fuel + 1) node = true := by
  intro fuel
  induction fuel with
  | zero => intro node walked; simp [Structure.dominates.walk] at walked
  | succ fuel ih =>
      intro node walked
      rw [Structure.dominates.walk] at walked ⊢
      by_cases same : node = a
      · simp [same]
      · simp only [same, if_false] at walked ⊢
        cases up : Structure.idom g node with
        | none => rw [up] at walked; exact walked
        | some parent => rw [up] at walked; exact ih parent walked

/-- The dominator walk from a child either stops at the child or continues from
its immediate dominator. -/
theorem dominates_step {g : Structure.Graph} {source child parent : Nat}
    (up : Structure.idom g child = some parent)
    (dom : Structure.dominates g source child = true) :
    source = child ∨ Structure.dominates g source parent = true := by
  by_cases same : child = source
  · exact Or.inl same.symm
  · right
    unfold Structure.dominates at dom ⊢
    rw [Structure.dominates.walk] at dom
    simp only [same, if_false, up] at dom
    exact walk_mono g source g.size parent dom

/-- Nothing but the entry dominates the entry: `idom` of the entry is `none`. -/
theorem dominates_entry {g : Structure.Graph} {source : Nat}
    (dom : Structure.dominates g source g.entry = true) : source = g.entry := by
  by_cases same : g.entry = source
  · exact same.symm
  · exfalso
    unfold Structure.dominates at dom
    rw [Structure.dominates.walk] at dom
    simp only [same, if_false] at dom
    have entryIdom : Structure.idom g g.entry = none := by simp [Structure.idom]
    rw [entryIdom] at dom
    exact Bool.false_ne_true dom

/-! ## A `break` target is a node of the graph

`emitNode` emits a `break` only to a merge node or a loop header, and both are
detected from `preds`, which is built from the graph's own successor lists. -/

/-- Successor lists stay inside the node range. True of `Flow.graphOf` by
construction, since its successors are `position`s in the block list. -/
def GraphClosed (g : Structure.Graph) : Prop :=
  ∀ source target, target ∈ g.succs source → target < g.size

theorem mem_succs_of_mem_preds {g : Structure.Graph} {target source : Nat}
    (mem : source ∈ Structure.preds g target) : target ∈ g.succs source := by
  unfold Structure.preds at mem
  exact List.contains_iff_mem.mp (List.mem_filter.mp mem).2

/-- A merge node or loop header is the target of a declared edge. -/
theorem exists_pred_of_transferTarget {g : Structure.Graph} {target : Nat}
    (shape : Structure.isMerge g target = true ∨ Structure.isLoopHeader g target = true) :
    ∃ source, target ∈ g.succs source := by
  have nonempty : Structure.preds g target ≠ [] := by
    rcases shape with merge | header
    · unfold Structure.isMerge at merge
      intro empty
      rw [empty] at merge
      simp at merge
    · unfold Structure.isLoopHeader at header
      intro empty
      rw [empty] at header
      simp at header
  cases predsEq : Structure.preds g target with
  | nil => exact absurd predsEq nonempty
  | cons source rest =>
      exact ⟨source, mem_succs_of_mem_preds (by rw [predsEq]; exact List.mem_cons_self)⟩

/-- Every `break` `emitNode` can emit names a node of the graph. -/
theorem lt_size_of_transferTarget {g : Structure.Graph} (closed : GraphClosed g) {target : Nat}
    (shape : Structure.isMerge g target = true ∨ Structure.isLoopHeader g target = true) :
    target < g.size := by
  obtain ⟨source, mem⟩ := exists_pred_of_transferTarget shape
  exact closed source target mem

/-! ## The emission is well scoped -/

/-- The caller's block body introduces no labelled jump of its own: whatever it
returns is well scoped as soon as every control transfer it was handed is.
Effect4's `Flow.skeletonBody` satisfies this — `skeletonBlockWith` splices the
transfer nodes and adds only assignments, performs and decisions. -/
def BodyScoped (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)) : Prop :=
  ∀ (node : Nat) (transfer : Nat → Option (List Skeleton)) (blocks loops : List String)
    (own : List Skeleton),
    (∀ target control, transfer target = some control →
      Skel.wellScopedList blocks loops control = true) →
    body node transfer = some own → Skel.wellScopedList blocks loops own = true

/-- `wellScopedList` distributes over `++`. -/
theorem wellScopedList_append (blocks loops : List String) :
    ∀ (left right : List Stmt),
      wellScopedList blocks loops (left ++ right) =
        (wellScopedList blocks loops left && wellScopedList blocks loops right)
  | [], right => by simp [wellScopedList]
  | s :: rest, right => by
      simp [wellScopedList, wellScopedList_append blocks loops rest right, Bool.and_assoc]

/-- The scope of a merge or inlined child of `node`: the child adds its own loop
label when it is a loop header, and inherits everything else. -/
theorem loops_of_child {g : Structure.Graph} {node child : Nat} {loops : List String}
    (up : Structure.idom g child = some node)
    (hLoops : ∀ target, Structure.dominates g target node = true →
      Structure.isLoopHeader g target = true → Structure.loopLabel target ∈ loops) :
    ∀ target, Structure.dominates g target child = true →
      Structure.isLoopHeader g target = true →
      Structure.loopLabel target ∈
        (if Structure.isLoopHeader g child = true then Structure.loopLabel child :: loops
         else loops) := by
  intro target dom header
  rcases dominates_step up dom with rfl | domNode
  · rw [if_pos header]
    exact List.mem_cons_self
  · by_cases childHeader : Structure.isLoopHeader g child = true
    · rw [if_pos childHeader]
      exact List.mem_cons_of_mem _ (hLoops target domNode header)
    · rw [if_neg childHeader]
      exact hLoops target domNode header

/-- **The emission is well scoped, node by node.** Every `continue l` the
structured form emits sits inside its `while l`; every `break l` names a block
label of the graph. -/
theorem emitNode_wellScoped {g : Structure.Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (closed : GraphClosed g) (scopedBody : BodyScoped body) :
    ∀ (fuel node : Nat) (blocks loops : List String) (out : List Skeleton),
      (∀ target, target < g.size → Structure.blockLabel target ∈ blocks) →
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
      -- The fold: each merge child wraps everything emitted before it.
      have fold : ∀ (ms : List Nat) (acc result : List Skeleton),
          (∀ m, m ∈ ms → Structure.idom g m = some node) →
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
            intro acc result _ scopedAcc folded
            simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at folded
            simpa [← folded] using scopedAcc
        | cons m rest ihFold =>
            intro acc result children scopedAcc folded
            simp only [List.foldlM_cons] at folded
            obtain ⟨acc', step, rest'⟩ := Option.bind_eq_some_iff.mp folded
            obtain ⟨inner, hinner, hacc'⟩ := Option.bind_eq_some_iff.mp step
            simp only [Option.pure_def, Option.some.injEq] at hacc'
            subst hacc'
            refine ihFold _ result (fun m' mem => children m' (List.mem_cons_of_mem _ mem)) ?_ rest'
            have upM : Structure.idom g m = some node := children m List.mem_cons_self
            have innerScoped :
                Skel.wellScopedList (rest.map Structure.blockLabel ++ blocks)
                  (if Structure.isLoopHeader g m = true then Structure.loopLabel m :: loops
                   else loops) inner = true :=
              ih m _ _ inner
                (fun target lt => List.mem_append_right _ (hBlocks target lt))
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
      refine fold _ own out mergeChild ?_ hfold
      -- The body: its own statements are scoped once its transfers are.
      refine scopedBody node _ _ loops own ?_ hown
      intro target control transferred
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
          have lt : target < g.size :=
            lt_size_of_transferTarget closed (Bool.or_eq_true_iff.mp b2)
          have member : Structure.blockLabel target ∈
              List.map Structure.blockLabel merges ++ blocks :=
            List.mem_append_right _ (hBlocks target lt)
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
                (fun t lt => List.mem_append_right _ (hBlocks t lt))
                (loops_of_child (eq_of_beq b3) hLoops) transferred
            rw [if_neg (by simp [notHeader])] at scopedInner
            exact scopedInner
          · rw [if_neg b3] at transferred
            cases transferred

/-! ## The whole emission -/

/-- The block labels of the graph's own nodes. -/
def blockLabels (g : Structure.Graph) : List String :=
  (List.range g.size).map Structure.blockLabel

theorem mem_blockLabels {g : Structure.Graph} {target : Nat} (lt : target < g.size) :
    Structure.blockLabel target ∈ blockLabels g :=
  List.mem_map_of_mem (List.mem_range.mpr lt)

/-- **The structured form is `continue`-scoped.** Every `continue l` in the
emitted skeleton sits inside a `while l`, and every `break l` names a block
label of the graph.

This is where `emitWith`'s wrapping of a loop-header entry is load-bearing:
`emitNode` emits `continue W<entry>` for the entry's back edge, and the only
binder for it is that wrapper. `E4-TARGET-CE-013` was the emission without it,
and the theorem is false for that emission. Neither reducibility nor the
correctness of the dominator computation is needed: `Structure.dominates` is by
definition a walk up the `idom` chain, which is the chain `emitNode` descends. -/
theorem emitWith_wellScoped {g : Structure.Graph}
    {body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton)}
    (closed : GraphClosed g) (scopedBody : BodyScoped body) {out : List Skeleton}
    (emitted : Structuring.emitWith g structuredShapes body = some out) :
    Skel.wellScopedList (blockLabels g) [] out = true := by
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
  have innerScoped := emitNode_wellScoped closed scopedBody (g.size + 1) g.entry (blockLabels g)
    (if Structure.isLoopHeader g g.entry = true then [Structure.loopLabel g.entry] else []) inner
    (fun _ lt => mem_blockLabels lt) hLoops hinner
  by_cases header : Structure.isLoopHeader g g.entry = true
  · rw [if_pos header] at hout innerScoped
    subst hout
    simpa [Skel.wellScopedList, Skel.wellScoped, structuredShapes, Lowering.structuredLoop]
      using innerScoped
  · rw [if_neg header] at hout innerScoped
    subst hout
    exact innerScoped

/-- **The open half**, stated exactly. The `break` targets are proved above only
up to naming; that every `break L<t>` is enclosed by its `label L<t>:` is the
statement below, with the empty initial block scope.

Discharging it needs two facts about the pinned `typescript` package that
Effect4 cannot establish over the package's definitions:

1. `Structure.idom t` is on the `idom` chain of every predecessor of `t` — the
   correctness of the Cooper–Harvey–Kennedy iteration in `Structure.idoms`;
2. a forward edge's target comes later in `Structure.rpo` than its source, and
   `Structure.children` is listed in that order — so that the child of
   `idom t` on the path to the source is folded before `t`, which is what puts
   the source inside `label L<t>:`.

With (1) and (2), the induction above goes through with the block scope
`(children g a).filter … |>.drop …` instead of the permissive `blockLabels g`.
Owed by `lean4-typescript`; recorded on the `structured-agreement` row of
`docs/TRACE-DAG.md`. -/
def BreakScopedStatement : Prop :=
  ∀ (g : Structure.Graph) (body : Nat → (Nat → Option (List Skeleton)) → Option (List Skeleton))
    (out : List Skeleton),
    GraphClosed g → BodyScoped body → Structure.reducible g = true →
    Structuring.emitWith g structuredShapes body = some out →
    Skel.wellScopedList [] [] out = true

/-! ## Effect4's own body satisfies the hypothesis

`BodyScoped` is not an assumption Effect4 leaves hanging: `Flow.skeletonBody`
reaches the control transfers only through `transfer`, and every other node
`skeletonBlockWith` emits — a return, a perform, a decision, and the parameter
moves — carries no label. -/

theorem wellScopedList_of_forall {blocks loops : List String} :
    ∀ (stmts : List Stmt), (∀ s, s ∈ stmts → wellScoped blocks loops s = true) →
      wellScopedList blocks loops stmts = true
  | [], _ => by simp [wellScopedList]
  | s :: rest, all => by
      rw [wellScopedList]
      exact Bool.and_eq_true_iff.mpr
        ⟨all s List.mem_cons_self,
         wellScopedList_of_forall rest fun t mem => all t (List.mem_cons_of_mem _ mem)⟩

theorem paramMove_wellScoped (blocks loops : List String) (source target : BlockId)
    (values : List Slot) :
    Skel.wellScopedList blocks loops (Lowering.paramMove source target values) = true := by
  have assigns : ∀ (l : List (Nat × Slot)) (f : Nat × Slot → Skeleton),
      (∀ index value, Skel.wellScoped blocks loops (f (index, value)) = true) →
      Skel.wellScopedList blocks loops (l.map f) = true := by
    intro l f jumpFree
    refine Skel.wellScopedList_of_forall _ ?_
    intro s mem
    obtain ⟨⟨index, value⟩, _, rfl⟩ := List.mem_map.mp mem
    exact jumpFree index value
  unfold Lowering.paramMove
  split
  · rw [Skel.wellScopedList_append]
    refine Bool.and_eq_true_iff.mpr ⟨assigns _ _ ?_, assigns _ _ ?_⟩ <;>
      intro index value <;> simp [Skel.wellScoped]
  · exact assigns _ _ (by intro index value; simp [Skel.wellScoped])

/-- Every node `skeletonBlockWith` emits of its own carries no label, so its
result is well scoped as soon as the transfers it was handed are. -/
theorem skeletonBlockWith_wellScoped (table : List OpSpec) (block : RawBlock String)
    (move : BlockId → List Slot → Option (List Skeleton)) (blocks loops : List String)
    (moveScoped : ∀ target values control, move target values = some control →
      Skel.wellScopedList blocks loops control = true)
    {own : List Skeleton} (lowered : Flow.skeletonBlockWith table block move = some own) :
    Skel.wellScopedList blocks loops own = true := by
  have entered : ∀ body : List Skeleton, Skel.wellScopedList blocks loops body = true →
      Skel.wellScopedList blocks loops (Skeleton.enterBlock block.id :: body) = true := by
    intro body ok
    rw [Skel.wellScopedList]
    exact Bool.and_eq_true_iff.mpr ⟨by simp [Skel.wellScoped], ok⟩
  unfold Flow.skeletonBlockWith at lowered
  cases term : block.term with
  | ret value =>
      rw [term] at lowered
      simp only [Option.some.injEq] at lowered
      subst lowered
      exact entered _ (by simp [Skel.wellScopedList, Skel.wellScoped, Lowering.flowRet])
  | jump target args =>
      rw [term] at lowered
      obtain ⟨control, moved, rfl⟩ := Option.map_eq_some_iff.mp lowered
      exact entered _ (moveScoped _ _ _ moved)
  | perform operation request target args =>
      rw [term] at lowered
      obtain ⟨spec, _, lowered⟩ := Option.bind_eq_some_iff.mp lowered
      cases kind : spec.kind with
      | family =>
          rw [kind] at lowered
          obtain ⟨head, headEq, lowered⟩ := Option.bind_eq_some_iff.mp lowered
          obtain ⟨rest, hrest, headed⟩ := Option.bind_eq_some_iff.mp lowered
          injection headEq with headEq
          injection headed with headed
          subst headEq
          subst headed
          refine entered _ ?_
          rw [Skel.wellScopedList]
          exact Bool.and_eq_true_iff.mpr
            ⟨by simp [Skel.wellScoped, Lowering.flowPerform], moveScoped _ _ _ hrest⟩
      | atom =>
          rw [kind] at lowered
          obtain ⟨head, headEq, lowered⟩ := Option.bind_eq_some_iff.mp lowered
          obtain ⟨rest, hrest, headed⟩ := Option.bind_eq_some_iff.mp lowered
          injection headEq with headEq
          injection headed with headed
          subst headEq
          subst headed
          refine entered _ ?_
          rw [Skel.wellScopedList]
          exact Bool.and_eq_true_iff.mpr
            ⟨by simp [Skel.wellScoped, Lowering.flowAtom], moveScoped _ _ _ hrest⟩
      | lit value =>
          rw [kind] at lowered
          obtain ⟨head, headEq, lowered⟩ := Option.bind_eq_some_iff.mp lowered
          obtain ⟨spelling, _, spelled⟩ := Option.map_eq_some_iff.mp headEq
          obtain ⟨rest, hrest, headed⟩ := Option.bind_eq_some_iff.mp lowered
          injection headed with headed
          subst spelled
          subst headed
          refine entered _ ?_
          rw [Skel.wellScopedList]
          exact Bool.and_eq_true_iff.mpr
            ⟨by simp [Skel.wellScoped, Lowering.flowLiteral], moveScoped _ _ _ hrest⟩
  | choose decision left right args =>
      rw [term] at lowered
      obtain ⟨toLeft, hleft, lowered⟩ := Option.bind_eq_some_iff.mp lowered
      obtain ⟨toRight, hright, lowered⟩ := Option.bind_eq_some_iff.mp lowered
      simp only [Option.some.injEq] at lowered
      subst lowered
      refine entered _ ?_
      simp only [Lowering.chooseIf, Skel.wellScopedList, Skel.wellScoped, Bool.and_true]
      exact Bool.and_eq_true_iff.mpr ⟨moveScoped _ _ _ hleft, moveScoped _ _ _ hright⟩

/-- `List.findIdx?` returns a position inside the list. Reproved by induction:
the library form goes through `List.findIdx?_eq_some_iff_findIdx_eq`, which
carries `Classical.choice`. -/
private theorem findIdx?_lt_length {α : Type} {p : α → Bool} :
    ∀ {l : List α} {i : Nat}, l.findIdx? p = some i → i < l.length
  | [], i, found => by rw [List.findIdx?_nil] at found; cases found
  | a :: rest, i, found => by
      rw [List.findIdx?_cons] at found
      by_cases head : p a = true
      · rw [if_pos head] at found
        injection found with found
        subst found
        simp
      · rw [if_neg head] at found
        obtain ⟨j, tail, rfl⟩ := Option.map_eq_some_iff.mp found
        have := findIdx?_lt_length tail
        simp only [List.length_cons]
        omega

/-- `Flow.graphOf` keeps every successor inside the node range: its successors
are `position`s in the block list. -/
theorem graphOf_closed (blocks : List (RawBlock String)) (entry : BlockId) :
    GraphClosed (Flow.graphOf blocks entry) := by
  intro source target mem
  unfold Flow.graphOf at mem ⊢
  simp only at mem ⊢
  cases found : blocks[source]? with
  | none => rw [found] at mem; simp at mem
  | some block =>
      rw [found] at mem
      obtain ⟨successor, _, positioned⟩ := List.mem_filterMap.mp mem
      unfold Flow.position at positioned
      exact findIdx?_lt_length positioned

/-- **The structured skeleton Effect4 emits is `continue`-scoped.** Every
`continue l` in the skeleton of a structured lowering sits inside its
`while l`, and every `break l` names a block label of the flow's own graph.
No hypothesis is left over: `Flow.graphOf` is closed and `skeletonBlockWith`
introduces no label of its own. -/
theorem skeletonBody_wellScoped (table : List OpSpec) (blocks : List (RawBlock String))
    (entry : BlockId) {out : List Skeleton}
    (emitted : Flow.skeletonBody table blocks entry = some out) :
    Skel.wellScopedList (blockLabels (Flow.graphOf blocks entry)) [] out = true := by
  unfold Flow.skeletonBody at emitted
  refine emitWith_wellScoped (graphOf_closed blocks entry) ?_ emitted
  intro node transfer scopeBlocks scopeLoops own transferScoped lowered
  obtain ⟨block, _, lowered⟩ := Option.bind_eq_some_iff.mp lowered
  refine skeletonBlockWith_wellScoped table block _ scopeBlocks scopeLoops ?_ lowered
  intro target values control moved
  obtain ⟨position, _, moved⟩ := Option.bind_eq_some_iff.mp moved
  obtain ⟨transferred, transferredEq, moved⟩ := Option.bind_eq_some_iff.mp moved
  injection moved with moved
  subst moved
  rw [Skel.wellScopedList_append]
  exact Bool.and_eq_true_iff.mpr
    ⟨paramMove_wellScoped _ _ _ _ _, transferScoped position transferred transferredEq⟩

/-! ## Printing preserves scoping

`render` maps each labelled control shape to its spelling and introduces no
label of its own, so the property transports from the skeleton to the printed
program on the nose. -/

mutual

/-- Printing one skeleton node preserves label scoping. -/
theorem render_wellScoped (rows : ServiceRow) (blocks loops : List String) (node : Skeleton) :
    wellScopedList blocks loops (Skeleton.render rows node) =
      Skel.wellScoped blocks loops node := by
  match node with
  | .acquireService _ | .declare _ _ | .assign _ _ | .letTemp _ _ | .letBlockIndex _ _
  | .gotoBlock _ _ | .perform _ _ _ _ | .atom _ _ _ _ | .ret _
  | .acquire _ _ _ _ _ _ | .leave _ | .enterBlock _ =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        Lowering.serviceAcquire]
  | .literal _ _ _ value =>
      cases spelling : Flow.literal? value <;>
        simp [Skeleton.render, spelling, wellScopedList, wellScoped, Skel.wellScoped]
  | .dispatchLoop var cases =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        renderCases_wellScoped rows blocks loops cases]
  | .loop label body =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        renderList_wellScoped rows blocks (label :: loops) body]
  | .labelled label body =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        renderList_wellScoped rows (label :: blocks) loops body]
  | .breakTo label =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped]
  | .continueTo label =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped]
  | .decide answer site onTrue onFalse =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        renderList_wellScoped rows blocks loops onTrue,
        renderList_wellScoped rows blocks loops onFalse]
  | .enterScoped region body =>
      simp [Skeleton.render, wellScopedList, wellScoped, Skel.wellScoped,
        renderList_wellScoped rows [] [] body]
termination_by structural node

/-- Printing a skeleton list preserves label scoping. -/
theorem renderList_wellScoped (rows : ServiceRow) (blocks loops : List String)
    (nodes : List Skeleton) :
    wellScopedList blocks loops (Skeleton.renderList rows nodes) =
      Skel.wellScopedList blocks loops nodes := by
  match nodes with
  | [] => simp [Skeleton.renderList, wellScopedList, Skel.wellScopedList]
  | node :: rest =>
      rw [Skeleton.renderList, Skel.wellScopedList, wellScopedList_append,
        render_wellScoped rows blocks loops node, renderList_wellScoped rows blocks loops rest]
termination_by structural nodes

/-- Printing the arms of a dispatch switch preserves label scoping. -/
theorem renderCases_wellScoped (rows : ServiceRow) (blocks loops : List String)
    (cases : List (Nat × List Skeleton)) :
    wellScopedCases blocks loops (Skeleton.renderCases rows cases) =
      Skel.wellScopedCases blocks loops cases := by
  match cases with
  | [] => simp [Skeleton.renderCases, wellScopedCases, Skel.wellScopedCases]
  | (index, body) :: rest =>
      rw [Skeleton.renderCases, wellScopedCases, Skel.wellScopedCases,
        renderList_wellScoped rows blocks loops body,
        renderCases_wellScoped rows blocks loops rest]
termination_by structural cases

end

/-- **The structured TypeScript Effect4 prints is `continue`-scoped.** The
skeleton law, transported through `render`. -/
theorem structuredBody_wellScoped (rows : ServiceRow) (table : List OpSpec)
    (blocks : List (RawBlock String)) (entry : BlockId) {out : List Skeleton}
    (emitted : Flow.skeletonBody table blocks entry = some out) :
    wellScopedList (blockLabels (Flow.graphOf blocks entry)) [] (Skeleton.renderList rows out) =
      true := by
  rw [renderList_wellScoped]
  exact skeletonBody_wellScoped table blocks entry emitted

end Effect4.Target.Structured
