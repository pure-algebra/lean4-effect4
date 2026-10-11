import Tools.Graph.Summary
import Tools.View.FlowLaws

/-!
# Directed reachability of a flow, checked

A flow's edges name their ends by item positions (`Edge`, `tools/Tools/View/Flow.lean`), and
`Reach` is the directed path relation over them (`tools/Tools/View/FlowLaws.lean`). This module
connects `Reach` to the checked summaries of `Tools.Graph.Summary`
(`tools/Tools/Graph/Summary.lean`). The reach graph (`reachGraph`) has one node for each position
below a bound `n`. Each node seeds its own position as its label, and its children are the targets
of its outgoing edges, in order. So an accepted table reports a label at a node if and only if
`Reach` leads from the node to that position (`summary_flow_exact`).

The bound is a premise. An edge with an end at or above it would leave the reach graph, and a
path through that end would be lost: the battery's control `missingIntermediate`
(`Test/Audit/SummaryControls.lean`) shows one. So `checkReach` and `ReachTable.build?` refuse
such an edge, never drop it. `ReachTable` is the query interface: build once, then ask directed
queries, each answer proved equal to `Reach` (`ReachTable.reaches_iff`).

Placement: concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7), as a tool law. The
claim is `view-reachability-summary-exact`, with pointer `checkReach_exact`. Its consumers are
directed queries of the application graph, explanations and impact reports.

What it does not establish:

- when a fiber runs: `Reach` reads the flow's structure, not a schedule;
- the admission of a program source, a layout identity, a forest or a speed bound;
- weak connectedness: it keeps the edges' direction.
-/

namespace Tools.View.Flow

open Tools.Graph

/-- Every edge has both ends below the position bound. -/
def ValidEndpoints (n : Nat) (es : List Edge) : Prop :=
  ∀ e ∈ es, e.fr < n ∧ e.to < n

/-- The test of `ValidEndpoints`: it reads every edge, an edge from an end above the bound
included. -/
def endpointsCheck (n : Nat) (es : List Edge) : Bool :=
  es.all fun e => decide (e.fr < n ∧ e.to < n)

/-- The edge's target, when the edge leaves the source and its target is below the bound. -/
def childOf (n : Nat) (source : Fin n) (e : Edge) : Option (Fin n) :=
  if e.fr = source.val then
    if bound : e.to < n then some ⟨e.to, bound⟩ else none
  else none

/-- The targets of a position's outgoing edges, in the edges' order, repeated edges kept. -/
def outgoing (n : Nat) (es : List Edge) (source : Fin n) : List (Fin n) :=
  es.filterMap (childOf n source)

/-- The reach graph: each position seeds its own label, and its children are its outgoing
edges' targets. -/
def reachGraph (n : Nat) (es : List Edge) : Summary.Graph n n :=
  Summary.Graph.ofFn (fun u => [u]) (outgoing n es)

/-- A step of `view-reachability-summary-exact`. Its consumer is `reachGraph_to_flow`. -/
theorem reachGraph_seeds (n : Nat) (es : List Edge) (u : Fin n) :
    (reachGraph n es).seeds[u] = [u] :=
  Summary.Graph.ofFn_seeds _ _ u

/-- A step of `view-reachability-summary-exact`. Its consumer is `reachGraph_to_flow`. -/
theorem reachGraph_children (n : Nat) (es : List Edge) (u : Fin n) :
    (reachGraph n es).children[u] = outgoing n es u :=
  Summary.Graph.ofFn_children _ _ u

/-- The endpoint test establishes its proposition. A step of `view-reachability-summary-exact`.
Its consumer is `checkReach_exact`. -/
theorem endpoints_checked {n : Nat} {es : List Edge} (h : endpointsCheck n es = true) :
    ValidEndpoints n es := by
  intro e member
  exact of_decide_eq_true ((List.all_eq_true.mp h) e member)

/-- A position's children are exactly the targets of its edges in the list. The target's own
bound makes this hold before the endpoint test. A step of `view-reachability-summary-exact`. Its
consumers are `reachGraph_to_flow` and `flow_to_reachGraph`. -/
theorem outgoing_exact (n : Nat) (es : List Edge) (source target : Fin n) :
    target ∈ outgoing n es source ↔ ∃ e ∈ es, e.fr = source.val ∧ e.to = target.val := by
  constructor
  · intro member
    obtain ⟨e, inEdges, selected⟩ := List.mem_filterMap.mp member
    unfold childOf at selected
    split at selected
    next leaves =>
      split at selected
      next bound =>
        have same : (⟨e.to, bound⟩ : Fin n) = target := Option.some.inj selected
        exact ⟨e, inEdges, leaves, congrArg Fin.val same⟩
      next => cases selected
    next => cases selected
  · rintro ⟨e, inEdges, leaves, arrives⟩
    apply List.mem_filterMap.mpr
    refine ⟨e, inEdges, ?_⟩
    have bound : e.to < n := arrives ▸ target.isLt
    simp only [childOf, if_pos leaves, dif_pos bound]
    exact congrArg some (Fin.ext arrives)

/-- A path of the reach graph is a `Reach` path of the flow. A step of
`view-reachability-summary-exact`. Its consumer is `reaches_iff_flow`. -/
theorem reachGraph_to_flow {n : Nat} {es : List Edge} {source target : Fin n}
    (path : Summary.Reaches (reachGraph n es) source target) : Reach es source.val target.val := by
  induction path with
  | @seed u l seeded =>
    rw [reachGraph_seeds, List.mem_singleton] at seeded
    rw [seeded]
    exact .refl _
  | @step u v l edge _ ih =>
    rw [reachGraph_children] at edge
    obtain ⟨e, inEdges, leaves, arrives⟩ := (outgoing_exact n es u v).mp edge
    rw [← leaves]
    apply Reach.step e inEdges
    rw [arrives]
    exact ih

/-- A `Reach` path between two positions below the bound is a path of the reach graph. The
premise bounds every edge, so every position on the path, not only its two ends. A step of
`view-reachability-summary-exact`. Its consumer is `reaches_iff_flow`. -/
theorem flow_to_reachGraph {n : Nat} {es : List Edge} (valid : ValidEndpoints n es)
    {source target : Nat} (path : Reach es source target) :
    ∀ sourceBound : source < n, ∀ targetBound : target < n,
      Summary.Reaches (reachGraph n es) ⟨source, sourceBound⟩ ⟨target, targetBound⟩ := by
  induction path with
  | refl source =>
    intro sourceBound targetBound
    apply Summary.Reaches.seed
    rw [reachGraph_seeds]
    exact List.mem_singleton_self _
  | step e inEdges _ ih =>
    intro sourceBound targetBound
    have bounds := valid e inEdges
    apply Summary.Reaches.step (v := ⟨e.to, bounds.2⟩)
    · rw [reachGraph_children]
      exact (outgoing_exact n es ⟨e.fr, sourceBound⟩ ⟨e.to, bounds.2⟩).mpr ⟨e, inEdges, rfl, rfl⟩
    · exact ih bounds.2 targetBound

/-- The reach graph's paths are the flow's `Reach` paths, at every two positions below the bound.
A step of `view-reachability-summary-exact`. Its consumer is `summary_flow_exact`. -/
theorem reaches_iff_flow {n : Nat} {es : List Edge} (valid : ValidEndpoints n es)
    (source target : Fin n) :
    Summary.Reaches (reachGraph n es) source target ↔ Reach es source.val target.val :=
  ⟨reachGraph_to_flow, fun path => flow_to_reachGraph valid path source.isLt target.isLt⟩

/-- An accepted distance table of the reach graph reports a target at a source if and only if
`Reach` leads from the source to the target, when every edge lies below the bound. A step of
`view-reachability-summary-exact`. Its consumers are `checkReach_exact` and
`ReachTable.reaches_iff`. -/
theorem summary_flow_exact {n : Nat} {es : List Edge} {d : Summary.Distances n n}
    (valid : ValidEndpoints n es) (accepted : Summary.check (reachGraph n es) d = true)
    (source target : Fin n) :
    Summary.Present d source target ↔ Reach es source.val target.val :=
  (Summary.check_summary_exact accepted source target).trans (reaches_iff_flow valid source target)

/-- Accept a distance table for a flow: every edge lies below the bound, and `check` accepts the
table on the reach graph. -/
def checkReach (n : Nat) (es : List Edge) (d : Summary.Distances n n) : Bool :=
  endpointsCheck n es && Summary.check (reachGraph n es) d

/-- **A checked flow summary**: when `checkReach` accepts a distance table, the table reports a
target at a source if and only if `Reach` leads from the source to the target. The pointer of
the claim `view-reachability-summary-exact`. Its consumers are directed queries of the
application graph, explanations and impact reports. It establishes no schedule. -/
theorem checkReach_exact {n : Nat} {es : List Edge} {d : Summary.Distances n n}
    (accepted : checkReach n es d = true) (source target : Fin n) :
    Summary.Present d source target ↔ Reach es source.val target.val := by
  have checks := Bool.and_eq_true_iff.mp accepted
  exact summary_flow_exact (endpoints_checked checks.1) checks.2 source target

/-- A flow's directed reachability below a bound, built once and checked. -/
structure ReachTable (n : Nat) (es : List Edge) where
  valid : endpointsCheck n es = true
  summary : Summary.Checked (reachGraph n es)

/-- Build the reach table of a flow. An edge with an end at or above the bound refuses the table,
and so does a summary that `check` refuses; neither gives an empty table. -/
def ReachTable.build? (n : Nat) (es : List Edge) : Option (ReachTable n es) :=
  if valid : endpointsCheck n es = true then
    (Summary.summarize (reachGraph n es)).map fun summary => ⟨valid, summary⟩
  else none

/-- Whether the table reports that `Reach` leads from `source` to `target`. -/
def ReachTable.reaches {n : Nat} {es : List Edge} (t : ReachTable n es)
    (source target : Fin n) : Bool :=
  t.summary.reports source target

/-- Each answer of a reach table is `Reach`. A consumer of `summary_flow_exact`, for a caller that
builds the table once and asks many directed queries. -/
theorem ReachTable.reaches_iff {n : Nat} {es : List Edge} (t : ReachTable n es)
    (source target : Fin n) :
    t.reaches source target = true ↔ Reach es source.val target.val :=
  summary_flow_exact (endpoints_checked t.valid) t.summary.accepted source target

end Tools.View.Flow
