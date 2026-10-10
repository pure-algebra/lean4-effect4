import Reachability
import Tools.View.FlowLaws

/-!
Research connector for proposed tool claim `view-reachability-summary-exact`.
Placement and consumers precede this file in `OPERATIONAL-PLAN.md`.
The snapshot retains directed reachability at bounded item positions.
It uses the existing `Tools.View.Flow.Reach`, including its reflexive case.
It establishes no scheduler, source admission, layout identity or performance property.
-/

namespace Research.FlowReachability

open Research.DependencySummary
abbrev Edge := Tools.View.Flow.Edge

/-- Every existing edge has both endpoints inside the finite position table. -/
def ValidEndpoints (n : Nat) (es : List Edge) : Prop :=
  ∀ e ∈ es, e.fr < n ∧ e.to < n

/-- Check every edge occurrence, including edges from an invalid source. -/
def endpointsCheck (n : Nat) (es : List Edge) : Bool :=
  es.all fun e => decide (e.fr < n ∧ e.to < n)

/-- An outgoing target at a bounded source, retaining the edge's direction. -/
def childOf (n : Nat) (source : Fin n) (e : Edge) : Option (Fin n) :=
  if e.fr = source.val then
    if targetBound : e.to < n then some ⟨e.to, targetBound⟩ else none
  else none

/-- The ordered child occurrences of one position. -/
def children (n : Nat) (es : List Edge) (source : Fin n) : List (Fin n) :=
  es.filterMap (childOf n source)

/-- Derived analysis data; each position seeds its own label. -/
def snapshot (n : Nat) (es : List Edge) : DependencySummary.Graph n n :=
  { rows := ⟨(List.ofFn fun source =>
      { seeds := [source], children := children n es source }).toArray,
      by rw [List.size_toArray, List.length_ofFn]⟩ }

/-- The public adapter refuses an invalid endpoint instead of silently dropping its edge. -/
def ofEdges? (n : Nat) (es : List Edge) : Option (DependencySummary.Graph n n) :=
  if endpointsCheck n es then some (snapshot n es) else none

/-- The operational check requires the endpoint check as well as the summary certificate. -/
def checkFlow (n : Nat) (es : List Edge) (c : Certificate n n) : Bool :=
  endpointsCheck n es && check (snapshot n es) c

/-- Adapter helper for `certificate_flow_exact`: the endpoint check establishes its premise. -/
theorem endpoints_checked {n : Nat} {es : List Edge} (h : endpointsCheck n es = true) :
    ValidEndpoints n es := by
  intro e member
  exact of_decide_eq_true ((List.all_eq_true.mp h) e member)

/-- Adapter helper for `reaches_iff_flow`: child occurrences are precisely the directed edges.
The bounded target makes this equality valid even before checking all source endpoints. -/
theorem children_exact (n : Nat) (es : List Edge) (source target : Fin n) :
    target ∈ children n es source ↔
      ∃ e ∈ es, e.fr = source.val ∧ e.to = target.val := by
  constructor
  · intro member
    obtain ⟨e, inEdges, selected⟩ := List.mem_filterMap.mp member
    by_cases originEq : e.fr = source.val
    · by_cases bound : e.to < n
      · have same : (⟨e.to, bound⟩ : Fin n) = target := by
          apply Option.some.inj
          simpa only [childOf, if_pos originEq, dif_pos bound] using selected
        exact ⟨e, inEdges, originEq, congrArg Fin.val same⟩
      · simp only [childOf, if_pos originEq, dif_neg bound] at selected
        cases selected
    · simp only [childOf, if_neg originEq] at selected
      cases selected
  · rintro ⟨e, inEdges, originEq, to⟩
    apply List.mem_filterMap.mpr
    refine ⟨e, inEdges, ?_⟩
    have bound : e.to < n := to ▸ target.isLt
    simp only [childOf, if_pos originEq, dif_pos bound]
    exact congrArg some (Fin.ext to)

/-- Adapter helper for `reaches_iff_flow`: snapshot paths are existing flow paths. -/
theorem snapshot_to_flow {n : Nat} {es : List Edge} {source target : Fin n}
    (path : Reaches (snapshot n es) source target) :
    Tools.View.Flow.Reach es source.val target.val := by
  induction path with
  | @seed source target seed =>
    have same : target = source := by
      simpa only [snapshot, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn, List.mem_singleton] using seed
    subst target
    exact .refl _
  | @step source child target edge _ ih =>
    have member : child ∈ children n es source := by
      simpa only [snapshot, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn] using edge
    obtain ⟨e, inEdges, originEq, to⟩ := (children_exact n es source child).mp member
    rw [← originEq]
    apply Tools.View.Flow.Reach.step e inEdges
    rw [to]
    exact ih

/-- Adapter helper for `reaches_iff_flow`: bounded flow paths are snapshot paths.
Valid endpoints include every intermediate position, not just the selected query endpoints. -/
theorem flow_to_snapshot {n : Nat} {es : List Edge} (valid : ValidEndpoints n es)
    {source target : Nat} (path : Tools.View.Flow.Reach es source target) :
    ∀ sourceBound : source < n, ∀ targetBound : target < n,
      Reaches (snapshot n es) ⟨source, sourceBound⟩ ⟨target, targetBound⟩ := by
  induction path with
  | refl source =>
    intro sourceBound targetBound
    apply Reaches.seed
    simp only [snapshot, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn, List.mem_singleton]
  | step e inEdges _ ih =>
    intro sourceBound targetBound
    have bounds := valid e inEdges
    apply Reaches.step (child := ⟨e.to, bounds.2⟩)
    · have member := (children_exact n es ⟨e.fr, sourceBound⟩ ⟨e.to, bounds.2⟩).mpr
        ⟨e, inEdges, rfl, rfl⟩
      simpa only [snapshot, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_ofFn] using member
    · exact ih bounds.2 targetBound

/-- Exact adapter relation for the directed path observation; no new path relation is introduced. -/
theorem reaches_iff_flow {n : Nat} {es : List Edge} (valid : ValidEndpoints n es)
    (source target : Fin n) :
    Reaches (snapshot n es) source target ↔ Tools.View.Flow.Reach es source.val target.val :=
  ⟨snapshot_to_flow, fun path => flow_to_snapshot valid path source.isLt target.isLt⟩

/-- Proposed tool claim `view-reachability-summary-exact`, concept `initial-algebras-folds`.
Consumers: directed application graph queries, explanations and impact reports.
Accepted summaries agree with existing `Flow.Reach` at every bounded pair of endpoints.
The explicit endpoint premise excludes lost edges through positions outside the snapshot. -/
theorem certificate_flow_exact {n : Nat} {es : List Edge} {c : Certificate n n}
    (valid : ValidEndpoints n es) (accepted : check (snapshot n es) c = true)
    (source target : Fin n) :
    Present c source target ↔ Tools.View.Flow.Reach es source.val target.val :=
  (check_summary_exact accepted source target).trans (reaches_iff_flow valid source target)

/-- Operational consumer: a successful combined check supplies every connector premise. -/
theorem checkFlow_exact {n : Nat} {es : List Edge} {c : Certificate n n}
    (accepted : checkFlow n es c = true) (source target : Fin n) :
    Present c source target ↔ Tools.View.Flow.Reach es source.val target.val := by
  have checks := Bool.and_eq_true_iff.mp accepted
  exact certificate_flow_exact (endpoints_checked checks.1) checks.2 source target

def connectorProof : ProofGraph.ProofRef := checked_theorem% certificate_flow_exact
def checkedConnectorProof : ProofGraph.ProofRef := checked_theorem% checkFlow_exact

namespace Controls

def directed : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 2 }]
def directedAnswers : Certificate 3 3 :=
  { rows := ⟨#[⟨#[some 0, some 1, some 2], rfl⟩,
               ⟨#[none, some 0, some 1], rfl⟩,
               ⟨#[none, none, some 0], rfl⟩], rfl⟩ }

example : checkFlow 3 directed directedAnswers = true := by decide
example : Tools.View.Flow.Reach directed 0 2 :=
  (checkFlow_exact (by decide : checkFlow 3 directed directedAnswers = true) 0 2).mp (by decide)
example : ¬ Tools.View.Flow.Reach directed 2 0 := by
  intro reversed
  have present := (checkFlow_exact
    (by decide : checkFlow 3 directed directedAnswers = true) 2 0).mpr reversed
  exact (by decide : ¬ Present directedAnswers 2 0) present

def reversedAnswer : Certificate 3 3 :=
  { rows := ⟨#[⟨#[some 0, some 1, some 2], rfl⟩,
               ⟨#[none, some 0, some 1], rfl⟩,
               ⟨#[some 1, none, some 0], rfl⟩], rfl⟩ }
example : checkFlow 3 directed reversedAnswer = false := by decide

def cycle : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 0 }]
def cycleAnswers : Certificate 2 2 :=
  { rows := ⟨#[⟨#[some 0, some 1], rfl⟩, ⟨#[some 1, some 0], rfl⟩], rfl⟩ }
example : checkFlow 2 cycle cycleAnswers = true := by decide
example : Tools.View.Flow.Reach cycle 1 0 :=
  (checkFlow_exact (by decide : checkFlow 2 cycle cycleAnswers = true) 1 0).mp (by decide)

def badTarget : List Edge := [{ fr := 0, to := 2 }]
def badSource : List Edge := [{ fr := 2, to := 0 }]
example : ofEdges? 2 badTarget = none := by decide
example : ofEdges? 2 badSource = none := by decide
example : checkFlow 2 badTarget cycleAnswers = false := by decide
example : checkFlow 2 badSource cycleAnswers = false := by decide

/-- Removing an out-of-bounds intermediate would destroy a real bounded-endpoint path. -/
def missingIntermediate : List Edge := [{ fr := 0, to := 2 }, { fr := 2, to := 1 }]
def identities : Certificate 2 2 :=
  { rows := ⟨#[⟨#[some 0, none], rfl⟩, ⟨#[none, some 0], rfl⟩], rfl⟩ }

-- The raw bounded snapshot loses both offending edges and accepts only identities.
example : check (snapshot 2 missingIntermediate) identities = true := by decide
example : ¬ Present identities 0 1 := by decide
-- The original relation still has the directed path through position 2.
example : Tools.View.Flow.Reach missingIntermediate 0 1 :=
  .step { fr := 0, to := 2 } List.mem_cons_self
    (.step { fr := 2, to := 1 } (List.mem_cons_of_mem _ List.mem_cons_self) (.refl 1))
-- The operational adapter and combined checker refuse that incomplete position table.
example : ofEdges? 2 missingIntermediate = none := by decide
example : checkFlow 2 missingIntermediate identities = false := by decide

end Controls

run_cmd Lean.Elab.Command.liftTermElabM do
  for name in #[``endpoints_checked, ``children_exact, ``snapshot_to_flow,
      ``flow_to_snapshot, ``reaches_iff_flow, ``certificate_flow_exact, ``checkFlow_exact] do
    let some axioms := ProofGraph.exactAxioms (← Lean.getEnv) name
      | Lean.throwError "application reachability audit exhausted its budget"
    Lean.logInfo m!"{name}: exact axioms {axioms}"

end Research.FlowReachability
