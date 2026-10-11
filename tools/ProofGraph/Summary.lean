import ProofGraph.Axioms
import Tools.Graph.Summary

/-!
# The axiom walk's answers, checked against a captured graph

`reachedAxioms` (`tools/ProofGraph/Axioms.lean`) answers, for each constant, the axioms and the
stopped constants that it reaches. Its memo and its cycle handling are untrusted code: a member
of a cycle stored short once (the section Cycles of that module). This module checks the answers
against the graph that the walk reads, by the summary law of `Tools.Graph.Summary`
(`tools/Tools/Graph/Summary.lean`):

1. `captureDependencies` reads the graph from the roots under the walk's own policy. A node is a
   constant, and its children are the constants its content names (`usedConstantsOf`). A stopped
   constant is a leaf with its own label. An axiom has its own label, and its type is read.
2. `collectorTable` asks `reachedAxiomsMany` for every captured constant. Each answer becomes a
   table entry, with a distance from a separate breadth-first search (`Summary.distances`).
3. `checkDependencies` runs `Summary.check` on that table. When it accepts,
   `Summary.Checked.reports_iff` says: the walk reports a label at a captured constant if and
   only if a path of the captured graph leads from the constant to that label.

`#axiom_audit checked M …` runs the three steps over the declarations that it walks
(`tools/ProofGraph/AxiomAudit.lean`).

Placement: concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7), the claim
`dependency-summary-exact`: this module is its consumer at the axiom walk. It serves the
evidence of R4, R10 and R14 reports, and proves none of those requirements.

What it does not establish:

- that the captured graph holds every dependency: the capture reads `usedConstantsOf`, the walk's
  own relation, from this environment, which is a reflection boundary;
- a body that the environment withholds: a missing constant refuses the capture, and it is
  never read as a constant with no dependency;
- a statement about any theorem that a node names;
- a change of the stopping policy or of the planned goals: that is another graph.

A capture that runs out of its budget refuses, so an exhausted capture never reads as an empty
graph. These definitions read `Lean.Environment`, so they reach `Classical.choice` as the walk
does; the law they apply rests on `propext` and `Quot.sound`.
-/

namespace ProofGraph
open Lean
open Tools.Graph

/-- A captured dependency graph: the constants, the labels (the axioms and the stopped
constants met), and the graph over their positions. -/
structure DependencySnapshot where
  names : Array Name
  labels : Array Name
  graph : Summary.Graph names.size labels.size

/-- One captured constant before its positions are typed. -/
structure RawDependency where
  seeds : List Nat
  children : List Nat

/-- A position below `size`, or a refusal that names it. -/
def positionBelow (size i : Nat) : Except String (Fin size) :=
  if h : i < size then .ok ⟨i, h⟩ else .error s!"position {i} is not below {size}"

/-- Capture the graph that the walk reads from `roots` under `stop`, one constant a step, at most
`budget` steps. A constant that is not stopped and has no declaration refuses the capture. -/
def captureDependencies (env : Environment) (roots : Array Name) (stop : Name → Bool)
    (budget : Nat := axiomBudget) : Except String DependencySnapshot := do
  let mut names : Array Name := #[]
  let mut index : Std.HashMap Name Nat := {}
  for root in roots do
    unless index.contains root do
      index := index.insert root names.size
      names := names.push root
  let mut labels : Array Name := #[]
  let mut labelIndex : Std.HashMap Name Nat := {}
  let mut raw : Array RawDependency := #[]
  for _ in [0:budget] do
    let some name := names[raw.size]? | break
    let stopped := stop name
    let info := env.find? name
    if !stopped && info.isNone then throw s!"{name} has no declaration in this environment"
    let labelled := stopped || (match info with | some (.axiomInfo _) => true | _ => false)
    let mut seeds : List Nat := []
    if labelled then
      match labelIndex[name]? with
      | some l => seeds := [l]
      | none =>
        labelIndex := labelIndex.insert name labels.size
        seeds := [labels.size]
        labels := labels.push name
    let used := match stopped, info with
      | false, some ci => usedConstantsOf ci
      | _, _ => #[]
    let mut children : Array Nat := #[]
    for child in used do
      match index[child]? with
      | some i => children := children.push i
      | none =>
        index := index.insert child names.size
        children := children.push names.size
        names := names.push child
    raw := raw.push { seeds, children := children.toList }
  unless raw.size == names.size do throw "the capture ran out of its budget"
  let typed ← raw.mapM fun node => do
    let seeds ← node.seeds.mapM (positionBelow labels.size)
    let children ← node.children.mapM (positionBelow names.size)
    pure (seeds, children)
  if h : typed.size = names.size then
    return { names, labels,
             graph := { seeds := ⟨typed.map (·.1), by rw [Array.size_map, h]⟩,
                        children := ⟨typed.map (·.2), by rw [Array.size_map, h]⟩ } }
  else throw "the captured constant count changed"

/-- The walk's answers at every captured constant as a distance table. An entry stands wherever
`reachedAxiomsMany` answers the label. Its distance comes from `Summary.distances`, and zero
stands where that search has none, which `Summary.check` then refuses unless the label is the
constant's own. -/
def collectorTable (env : Environment) (snapshot : DependencySnapshot) (stop : Name → Bool) :
    Except String (Summary.Distances snapshot.names.size snapshot.labels.size) := do
  let (answers, _) := reachedAxiomsMany env snapshot.names {} stop
  unless answers.size == snapshot.names.size do throw "the walk answered another count"
  let mut sets : Array (Std.HashSet Name) := #[]
  for answer in answers do
    let some reached := answer | throw "the walk ran out of its step budget"
    unless reached.all snapshot.labels.contains do
      throw "the walk reported a label outside the captured graph"
    sets := sets.push (Std.HashSet.ofArray reached)
  let support := Summary.distances snapshot.graph
  return Vector.ofFn fun u => Vector.ofFn fun l =>
    if (sets[u.val]?.map (·.contains snapshot.labels[l])).getD false then
      some ((Summary.distance support u l).getD 0)
    else none

/-- The walk's answers over a captured graph, accepted by `Summary.check`. -/
structure CheckedDependencies where
  snapshot : DependencySnapshot
  summary : Summary.Checked snapshot.graph

/-- Capture the graph from `roots`, read the walk's answers, and check them. -/
def checkDependencies (env : Environment) (roots : Array Name) (stop : Name → Bool)
    (budget : Nat := axiomBudget) : Except String CheckedDependencies := do
  let snapshot ← captureDependencies env roots stop budget
  let table ← collectorTable env snapshot stop
  match Summary.admit snapshot.graph table with
  | some summary => return { snapshot, summary }
  | none => throw "the walk's answers disagree with the captured graph"

/-- The labels that the checked summary reports at a captured constant, in label order. -/
def CheckedDependencies.reported (c : CheckedDependencies) (u : Fin c.snapshot.names.size) :
    Array Name :=
  (List.finRange c.snapshot.labels.size).foldl (init := #[]) fun acc l =>
    if c.summary.reports u l then acc.push c.snapshot.labels[l] else acc

end ProofGraph
