import Baseline
import Tools.View.FlowPath
import ProofGraph.Proof

/-! Positive and negative readers at actual Flow edge occurrences.
The bounded query retains its old policy; a successful answer carries a path. -/
set_option autoImplicit false
namespace GraphToolsProbe.FlowPaths
open Tools.View.Flow Tools.Graph

def cycleEdges : List Edge :=
  [{ fr := 0, to := 1 }, { fr := 1, to := 2 }, { fr := 2, to := 0 }, { fr := 0, to := 1 }]

/-- The shared frontier helper retains the independent old query at every fuel. -/
theorem reaches_old (es : List Edge) (fuel : Nat) (frontier seen : List Nat) (target : Nat) :
    reaches es fuel frontier seen target = Baseline.reaches es fuel frontier seen target := by
  induction fuel generalizing frontier seen with
  | zero => rfl
  | succ fuel ih =>
    simp only [reaches, Baseline.reaches, searchNext, ih]

-- Exact edge positions distinguish the two parallel edges, even with equal endpoints.
#guard ((Walk.read? (occurrenceEndpoints cycleEdges) 0 2 [⟨0, by decide⟩, ⟨1, by decide⟩]).map Walk.edges).map
  (List.map Fin.val) == some [0, 1]
#guard ((Walk.read? (occurrenceEndpoints cycleEdges) 0 2 [⟨3, by decide⟩, ⟨1, by decide⟩]).map Walk.edges).map
  (List.map Fin.val) == some [3, 1]
#guard (Walk.read? (occurrenceEndpoints cycleEdges) 0 2 [⟨0, by decide⟩, ⟨2, by decide⟩]).isNone
#guard ((explainWait 3 cycleEdges (2, 0)).map Walk.edges).map (List.map Fin.val) == some [0, 1]
#guard ((explainWait 1 [] (0, 0)).map Walk.edges).map (List.map Fin.val) == some []
#guard (explainReaches cycleEdges 0 0 0).isNone
#guard (explainReaches cycleEdges 1 0 2).isNone
#guard (explainReaches cycleEdges 2 0 2).isNone
#guard (explainReaches cycleEdges 3 0 2).isSome

-- Changing the middle edge invalidates that occurrence sequence.
def changed : List Edge :=
  [{ fr := 0, to := 1 }, { fr := 4, to := 2 }, { fr := 2, to := 0 }, { fr := 0, to := 1 }]
#guard (Walk.read? (occurrenceEndpoints changed) 0 2 [⟨0, by decide⟩, ⟨1, by decide⟩]).isNone

-- Weak connectedness does not imply the directed query succeeds.
def joined : List Edge := [{ fr := 0, to := 2 }, { fr := 1, to := 2 }]
#guard (explainReaches joined 8 0 1).isNone
#guard (explainReaches joined 8 0 2).isSome

-- A different edge alphabet explicitly forgets direction for a connectedness witness.
def weakEnds (e : Fin joined.length ⊕ Fin joined.length) : Nat × Nat :=
  match e with
  | .inl i => occurrenceEndpoints joined i
  | .inr i => ((occurrenceEndpoints joined i).2, (occurrenceEndpoints joined i).1)
#guard (Walk.read? weakEnds 0 1 [.inl ⟨0, by decide⟩, .inr ⟨1, by decide⟩]).isSome

-- No item-count premise is silently added: the raw search can traverse position 20.
def far : List Edge := [{ fr := 0, to := 20 }, { fr := 20, to := 1 }]
#guard ((explainWait 2 far (1, 0)).map Walk.edges).map (List.map Fin.val) == some [0, 1]

/-- A real cycle query consumes the new positive-path connector. -/
example : Reach cycleEdges 0 2 := by
  let first := Walk.edge (occurrenceEndpoints cycleEdges) ⟨0, by decide⟩
  let second := Walk.edge (occurrenceEndpoints cycleEdges) ⟨1, by decide⟩
  let path : Walk (occurrenceEndpoints cycleEdges) 0 2 := first.append second
  exact occurrenceWalk_reach cycleEdges path

example : Reach cycleEdges 0 2 :=
  reaches_reach cycleEdges 3 0 2 (by decide)

run_elab do
  let env ← Lean.getEnv
  let names := env.header.moduleNames
  let roots := env.constants.toList.filterMap fun (name, _) =>
    let owner := (env.getModuleIdxFor? name).bind fun index => names[index]?
    if owner == some `Tools.View.FlowPath then some name else none
  let (answers, _) := ProofGraph.reachedAxiomsMany env roots.toArray {}
  for (name, answer) in roots.toArray.zip answers do
    let some axioms := answer | throwError "exact dependency traversal exhausted for {name}"
    for axiomName in axioms do
      unless [``propext, ``Quot.sound].contains axiomName do
        throwError "{name} reaches forbidden axiom {axiomName}"
    Lean.logInfo m!"{name}: exact axioms {axioms}"
  Lean.logInfo m!"PASS: Flow paths, controls, and exact dependencies for {roots.length} declarations"
end GraphToolsProbe.FlowPaths
