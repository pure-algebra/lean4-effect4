import Tools.Graph.Path
import ProofGraph.Axioms

open Tools.Graph
namespace CheckedPathControls

def ends : Nat → Nat × Nat
  | 0 => (0, 1)
  | 1 => (1, 0)
  | _ => (0, 1)

def cycle : Walk ends 0 0 :=
  .cons 0 (.cons 1 (.cons 0 (.cons 1 (.refl 0))))

def parallel : Walk ends 0 1 := .cons 2 (.refl 1)

example : Walk.read? ends 0 0 cycle.edges = some cycle := Walk.read?_edges cycle
example : (cycle.append parallel).edges = cycle.edges ++ parallel.edges :=
  Walk.edges_append cycle parallel
example (p : Walk ends 0 1) (h : Walk.read? ends 0 1 [2] = some p) : p.edges = [2] :=
  Walk.edges_of_read? [2] p h

#guard ((Walk.read? ends 7 7 []).map Walk.edges) = some []
#guard (Walk.read? ends 7 8 []).isNone
#guard ((Walk.read? ends 0 0 [0, 1, 0, 1]).map Walk.edges) = some [0, 1, 0, 1]
#guard ((Walk.read? ends 0 1 [2]).map Walk.edges) = some [2]
#guard (Walk.read? ends 0 1 [0, 0]).isNone
#guard (Walk.read? ends 1 1 [0]).isNone
#guard (Walk.read? ends 0 0 [0]).isNone
#guard (Walk.read? (fun _ : Nat => (1, 0)) 0 1 [2]).isNone

-- The same fold consumes paths as data and as a relational proof.
#guard cycle.fold (fun _ _ => Nat) (fun _ => 0) (fun _ _ count => count + 1) = 4

inductive Connect : Nat → Nat → Prop where
  | refl (a : Nat) : Connect a a
  | step (e : Nat) {b : Nat} : Connect (ends e).2 b → Connect (ends e).1 b

example {a b : Nat} (p : Walk ends a b) : Connect a b :=
  p.fold Connect Connect.refl (fun e _ tail => Connect.step e tail)

run_elab do
  let env ← Lean.getEnv
  let moduleNames := env.header.moduleNames
  let roots := env.constants.toList.filterMap fun (name, _) =>
    let owner := (env.getModuleIdxFor? name).bind fun index => moduleNames[index]?
    if owner == some `Tools.Graph.Path then some name else none
  let (answers, _) := ProofGraph.reachedAxiomsMany env roots.toArray {}
  for (name, answer) in roots.toArray.zip answers do
    let some axioms := answer | throwError "axiom walk exhausted for {name}"
    for axiomName in axioms do
      unless [``propext, ``Quot.sound].contains axiomName do
        throwError "{name} reaches forbidden axiom {axiomName}"
    Lean.logInfo m!"{name} exact axioms: {axioms}"
  Lean.logInfo m!"checked-path audit passed for {roots.length} declarations"
end CheckedPathControls
