import Reachability
import ProofGraph.Goal

/-! Research adapter for dependency-summary-exact.
The extractor reads real Lean declaration types and bodies through usedConstantsOf.
The existing collector supplies candidate membership. Independent distance propagation
supplies support witnesses. The generic checker certifies the captured graph.
Environment extraction remains a reflection boundary, not a proved compiler stage. -/
set_option autoImplicit false
namespace MathTransferProbe.ProofGraphProbe
open Lean Research.DependencySummary

structure RawRow where
  seeds : List Nat
  children : List Nat

structure Snapshot where
  names : Array Name
  labels : Array Name
  graph : Graph names.size labels.size

def checkedFin (n i : Nat) : Except String (Fin n) :=
  if h : i < n then .ok ⟨i, h⟩ else .error "out-of-range reference"

def capture (env : Environment) (roots : Array Name) (stop : Name → Bool)
    (budget : Nat) : Except String Snapshot := do
  let mut names : Array Name := #[]
  for root in roots do
    unless names.contains root do names := names.push root
  let mut labels : Array Name := #[]
  let mut rows : Array RawRow := #[]
  for _ in [0:budget] do
    if rows.size == names.size then break
    let name := names[rows.size]!
    let some info := env.find? name | throw s!"missing declaration {name}"
    let stopped := stop name
    let seeded := stopped || (match info with | .axiomInfo _ => true | _ => false)
    let mut seeds : List Nat := []
    if seeded then
      let label := (labels.toList.idxOf? name).getD labels.size
      unless labels.contains name do labels := labels.push name
      seeds := [label]
    let mut children : List Nat := []
    let used := if stopped then #[] else ProofGraph.usedConstantsOf info
    for child in used do
      let index := (names.toList.idxOf? child).getD names.size
      unless names.contains child do names := names.push child
      children := children ++ [index]
    rows := rows.push { seeds, children }
  unless rows.size == names.size do throw "capture budget exhausted"
  let typed ← rows.mapM fun row => do
    let seeds ← row.seeds.mapM (checkedFin labels.size)
    let children ← row.children.mapM (checkedFin names.size)
    pure ({ seeds, children } : Row names.size labels.size)
  if h : typed.size = names.size then
    pure { names, labels, graph := { rows := ⟨typed, h⟩ } }
  else throw "captured row count changed"

/-- Finite shortest-distance relaxation, independent of the production collector.
A reachable local label has a path with fewer than n edges after removing cycles. -/
def distances {n m : Nat} (g : Graph n m) : Certificate n m := Id.run do
  let mut table : Vector (Vector (Option Nat) m) n := Vector.ofFn fun u =>
    Vector.ofFn fun label => if label ∈ g.rows[u].seeds then some 0 else none
  for _ in [0:n] do
    table := Vector.ofFn fun u => Vector.ofFn fun label =>
      (g.rows[u].children).foldl (init := table[u][label]) fun best child =>
        match best, table[child][label] with
        | none, none => none
        | some old, none => some old
        | none, some d => some (d + 1)
        | some old, some d => some (min old (d + 1))
  return { rows := table }

/-- Preserve candidate membership from the existing collector. A missing witness receives
zero and must then fail the generic check unless it is a genuine local seed. -/
def candidates (env : Environment) (snap : Snapshot) (stop : Name → Bool) :
    Except String (Certificate snap.names.size snap.labels.size) := do
  let (outs, _) := ProofGraph.reachedAxiomsMany env snap.names {} stop
  unless outs.size == snap.names.size do throw "collector output count changed"
  for out in outs do
    let some labels := out | throw "collector budget exhausted"
    unless labels.all snap.labels.contains do throw "collector reported an unknown label"
  let support := distances snap.graph
  let table := Vector.ofFn fun u : Fin snap.names.size =>
    Vector.ofFn fun label : Fin snap.labels.size =>
      if ((outs[u.val]?.bind id).getD #[]).contains snap.labels[label.val] then
        some ((rank support u label).getD 0)
      else none
  return { rows := table }

/-- Checked analysis binds the captured table to the answers admitted for that table. -/
structure Analysis where
  snapshot : Snapshot
  certificate : Certificate snapshot.names.size snapshot.labels.size
  accepted : check snapshot.graph certificate = true

/-- Capture and query one environment under one stopping policy, then check the answers.
The snapshot extractor remains outside the universal graph theorem. -/
def analyze (env : Environment) (roots : Array Name) (stop : Name → Bool)
    (budget : Nat) : Except String Analysis := do
  let snapshot ← capture env roots stop budget
  let certificate ← candidates env snapshot stop
  if accepted : check snapshot.graph certificate = true then
    pure ⟨snapshot, certificate, accepted⟩
  else throw "collector answers disagree with captured dependencies"

/-- Follow a supplied descending witness to obtain one concrete dependency explanation. -/
def explain {n m : Nat} (g : Graph n m) (c : Certificate n m)
    (u : Fin n) (label : Fin m) : Nat → Option (List (Fin n))
  | 0 => none
  | fuel + 1 =>
    if label ∈ g.rows[u].seeds then some [u] else do
      let current ← rank c u label
      let child ← g.rows[u].children.find? fun child =>
        match rank c child label with | some d => d < current | none => false
      let rest ← explain g c child label fuel
      pure (u :: rest)

def gHasChild {n m : Nat} (g : Graph n m) (a b : Fin n) : Bool :=
  g.rows[a].children.contains b

def memoLeaf : Nat := 0
inductive MemoCycle where
  | quiet : MemoCycle
  | loud : Fin (memoLeaf + 1) → MemoCycle

def memoEntry : Type := MemoCycle

run_cmd do
  let env ← getEnv
  let stop := (· == ``memoLeaf)
  let .ok analysis := analyze env #[``memoEntry, ``MemoCycle.quiet] stop 10000
    | throwError "checked dependency analysis failed"
  let snap := analysis.snapshot
  let cert := analysis.certificate
  let some qi := snap.names.toList.idxOf? ``MemoCycle.quiet
    | throwError "quiet not captured"
  let some li := snap.labels.toList.idxOf? ``memoLeaf
    | throwError "stop leaf not captured"
  let .ok u := checkedFin snap.names.size qi | throwError "quiet index invalid"
  let .ok label := checkedFin snap.labels.size li | throwError "leaf index invalid"
  let some path := explain snap.graph cert u label (snap.names.size + 1)
    | throwError "no dependency explanation"
  unless path.head? == some u && path.getLast? ==
      (snap.names.toList.idxOf? ``memoLeaf).bind (fun i => (checkedFin snap.names.size i).toOption) do
    throwError "explanation endpoints changed"
  unless (path.zip path.tail).all (fun (a, b) => gHasChild snap.graph a b) do
    throwError "explanation contains a non-edge"
  let poison : Certificate snap.names.size snap.labels.size :=
    { rows := Vector.ofFn fun v => Vector.ofFn fun l =>
        if v == u && l == label then none else rank cert v l }
  if check snap.graph poison then throwError "omitted cyclic answer accepted"
  logInfo m!"collector graph: {snap.names.size} nodes, {snap.labels.size} labels; accepted; poisoned omission refused"
  logInfo m!"dependency explanation: {path.map (fun i => snap.names[i.val])}"
  -- Capture refusal is distinct from a graph with no dependencies.
  unless (capture env #[``memoEntry] stop 0).toOption.isNone do
    throwError "budget exhaustion accepted as empty graph"
  unless (capture env #[`ThisDeclarationDoesNotExist] stop 100).toOption.isNone do
    throwError "missing declaration accepted as empty graph"

end MathTransferProbe.ProofGraphProbe
