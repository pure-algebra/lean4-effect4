import Lean
import ProofGraph.Population
import ProofGraph.Goal
import ProofGraph.Registry

/-!
# Tools.LoadPaths — which theorems carry load, and how much a landing reuses

The proof graph's theorems are its members, and a member's direct dependencies are the authored
theorems its proof names (walking through the auxiliaries that the elaborator generates,
`ProofGraph.isAuxiliary`). The **roots** are the registry's claim pointers and the requirements'
top nodes (`ProofGraph.Registry`). A theorem is **load-bearing** when a root reaches it along
direct dependencies. A theorem that no theorem of the loaded tree names, and that is no root, is
**unconsumed**.

For a **landing**, the theorems of a set of modules, the report counts the landing's dependency
edges by where they end:

| Edge ends at | Means |
| --- | --- |
| local | a theorem of the landing itself: a helper it wrote |
| tree | a theorem of the tree outside the landing: a law it reused |
| core | a theorem of Lean's own library |
| instance | an instance that type-class resolution chose: plumbing, not a law |

The **reuse ratio** is tree edges over tree and local edges. The **joints** of a landing are the
tree theorems it names most.

The measures follow the structural reading of formal libraries: dependency graphs from proof terms
(Blanchette, Haslbeck, Matichuk and Nipkow, *Mining the Archive of Formal Proofs*, CICM 2015;
Li, Peng, Severini and Shafto, *The Network Structure of Mathlib*, arXiv 2604.24797), and
fully stressed, least-weight frames (Michell 1904). The research note is
`docs/research/2026-10-08-load-paths.md`.

**What it is not.** It reads proof terms, so a lemma that an `aesop` bank used leaves its trace
only through the term that the search built. It counts edges, not the size or cost of a proof.
Its answers are of the loaded environment: a consumer that the file does not import is not seen.
-/

namespace Tools.LoadPaths

open Lean Elab Command ProofGraph

/-- The module that declares `c`, or the main module. -/
def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- Whether one of `scopes` is a prefix of the module `m`. -/
def within (scopes : List Name) (m : Name) : Bool := scopes.any (·.isPrefixOf m)

/-- The tree's own modules. -/
def treeScopes : List Name := [`Effect4, `Test, `Tools, `ProofGraph]

/-- An authored theorem: a theorem that no elaborator generated. -/
def authoredTheorem (env : Environment) (c : Name) : Bool :=
  (env.find? c matches some (.thmInfo _)) && !isAuxiliary env c

/-- The bound on one walk's stack pops: an engineering limit, as `ProofGraph.walkBudget`. -/
def walkBudget : Nat := 1000000

/-- **The direct dependencies of `c`**: the authored theorems that its value names, walking
through generated auxiliaries and through nothing else. `none` when the bound did not empty the
stack. -/
def directTheorems (env : Environment) (c : Name) : Option (Array Name) := Id.run do
  let some info := env.find? c | return some #[]
  let mut out : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack := (info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
  for _ in [0:walkBudget] do
    let some d := stack.back? | break
    stack := stack.pop
    if seen.contains d || d == c then continue
    seen := seen.insert d
    if authoredTheorem env d then
      out := out.push d
    else if isAuxiliary env d then
      let some di := env.find? d | continue
      stack := stack ++ ((di.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  if stack.isEmpty then return some out else return none

/-- **The graph**: for every authored theorem of the tree in the loaded environment, its direct
dependencies, and the reverse edges. -/
structure Graph where
  deps : Std.HashMap Name (Array Name) := {}
  usedBy : Std.HashMap Name (Array Name) := {}
  /-- theorems whose walk exhausted its bound -/
  exhausted : Array Name := #[]

/-- Build the graph over the tree's authored theorems. -/
def buildGraph (env : Environment) : Graph := Id.run do
  let mut g : Graph := {}
  for (c, _) in env.constants.toList do
    unless authoredTheorem env c && within treeScopes (moduleOf env c) do continue
    match directTheorems env c with
    | none => g := { g with exhausted := g.exhausted.push c }
    | some ds =>
      g := { g with deps := g.deps.insert c ds }
      for d in ds do
        g := { g with usedBy := g.usedBy.insert d ((g.usedBy.getD d #[]).push c) }
  return g

/-- The registry's roots present in the environment: claim pointers and requirement top nodes. -/
def roots (env : Environment) : Array Name :=
  let claims := Tools.Semantics.registry.claims.filterMap fun cl =>
    match cl.pointer with
    | .witness n => some n
    | .refutedBy _ n => some n
    | _ => none
  let tops := Tools.Semantics.registry.requirements.flatMap (·.top)
  ((claims ++ tops).filter env.contains).toArray

/-- **The load-bearing theorems**: every theorem that a root reaches along direct dependencies. -/
def loadBearing (g : Graph) (rs : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := rs
  for _ in [0:walkBudget * 10] do
    let some c := stack.back? | break
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    stack := stack ++ g.deps.getD c #[]
  return seen

/-- **The edges of some theorems of a landing**, by where each ends (the table above). It is the
one count: `#load_report` gives it over every theorem of the landing, and `#landing_plan` over the
theorems that its walk reaches in the landing (Codex's S1-PLAN-02). -/
structure Edges where
  local_ : Nat := 0
  tree : Nat := 0
  core : Nat := 0
  instances : Nat := 0
  /-- each tree theorem that an edge ends at, with how many do -/
  cited : Std.HashMap Name Nat := {}

/-- The reuse ratio, in percent, rounded down: tree edges over tree and local edges. -/
def Edges.ratio (e : Edges) : Nat :=
  if e.tree + e.local_ = 0 then 0 else (100 * e.tree) / (e.tree + e.local_)

/-- The tree theorems that the edges end at, the most cited first. -/
def Edges.joints (e : Edges) : Array (Name × Nat) :=
  e.cited.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1.toString < b.1.toString)

/-- **Count the edges of `members`**, theorems of the landing `landing`. -/
def countEdges (env : Environment) (g : Graph) (landing : List Name) (members : List Name) :
    Edges := Id.run do
  let mut e : Edges := {}
  for c in members do
    for d in g.deps.getD c #[] do
      let m := moduleOf env d
      if Meta.isInstanceCore env d then e := { e with instances := e.instances + 1 }
      else if within landing m then e := { e with local_ := e.local_ + 1 }
      else if within treeScopes m then
        e := { e with tree := e.tree + 1, cited := e.cited.insert d (e.cited.getD d 0 + 1) }
      else e := { e with core := e.core + 1 }
  return e

/-- **The report on a landing.** -/
structure Report where
  members : Nat
  edges : Edges
  loadBearing : Nat
  rootsIn : Nat
  unconsumed : Array Name
  offPath : Array Name
  joints : Array (Name × Nat)

/-- Measure the landing `landing` against the graph. -/
def measure (env : Environment) (g : Graph) (rs : Array Name) (load : Std.HashSet Name)
    (landing : List Name) : Report :=
  let members := (g.deps.toList.filter fun (c, _) => within landing (moduleOf env c)).map (·.1)
  let edges := countEdges env g landing members
  let isRoot (c : Name) : Bool := rs.contains c
  let unconsumed := members.filter fun c => (g.usedBy.getD c #[]).isEmpty && !isRoot c
  let offPath := members.filter fun c => !load.contains c && !unconsumed.contains c
  { members := members.length, edges,
    loadBearing := (members.filter load.contains).length,
    rootsIn := (members.filter isRoot).length,
    unconsumed := unconsumed.toArray.qsort (·.toString < ·.toString),
    offPath := offPath.toArray.qsort (·.toString < ·.toString),
    joints := edges.joints.extract 0 8 }

/-- The report as lines. -/
def Report.lines (r : Report) (landing : List Name) : List String :=
  [s!"landing {landing}: {r.members} theorems, {r.rootsIn} of them roots",
   s!"  edges: {r.edges.local_} local, {r.edges.tree} tree, {r.edges.core} core, " ++
     s!"{r.edges.instances} instance; reuse ratio {r.edges.ratio}%",
   s!"  load-bearing: {r.loadBearing} of {r.members}",
   s!"  unconsumed ({r.unconsumed.size}): {r.unconsumed.toList}",
   s!"  reached by a consumer, but by no root ({r.offPath.size}): {r.offPath.toList}",
   s!"  joints: {r.joints.toList.map fun (n, k) => s!"{n} ×{k}"}"]

/-- `#load_report M₁ M₂ …`: the report on the landing of the named module prefixes, against every
authored theorem of the tree that the file loads. -/
elab "#load_report " ms:ident+ : command => do
  let env ← getEnv
  let landing := ms.toList.map (·.getId)
  let g := buildGraph env
  let rs := roots env
  let load := loadBearing g rs
  let r := measure env g rs load landing
  let head := s!"graph: {g.deps.size} theorems of the tree, {rs.size} roots, {load.size} load-bearing" ++
    (if g.exhausted.isEmpty then "" else s!", {g.exhausted.size} walks exhausted")
  logInfo (String.intercalate "\n" (head :: r.lines landing))

/-- The first `k` components of a module name: its area. -/
def areaOf (k : Nat) (m : Name) : Name :=
  let cs := m.components
  cs.take k |>.foldl (fun acc c => acc ++ c) .anonymous

/-- `#load_map k`: for each area of the tree (the first `k` components of a module's name), its
theorems, how many are load-bearing, how many are unconsumed, and its reuse ratio. -/
elab "#load_map " k:num : command => do
  let env ← getEnv
  let g := buildGraph env
  let rs := roots env
  let load := loadBearing g rs
  let areas : Std.HashSet Name := g.deps.fold (init := {}) fun acc c _ =>
    acc.insert (areaOf k.getNat (moduleOf env c))
  let sorted := areas.toArray.qsort (·.toString < ·.toString)
  let mut lines : Array String := #[s!"graph: {g.deps.size} theorems of the tree, {rs.size} roots, {load.size} load-bearing"]
  for a in sorted do
    let r := measure env g rs load [a]
    lines := lines.push s!"{a}: {r.members} theorems, {r.loadBearing} load-bearing, {r.unconsumed.size} unconsumed, {r.offPath.size} off the roots' paths; reuse {r.edges.ratio}% ({r.edges.tree} tree, {r.edges.local_} local)"
  logInfo (String.intercalate "\n" lines.toList)

/-! ## The landing plan: a prediction before a slice

A slice's top theorems are written first, as a decomposition whose open steps are planned goals
(`proof_goal`, or the parts that `proof_sketch` makes). Their proofs then name what the slice
reuses and what it still owes, before any step is proved. `#landing_plan T₁ …` walks from the
tops through the theorems of their own modules, and sorts what the walk reaches:

| Reached | Means |
| --- | --- |
| a planned goal | a step the slice still owes: what has to land |
| a theorem of the tops' modules | a local step, proved or modulo goals (`ProofGraph.standing`) |
| a theorem of the tree outside them | a joint the slice reuses, with its load-bearing standing |

The predicted reuse ratio is the one `#load_report` gives (`countEdges`), over the theorems of the
tops' modules that the walk reaches. After the landing, `#load_report` on the same modules counts
every theorem of them, so the two agree when those modules hold only what the tops reach. A top
must be an authored theorem. -/

/-- What a landing plan reaches from its tops. -/
structure Prediction where
  owed : Array Name := #[]
  localSteps : Array Name := #[]
  /-- the theorems reached in the tops' modules, the tops and their goals included: what the
  edges are counted over -/
  members : Array Name := #[]

/-- Walk from `tops` through the authored theorems of `modules`, stopping at planned goals and at
theorems outside `modules`. -/
def predict (env : Environment) (modules : List Name) (tops : Array Name) : Prediction := Id.run do
  let mut pr : Prediction := {}
  let mut seen : Std.HashSet Name := {}
  let mut stack := tops
  for _ in [0:walkBudget] do
    let some c := stack.back? | break
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let inside := within modules (moduleOf env c)
    if inside then pr := { pr with members := pr.members.push c }
    if ProofGraph.isGoal env c then
      pr := { pr with owed := pr.owed.push c }
    else if inside then
      unless tops.contains c do pr := { pr with localSteps := pr.localSteps.push c }
      stack := stack ++ ((directTheorems env c).getD #[])
  return pr

/-- `#landing_plan T₁ …`: the prediction of a slice from its top theorems. -/
elab "#landing_plan " ts:ident+ : command => do
  let env ← getEnv
  let tops ← ts.mapM fun t => do
    let c ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
    -- a plan's top is a theorem: data has no proof to plan (Codex's S1-PLAN-03)
    unless authoredTheorem env c do
      throwErrorAt t "#landing_plan: {c} is not an authored theorem; a plan's top is a theorem"
    return c
  let modules := (tops.map (moduleOf env)).toList.eraseDups
  let pr := predict env modules tops
  let g := buildGraph env
  let load := loadBearing g (roots env)
  let edges := countEdges env g modules pr.members.toList
  let joints := edges.joints.filter fun (n, _) => !ProofGraph.isGoal env n
  let carrying := joints.filter fun (n, _) => load.contains n
  -- a step's standing is the proof graph's, so a step that rests on a goal is not called proved
  -- (Codex's S1-PLAN-01); a top and a joint carry theirs too, since a joint may rest on a goal
  -- outside the walk
  let named := tops ++ pr.localSteps ++ joints.map (·.1)
  let (standings, _) := (named.mapM fun c => do return (c, ← ProofGraph.standing env c)).run {}
  let standingOf (c : Name) : Option ProofGraph.Standing :=
    (standings.find? (·.1 == c)).bind fun (_, st) => st.map (·.1)
  let word (c : Name) : String :=
    match standingOf c with
    | some (.modulo goals) => s!"modulo {goals.toList}"
    | some st => st.word
    | none => "standing not reached in the walk's bound"
  let proved := pr.localSteps.filter fun c => standingOf c == some .proved
  let unproved := pr.localSteps.filter fun c => standingOf c != some .proved
  let jointWord (n : Name) (k : Nat) : String :=
    s!"{n}{if load.contains n then "" else " (off the roots' paths)"}" ++
      s!"{if standingOf n == some .proved then "" else s!" ({word n})"}{if k > 1 then s!" ×{k}" else ""}"
  let lines := [
    s!"landing plan for {tops.toList.map fun t => s!"{t} ({word t})"} in {modules}",
    s!"  to land ({pr.owed.size} planned goals): {pr.owed.toList}",
    s!"  local steps, proved ({proved.size}): {proved.toList}",
    s!"  local steps, not proved ({unproved.size}): {unproved.toList.map fun c => s!"{c} ({word c})"}",
    s!"  joints reused ({joints.size}, {carrying.size} of them load-bearing): " ++
      s!"{joints.toList.map fun (n, k) => jointWord n k}",
    s!"  predicted reuse: {edges.ratio}% ({edges.tree} tree edges, {edges.local_} local), " ++
      "as `#load_report` counts it"]
  logInfo (String.intercalate "\n" lines)

end Tools.LoadPaths
