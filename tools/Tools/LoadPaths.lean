import Lean
import ProofGraph.Population
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

/-- **The report on a landing.** -/
structure Report where
  members : Nat
  local_ : Nat
  tree : Nat
  core : Nat
  instances : Nat
  loadBearing : Nat
  rootsIn : Nat
  unconsumed : Array Name
  offPath : Array Name
  joints : Array (Name × Nat)

/-- The reuse ratio, in percent, rounded down. -/
def Report.ratio (r : Report) : Nat :=
  if r.tree + r.local_ = 0 then 0 else (100 * r.tree) / (r.tree + r.local_)

/-- Measure the landing `landing` against the graph. -/
def measure (env : Environment) (g : Graph) (rs : Array Name) (load : Std.HashSet Name)
    (landing : List Name) : Report := Id.run do
  let members := (g.deps.toList.filter fun (c, _) => within landing (moduleOf env c)).map (·.1)
  let mut local_ := 0
  let mut tree := 0
  let mut core := 0
  let mut instances := 0
  let mut cited : Std.HashMap Name Nat := {}
  for c in members do
    for d in g.deps.getD c #[] do
      let m := moduleOf env d
      if Meta.isInstanceCore env d then instances := instances + 1
      else if within landing m then local_ := local_ + 1
      else if within treeScopes m then
        tree := tree + 1
        cited := cited.insert d (cited.getD d 0 + 1)
      else core := core + 1
  let isRoot (c : Name) : Bool := rs.contains c
  let unconsumed := members.filter fun c => (g.usedBy.getD c #[]).isEmpty && !isRoot c
  let offPath := members.filter fun c => !load.contains c && !unconsumed.contains c
  let joints := (cited.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1.toString < b.1.toString))
  return { members := members.length, local_, tree, core, instances,
           loadBearing := (members.filter load.contains).length,
           rootsIn := (members.filter isRoot).length,
           unconsumed := unconsumed.toArray.qsort (·.toString < ·.toString),
           offPath := offPath.toArray.qsort (·.toString < ·.toString),
           joints := joints.extract 0 8 }

/-- The report as lines. -/
def Report.lines (r : Report) (landing : List Name) : List String :=
  [s!"landing {landing}: {r.members} theorems, {r.rootsIn} of them roots",
   s!"  edges: {r.local_} local, {r.tree} tree, {r.core} core, {r.instances} instance; reuse ratio {r.ratio}%",
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
    lines := lines.push s!"{a}: {r.members} theorems, {r.loadBearing} load-bearing, {r.unconsumed.size} unconsumed, {r.offPath.size} off the roots' paths; reuse {r.ratio}% ({r.tree} tree, {r.local_} local)"
  logInfo (String.intercalate "\n" lines.toList)

end Tools.LoadPaths
