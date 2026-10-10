import ProofGraph.Goal
import ProofGraph.Proof
import ProofGraph.Population

/-!
# The planning graph

The nodes are the planned goals (`proof_goal`, `ProofGraph.Goal`) and the theorems a plan names: a
requirement's top nodes. A node's status is its standing, read from its dependencies with goals as
leaves: a goal, proved modulo the goals its proof reaches, or proved. A decomposition is an
ordinary theorem whose proof uses goals: the kernel checked it when it was added, and the walk
reads its edges from the proof term. No authored edge, matcher or closing command exists
(decisions row 203).

A node's edges go to its **nearest nodes**: the walk from its proof stops at every other node
(LeanArchitect's `CollectUsed.collect` semantics, on an explicit stack). The same walk counts what
the proof brings in from the tree: theorems and definitions apart, auxiliaries (`isAuxiliary`)
walked through and not counted. Aesop rule banks leave no trace in a proof term; the banks a proof
called come from its syntax.

A node's real axioms must stay within the semantic ceiling (`disallowedAxioms`). The **next goals**
are the goals the named nodes rest on. `#plan_status G` prints a node's standing, the statements
of the goals it rests on, and what its proof brings in; the semantics report
(`tools/Tools/Semantics.lean`) renders the whole plan from the registry. This reflection data is
tooling only; it never enters stored program content.
-/
namespace ProofGraph
open Lean Meta Elab Command

/-- A node of the plan: a goal or a named theorem, with its standing and what its proof brings in. -/
structure Node where
  name : Name
  standing : Standing
  /-- the axioms its proof reaches, goals excluded -/
  axioms : Array Name := #[]
  /-- the nodes the walk from its proof reaches first -/
  nearest : Array Name := #[]
  lemmas : Nat := 0
  definitions : Nat := 0
  deriving Inhabited

/-- The goals the standing names: the node itself when it is a goal. -/
def Node.restsOn (n : Node) : Array Name :=
  match n.standing with
  | .goal => #[n.name]
  | .modulo goals => goals
  | .proved => #[]

structure Plan where
  nodes : Array Node
  deriving Inhabited

def Plan.find? (p : Plan) (name : Name) : Option Node := p.nodes.find? (·.name == name)

private def pushNew (acc : Array Name) (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) acc

/-- The goals the named nodes rest on, in order of first appearance. -/
def Plan.next (p : Plan) (names : Array Name) : Array Name :=
  let index : Std.HashMap Name Node := p.nodes.foldl (fun m n => m.insert n.name n) {}
  names.foldl (init := #[]) fun acc n => pushNew acc ((index[n]?).map (·.restsOn) |>.getD #[])

/-- Whether each imported module is in the tree that `scopes` names: one prefix test per module,
not one per constant. A caller computes it once and passes it down as data:
`EnvironmentHeader.moduleNames` builds a new array on every call, and a definition that returns
a closure is compiled with the closure's argument as one more parameter, so a table computed
inside it would be computed again on every call. -/
def treeModules (env : Environment) (scopes : List Name) : Array Bool :=
  env.header.moduleNames.map fun m => scopes.any (·.isPrefixOf m)

/-- Whether constant `c` is declared in the tree: `tree` is `treeModules`' answer, and `main`
whether the current module is in the tree. -/
def inTree (env : Environment) (tree : Array Bool) (main : Bool) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => tree[i.toNat]!
  | none => main

/-- Every goal declared in a module whose name one of `scopes` prefixes, sorted. A goal is tagged
in the module that declares it, so the goals are read from the tag's entries of the modules in
the tree, and from the current module's own tags, never from a scan of every constant. -/
def goalsIn (env : Environment) (scopes : List Name) : Array Name := Id.run do
  let tree := treeModules env scopes
  let mut goals : Array Name := #[]
  for h : i in [0:tree.size] do
    if tree[i] then goals := goals ++ PersistentEnvExtension.getModuleEntries goalExt env i
  if scopes.any (·.isPrefixOf env.mainModule) then
    goals := (goalExt.getState env).foldl (·.push ·) goals
  return goals.qsort (·.toString < ·.toString)

/-- The plan's bound on the walk's stack pops. It is an engineering limit: no law says that an
environment stays under it. A repeated dependency entry costs a pop too, before the `seen` test
skips it. -/
def walkBudget : Nat := 10000000

/-- What a constant of the tree gives every walk: the constants its type and value name, and its
kind among the counts (1 a theorem, 2 a definition, 0 neither or an auxiliary). The walks of all
the nodes share these, so a proof term is read once and not once per node that reaches it. -/
abbrev WalkMemo := Std.HashMap Name (Array Name × UInt8)

/-- What the proof of `name` brings in, stopping at the nodes `isNode` selects other than itself:
its nearest nodes, and the counts of the theorems and the definitions of the tree that it walks
through. `none` when `budget` pops did not empty the stack. The answer would then be a part of
the truth, so the walk gives none, as the axiom collector does (`reachedAxioms`), and
`buildPlan` refuses. The memo holds each tree constant's dependencies and kind, which depend on
the environment alone, so one memo serves every walk over one environment. -/
def walkMemo (env : Environment) (budget : Nat) (tree : Array Bool) (main : Bool)
    (isNode : Name → Bool) (name : Name) :
    StateM WalkMemo (Option (Array Name × Nat × Nat)) := do
  let some info := env.find? name | return some (#[], 0, 0)
  let mut nearest : Array Name := #[]
  let mut lemmas := 0
  let mut definitions := 0
  let mut seen : Std.HashSet Name := {}
  let mut stack := (info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
  -- each constant is entered once; the bound is a loop bound
  for _ in [0:budget] do
    let some c := stack.back? | break
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c != name && isNode c then
      unless nearest.contains c do nearest := nearest.push c
      continue
    unless inTree env tree main c do continue
    let known := (← get)[c]?
    let entry := known.orElse fun _ => (env.find? c).map fun ci =>
      let kind : UInt8 := if isAuxiliary env c then 0 else match ci with
        | .thmInfo _ => 1
        | .defnInfo _ | .opaqueInfo _ => 2
        | _ => 0
      (ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]), kind)
    let some (deps, kind) := entry | continue
    if known.isNone then modify (·.insert c (deps, kind))
    if kind == 1 then lemmas := lemmas + 1
    else if kind == 2 then definitions := definitions + 1
    stack := stack ++ deps
  -- an unfinished stack is an exhausted walk, never a short answer
  if stack.isEmpty then return some (nearest, lemmas, definitions) else return none

/-- `walkMemo` with a fresh memo, over the current environment. -/
def walkWithin (budget : Nat) (scopes : List Name) (isNode : Name → Bool) (name : Name) :
    MetaM (Option (Array Name × Nat × Nat)) := do
  let env ← getEnv
  let tree := treeModules env scopes
  let main := scopes.any (·.isPrefixOf env.mainModule)
  return ((walkMemo env budget tree main isNode name).run {}).1

/-- The plan over the theorems `names` and every goal in `scopes`: each node's standing, checked
against the ceiling, and its nearest nodes and brought-in counts. -/
def buildPlan (scopes : List Name) (names : Array Name) (memo : IO.Ref AxiomMemo) : MetaM Plan := do
  let env ← getEnv
  let all := pushNew names (goalsIn env scopes)
  let nodeSet : Std.HashSet Name := Std.HashSet.ofArray all
  let isNode (c : Name) : Bool := nodeSet.contains c
  let tree := treeModules env scopes
  let main := scopes.any (·.isPrefixOf env.mainModule)
  let mut walks : WalkMemo := {}
  let mut nodes : Array Node := #[]
  for n in all do
    unless (env.find? n) matches some (.thmInfo _) do throwError "plan: {n} is not a theorem"
    let (reached, table) := (standing env n).run (← memo.get)
    memo.set table
    let some (s, axioms) := reached | throwError "plan: axiom collection exhausted its budget at {n}"
    let extra := disallowedAxioms axioms
    unless extra.isEmpty do throwError "plan: {n}: disallowed axioms {extra}"
    let (walked, memo') := (walkMemo env walkBudget tree main isNode n).run walks
    walks := memo'
    let some (nearest, lemmas, definitions) := walked
      | throwError "plan: the dependency walk exhausted its budget at {n}"
    nodes := nodes.push { name := n, standing := s, axioms, nearest, lemmas, definitions }
  return { nodes }

/-- One line per node and the statements of the goals it rests on, for the editor and receipts. -/
def Plan.describe (p : Plan) (tops : Array Name) : MetaM String := do
  let mut out := ""
  for n in tops do
    let some node := p.find? n | continue
    out := out ++ s!"{n}: {node.standing.word}"
    match node.standing with
    | .modulo goals => out := out ++ s!" {goals.toList}"
    | _ => pure ()
    out := out ++ s!"; nearest {node.nearest.toList}; {node.lemmas} lemmas, {node.definitions} definitions\n"
  let next := p.next tops
  out := out ++ s!"next goals: {next.size}"
  for g in next do
    let some (.thmInfo t) := (← getEnv).find? g | continue
    out := out ++ s!"\n  goal {g} : {← ppExpr t.type}"
  return out

/-- `#plan_status G₁ …`: the standing of each `Gᵢ`, and the statements of the goals they rest on.
The tree is the modules under the current module's root (`Effect4` in a law module, `Test` in a
battery): its goals are the nodes, and its declarations are what the counts count. -/
syntax (name := planStatus) "#plan_status " ident+ : command

@[command_elab planStatus] def elabPlanStatus : CommandElab := fun stx => do
  let report ← liftTermElabM do
    let tops ← stx[1].getArgs.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
    let plan ← buildPlan [(← getEnv).mainModule.getRoot] tops (← IO.mkRef {})
    plan.describe tops
  logInfo report

end ProofGraph
