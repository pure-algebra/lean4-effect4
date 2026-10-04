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
  names.foldl (init := #[]) fun acc n => pushNew acc ((p.find? n).map (·.restsOn) |>.getD #[])

/-- Every goal declared in a module whose name one of `scopes` prefixes, sorted. -/
def goalsIn (env : Environment) (scopes : List Name) : Array Name :=
  let inScope (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => scopes.any (·.isPrefixOf env.header.moduleNames[i.toNat]!)
    | none => scopes.any (·.isPrefixOf env.mainModule)
  (env.constants.toList.filterMap fun (n, _) =>
    if isGoal env n && inScope n then some n else none).toArray.qsort (·.toString < ·.toString)

/-- What the proof of `name` brings in, stopping at the nodes `isNode` selects other than itself. -/
private def walk (scopes : List Name) (isNode : Name → Bool) (name : Name) :
    MetaM (Array Name × Nat × Nat) := do
  let env ← getEnv
  let some info := env.find? name | return (#[], 0, 0)
  let inTree (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some i => scopes.any (·.isPrefixOf env.header.moduleNames[i.toNat]!)
    | none => scopes.any (·.isPrefixOf env.mainModule)
  let mut nearest : Array Name := #[]
  let mut lemmas := 0
  let mut definitions := 0
  let mut seen : Std.HashSet Name := {}
  let mut stack := (info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
  -- each constant is entered once; the bound is a loop bound
  for _ in [0:10000000] do
    let some c := stack.back? | break
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c != name && isNode c then
      unless nearest.contains c do nearest := nearest.push c
      continue
    unless inTree c do continue
    let some ci := env.find? c | continue
    unless isAuxiliary env c do
      match ci with
      | .thmInfo _ => lemmas := lemmas + 1
      | .defnInfo _ | .opaqueInfo _ => definitions := definitions + 1
      | _ => pure ()
    stack := stack ++ ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  return (nearest, lemmas, definitions)

/-- The plan over the theorems `names` and every goal in `scopes`: each node's standing, checked
against the ceiling, and its nearest nodes and brought-in counts. -/
def buildPlan (scopes : List Name) (names : Array Name) (memo : IO.Ref AxiomMemo) : MetaM Plan := do
  let env ← getEnv
  let all := pushNew names (goalsIn env scopes)
  let isNode (c : Name) : Bool := all.contains c
  let mut nodes : Array Node := #[]
  for n in all do
    unless (env.find? n) matches some (.thmInfo _) do throwError "plan: {n} is not a theorem"
    let (reached, table) := (standing env n).run (← memo.get)
    memo.set table
    let some (s, axioms) := reached | throwError "plan: axiom collection exhausted its budget at {n}"
    let extra := disallowedAxioms axioms
    unless extra.isEmpty do throwError "plan: {n}: disallowed axioms {extra}"
    let (nearest, lemmas, definitions) ← walk scopes isNode n
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
