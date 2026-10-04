import ProofGraph.Ledger
import ProofGraph.Search
import ProofGraph.Population

/-!
# The planning graph

The nodes are the ledger's goals and the proved theorems a plan names. A **reduction** is a
conditional theorem `r : ∀ ys, H₁ → … → Hₙ → C`, authored as reducing one target node. It becomes
an **edge** in four steps.

1. `C` is unified with the target's proposition, opened under the target's binders. A conclusion
   that does not unify is refused.
2. Each premise `Hᵢ` that the unification left open is matched to a node. The node's
   proposition, opened with metavariables, must unify with the premise's body under the premise's
   own binders, and every argument of the node must be fixed by that unification. Candidates are
   filtered by the head constant of their conclusion first.
3. With every premise matched, the implication `Q₁ → … → Qₖ → P` from the matched nodes'
   propositions to the target's is built from `r` and checked in the kernel without being added
   (`checkDeclaration`), and its type and proof must stay within the semantic ceiling
   (`disallowedAxioms`), which the kernel check alone does not hold. A wrong match cannot pass;
   the matcher only chooses candidates.
4. A premise that no node matches is a **loose premise**: an obligation nobody has declared. It is
   reported, not refused, and the edge stays unchecked, so it never makes its target ready.

Statuses are derived, never authored (`Status`). The **next goals** are the open goals that are
declared or ready, and the loose premises. `closeReady` proves a ready goal: it applies the checked
implication to the premise nodes' proofs and publishes `g.checked` through `addTheorem`, which
checks it again. The commands `#plan_status` and `#obligation_close` expose both in the editor; the
semantics report (`tools/Tools/Semantics.lean`) renders the whole plan from the registry.

The design is `docs/research/2026-10-04-reference-scout/proof-graph.md` §3.4: a sorry-free
analogue of a blueprint, whose edges the kernel checks. This reflection data is tooling only; it
never enters stored program content.
-/
namespace ProofGraph
open Lean Meta Elab Command

/-- A node of the plan: a ledger goal, or a proved theorem the plan names. -/
structure Node where
  name : Name
  levels : List Name
  proposition : Expr
  /-- a ledger goal, as against a proved theorem named as a node -/
  isGoal : Bool
  /-- the theorem that proves the node: the node itself, or a goal's validated `checked` companion -/
  proof : Option Name
  deriving Inhabited

def Node.proved (n : Node) : Bool := n.proof.isSome

/-- A node from a ledger goal. Its `checked` companion, when present, must validate. -/
def Node.ofGoal (g : Goal) : MetaM Node := do
  let checked := g.id ++ `checked
  let proof ← if (← getEnv).contains checked then do
      let ref : ProofRef := ⟨checked, g.levels, g.proposition⟩
      if let .error why ← ref.validate then throwError "plan: {why}"
      pure (some checked)
    else pure none
  return { name := g.id, levels := g.levels, proposition := g.proposition, isGoal := true, proof }

/-- A node from a proved theorem, which must hold within the ceiling. -/
def Node.ofTheorem (name : Name) : MetaM Node := do
  let .thmInfo t ← getConstInfo name | throwError "plan: {name} is not a theorem"
  let ref : ProofRef := ⟨name, t.levelParams, t.type⟩
  if let .error why ← ref.validate then throwError "plan: {why}"
  return { name, levels := t.levelParams, proposition := t.type, isGoal := false, proof := some name }

/-- The node for a name: a ledger goal when the name is one, otherwise a proved theorem. -/
def Node.ofName (name : Name) : MetaM Node := do
  match ← readGoal name with
  | some g => Node.ofGoal g
  | none => Node.ofTheorem name

/-- Every ledger goal declared in a module whose name one of `scopes` prefixes. -/
def goalsIn (scopes : List Name) : MetaM (Array Goal) := do
  let env ← getEnv
  let mut out : Array Goal := #[]
  for (name, info) in env.constants.toList do
    unless info matches .thmInfo _ && info.type.getForallBody.isAppOfArity ``Obligation 1 do
      continue
    let module := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    unless scopes.any (·.isPrefixOf module) do continue
    if let some g ← readGoal name then out := out.push g
  return out.qsort (·.id.toString < ·.id.toString)

/-- One premise of a reduction: its statement as printed, and what discharges it: a node, or a
hypothesis of the target itself. A premise with neither is loose. -/
structure PremiseMatch where
  premise : String
  node : Option Name
  byHypothesis : Bool := false
  deriving Inhabited

def PremiseMatch.loose (m : PremiseMatch) : Bool := m.node.isNone && !m.byHypothesis

/-- An edge of the plan: `reduction` reduces `target` to the nodes its premises matched. -/
structure Edge where
  target : Name
  reduction : Name
  premises : Array PremiseMatch
  /-- every premise matched and the kernel accepted the implication -/
  checked : Bool
  /-- the checked implication `Q₁ → … → Qₖ → P`, closed, with the matched nodes and their
  universe instances in binder order; `none` while a premise is loose -/
  implication : Option (Expr × Array (Name × List Level)) := none
  deriving Inhabited

/-- The derived status of a node. -/
inductive Status
  /-- the goal is declared, and no checked edge concludes it -/
  | declared
  /-- a checked edge concludes the goal, and some premise node is open -/
  | reduced
  /-- a checked edge concludes the goal, and every premise node is proved -/
  | ready
  /-- a validated theorem proves the node -/
  | proved
  deriving Inhabited, BEq, Repr

def Status.word : Status → String
  | .declared => "declared"
  | .reduced => "reduced"
  | .ready => "ready"
  | .proved => "proved"

private def conclusionHead (e : Expr) : Option Name := e.getForallBody.getAppFn.constName?

/-- The node indices worth trying for a premise body with this head. -/
private def candidates (nodes : Array Node) (body : Expr) : Array Nat :=
  let head := body.getAppFn.constName?
  (Array.range nodes.size).filter fun j =>
    head.isNone || conclusionHead nodes[j]!.proposition == head

/-- Find the first node whose proposition has the premise `T` as an instance, every argument of
the node fixed by the unification. All assignments are rolled back; the result is the node and
its universe instance. -/
private def findNode (nodes : Array Node) (T : Expr) : MetaM (Option (Nat × List Level)) :=
  forallTelescope T fun _ body => do
    for j in candidates nodes body do
      let node := nodes[j]!
      let saved ← saveState
      let us ← node.levels.mapM fun _ => mkFreshLevelMVar
      let (zs, _, B) ← forallMetaTelescope (node.proposition.instantiateLevelParams node.levels us)
      let unified ← isDefEq B body
      let fixed ← zs.allM fun z => return !(← instantiateMVars z).hasExprMVar
      let us ← us.mapM instantiateLevelMVars
      saved.restore
      if unified && fixed && !us.any (·.hasMVar) then return some (j, us)
    return none

/-- Discharge the premise `T` by an instance of the placeholder `q : Q`, where `Q` is the matched
node's proposition at universe instance `us`. The unification is redone and kept. -/
private def discharge (node : Node) (us : List Level) (q : Expr) (T : Expr) : MetaM Expr :=
  forallTelescope T fun ds body => do
    let (zs, _, B) ← forallMetaTelescope (node.proposition.instantiateLevelParams node.levels us)
    unless ← isDefEq B body do throwError "plan: the match of {node.name} did not replay"
    mkLambdaFVars ds (← instantiateMVars (mkAppN q zs))

/-- Turn the authored reduction of `target` by `r` into an edge (steps 1–4 of the module
docstring). -/
def reduce (nodes : Array Node) (target : Node) (r : Name) : MetaM Edge := do
  let .thmInfo rInfo ← getConstInfo r | throwError "plan: reduction {r} is not a theorem"
  -- placeholders for the matched nodes live in the empty context, so abstracting the target's
  -- binders never reverts them
  let (lamXs, placeholders, premises) ← forallTelescope target.proposition fun xs A => do
    let us ← rInfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let (ms, _, C) ← forallMetaTelescope (rInfo.type.instantiateLevelParams rInfo.levelParams us)
    unless ← isDefEq C A do
      throwError "plan: the conclusion of {r} does not unify with {target.name}"
    let mut placeholders : Array (Expr × Name × List Level) := #[]
    let mut premises : Array PremiseMatch := #[]
    let mut loose := false
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let T ← instantiateMVars (← inferType m)
      unless ← isProp T do continue
      let shown := toString (← ppExpr T)
      -- a hypothesis of the target discharges the premise before any node is tried
      if let some x ← xs.findM? (fun x => do
          let t ← inferType x
          return (← isProp t) && (← isDefEq t T)) then
        m.mvarId!.assign x
        premises := premises.push ⟨shown, none, true⟩
        continue
      match ← findNode nodes T with
      | none =>
        premises := premises.push ⟨shown, none, false⟩
        loose := true
      | some (j, nodeUs) =>
        let node := nodes[j]!
        let q ← match placeholders.find? (fun (_, n, l) => n == node.name && l == nodeUs) with
          | some (q, _, _) => pure q
          | none => do
            let Q := node.proposition.instantiateLevelParams node.levels nodeUs
            let q ← mkFreshExprMVarAt {} {} Q
            placeholders := placeholders.push (q, node.name, nodeUs)
            pure q
        m.mvarId!.assign (← discharge node nodeUs q T)
        premises := premises.push ⟨shown, some node.name, false⟩
    if loose then return (none, placeholders, premises)
    let value ← instantiateMVars (mkAppN (mkConst r us) ms)
    return (some (← mkLambdaFVars xs value), placeholders, premises)
  let some lamXs := lamXs
    | return { target := target.name, reduction := r, premises, checked := false }
  -- each matched node's proposition at the universe instance its match fixed
  let typeOf (n : Name) (us : List Level) : Expr :=
    let node := (nodes.find? (·.name == n)).get!
    node.proposition.instantiateLevelParams node.levels us
  let decls := placeholders.mapIdx fun i (_, n, us) =>
    ((`q).appendIndexAfter i, fun _ => pure (typeOf n us))
  withLocalDeclsD decls fun qs => do
    let mut body := lamXs
    for ((q, _, _), qf) in placeholders.zip qs do
      body := body.replace fun e => if e == q then some qf else none
    let value ← mkLambdaFVars qs body
    let type ← mkForallFVars qs target.proposition
    if value.hasMVar || type.hasMVar then
      throwError "plan: {r} leaves an argument unfixed when it reduces {target.name}"
    -- the kernel check alone does not hold the semantic ceiling; the edge must, as
    -- `addTheorem` does for a published proof
    let extra := disallowedAxioms (← axiomsOfTheorem type value)
    unless extra.isEmpty do
      throwError "plan: the edge {r} → {target.name} reaches disallowed axioms {extra}"
    let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
    let name ← mkFreshUserName `_planEdge
    checkDeclaration (← getEnv).toKernelEnv <| .thmDecl { name, levelParams := levels, type, value }
    return { target := target.name, reduction := r, premises, checked := true,
             implication := some (value, placeholders.map fun (_, n, us) => (n, us)) }

/-- The plan over a node set and the authored reductions `(target, reduction)`. -/
structure Plan where
  nodes : Array Node
  edges : Array Edge
  deriving Inhabited

/-- The derived status of the node `name`. -/
def Plan.status (p : Plan) (name : Name) : Status := Id.run do
  let some node := p.nodes.find? (·.name == name) | return .declared
  if node.proved then return .proved
  let proved (n : Name) := (p.nodes.find? (·.name == n)).any (·.proved)
  let checkedEdges := p.edges.filter fun e => e.target == name && e.checked
  if checkedEdges.isEmpty then return .declared
  if checkedEdges.any (·.premises.all fun m => m.byHypothesis || m.node.any proved) then
    return .ready
  return .reduced

/-- The loose premises: `(target, reduction, premise)`. -/
def Plan.loose (p : Plan) : Array (Name × Name × String) :=
  p.edges.foldl (init := #[]) fun acc e =>
    e.premises.foldl (init := acc) fun acc m =>
      if m.loose then acc.push (e.target, e.reduction, m.premise) else acc

/-- The nodes reachable from `tops` along matched premises, tops included, in visit order. -/
def Plan.reachable (p : Plan) (tops : Array Name) : Array Name := Id.run do
  let mut seen : Array Name := #[]
  let mut stack := tops
  for _ in [:p.nodes.size + tops.size + 1] do
    if stack.isEmpty then break
    let mut next : Array Name := #[]
    for n in stack do
      if seen.contains n then continue
      seen := seen.push n
      for e in p.edges do
        if e.target == n then
          for m in e.premises do
            if let some d := m.node then next := next.push d
    stack := next
  return seen

/-- The next goals among the nodes reachable from `tops`: open goals that are declared or ready. -/
def Plan.next (p : Plan) (tops : Array Name) : Array Name :=
  (p.reachable tops).filter fun n =>
    (p.nodes.find? (·.name == n)).any (·.isGoal) &&
      (p.status n == .declared || p.status n == .ready)

/-- Build the plan, refusing a cycle among matched edges (Kahn's algorithm). -/
def buildPlan (nodes : Array Node) (reductions : Array (Name × Name)) : MetaM Plan := do
  let mut edges : Array Edge := #[]
  for (target, r) in reductions do
    let some node := nodes.find? (·.name == target)
      | throwError "plan: reduction {r} names {target}, which is not a node"
    edges := edges.push (← reduce nodes node r)
  let pairs := edges.foldl (init := #[]) fun acc e =>
    e.premises.foldl (init := acc) fun acc m => match m.node with
      | some d => acc.push (e.target, d)
      | none => acc
  let mut remaining := nodes.map (·.name)
  for _ in [:nodes.size] do
    remaining := remaining.filter fun n =>
      pairs.any fun (src, dst) => src == n && remaining.contains dst
  unless remaining.isEmpty do throwError "plan: cycle through {remaining}"
  return { nodes, edges }

/-- Prove the ready goal `name` along one of its checked edges, publishing `name.checked`. -/
def closeReady (p : Plan) (name : Name) : MetaM ProofRef := do
  unless p.status name == .ready do
    throwError "plan: {name} is {(p.status name).word}, not ready"
  let some node := p.nodes.find? (·.name == name) | throwError "plan: {name} is not a node"
  let proved (n : Name) := (p.nodes.find? (·.name == n)).any (·.proved)
  let some edge := p.edges.find? fun e =>
      e.target == name && e.checked && e.premises.all fun m => m.byHypothesis || m.node.any proved
    | throwError "plan: no checked edge proves {name}"
  let some (impl, args) := edge.implication | throwError "plan: edge of {name} is unchecked"
  let mut proof := impl
  for (n, us) in args do
    let some premise := (p.nodes.find? (·.name == n)).bind (·.proof)
      | throwError "plan: premise {n} has no proof"
    proof := mkApp proof (mkConst premise us)
  addTheorem (name ++ `checked) node.levels node.proposition (← instantiateMVars proof)

/-- What a proved node's proof brings in, walked from its proof and stopping at nodes
(LeanArchitect's `CollectUsed.collect` semantics, on an explicit stack): the nodes it reaches
first, and the declarations of the tree (modules a prefix in `scopes` selects) it passes through
on the way, theorems and definitions apart. An instance counts as the definition it is: the
instance table is an extension that an environment imported without its extensions does not fill.
Auxiliaries (`isAuxiliary`) are walked through and not counted. Aesop rule banks leave no trace in
a proof term; the banks a proof called come from its syntax. -/
structure BroughtIn where
  nearest : Array Name := #[]
  lemmas : Nat := 0
  definitions : Nat := 0
  deriving Inhabited

def broughtIn (scopes : List Name) (p : Plan) (node : Node) : MetaM BroughtIn := do
  let env ← getEnv
  let some proof := node.proof | return {}
  let some info := env.find? proof | return {}
  let isNode (c : Name) : Bool := c != node.name && c != proof &&
    p.nodes.any fun n => n.name == c || n.proof == some c
  let inTree (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some i => scopes.any (·.isPrefixOf env.header.moduleNames[i.toNat]!)
    | none => false
  let mut out : BroughtIn := {}
  let mut seen : Std.HashSet Name := {}
  let mut stack := (info.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
  -- each constant is entered once; the bound is a loop bound
  for _ in [0:10000000] do
    let some c := stack.back? | break
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isNode c then
      let target := (p.nodes.find? fun n => n.name == c || n.proof == some c).get!.name
      unless out.nearest.contains target do out := { out with nearest := out.nearest.push target }
      continue
    unless inTree c do continue
    let some ci := env.find? c | continue
    unless isAuxiliary env c do
      match ci with
      | .thmInfo _ => out := { out with lemmas := out.lemmas + 1 }
      | .defnInfo _ | .opaqueInfo _ => out := { out with definitions := out.definitions + 1 }
      | _ => pure ()
    stack := stack ++ ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
  return out

/-- One line per edge and status, for the editor and the receipts. -/
def Plan.describe (p : Plan) (tops : Array Name) : MetaM String := do
  let mut out := ""
  for n in p.reachable tops do
    out := out ++ s!"{n}: {(p.status n).word}\n"
    for e in p.edges.filter (·.target == n) do
      out := out ++ s!"  via {e.reduction} ({if e.checked then "checked" else "unchecked"})\n"
      for m in e.premises do
        let by_ := match m.node with
          | some d => d.toString
          | none => if m.byHypothesis then "hypothesis" else "loose"
        out := out ++ s!"    {by_} ⊢ {m.premise}\n"
  let next := p.next tops
  out := out ++ s!"next goals: {next.toList}"
  let loose := (p.loose).filter fun (t, _, _) => (p.reachable tops).contains t
  unless loose.isEmpty do
    out := out ++ s!"\nloose premises: {loose.size}"
  return out

/-- `#plan_status g via r₁ … from n₁ …`: the plan reachable from the node `g`, over every ledger
goal in the environment's modules plus the proved theorems `nᵢ`, with the reductions `rᵢ` of
`g` or of any node they reach (each `rᵢ` names its target by `for`). -/
syntax (name := planStatus) "#plan_status " ident
  (" via " (ident " for " ident),+)? (" from " ident+)? : command

private def planOf (stx : Syntax) : TermElabM (Name × Plan) := do
  let top ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let reductions ← if stx[2].isNone then pure #[] else
    stx[2][1].getSepArgs.mapM fun pair => do
      return (← realizeGlobalConstNoOverloadWithInfo pair[2],
        ← realizeGlobalConstNoOverloadWithInfo pair[0])
  let froms ← if stx[3].isNone then pure #[] else
    stx[3][1].getArgs.mapM fun id => do return ← realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let scopes := env.header.moduleNames.toList ++ [env.mainModule]
  let mut nodes ← (← goalsIn scopes).mapM fun g => Node.ofGoal g
  for n in froms do
    unless nodes.any (·.name == n) do nodes := nodes.push (← Node.ofTheorem n)
  unless nodes.any (·.name == top) do nodes := nodes.push (← Node.ofName top)
  return (top, ← buildPlan nodes reductions)

@[command_elab planStatus] def elabPlanStatus : CommandElab := fun stx => do
  let report ← liftTermElabM do
    let (top, plan) ← planOf stx
    plan.describe #[top]
  logInfo report

/-- `#obligation_close g via r for g from n₁ …`: prove the ready goal `g` from its checked edge. -/
syntax (name := obligationClose) "#obligation_close " ident
  (" via " (ident " for " ident),+)? (" from " ident+)? : command

@[command_elab obligationClose] def elabObligationClose : CommandElab := fun stx => do
  liftTermElabM do
    let (top, plan) ← planOf stx
    discard <| closeReady plan top

end ProofGraph
