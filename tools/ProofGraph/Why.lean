import ProofGraph.Goal
import ProofGraph.Proof
import ProofGraph.Registry
import Tools.Graph.Path

/-!
# Why a declaration depends on another: checked dependency paths

`#why A B` answers through what `A` depends on `B`. `#why A` answers it for every planned goal
and every axiom outside `[propext, Quot.sound]` that `A` reaches. `#goal_impact G` names the
registry claims and the requirements whose nodes rest on the goal `G`, and `#goal_impact` ranks
every goal by them. `#axiom_audit` and the axiom gate explain a refusal by the same paths
(`auditCauses`).

**The relation is the axiom walk's.** An edge goes from a constant to a constant its content
names (`usedConstantsOf`: a declaration's type and value, an inductive's constructors), and the
stopping policy is the walk's: a planned goal is a leaf, and no path enters one on its way to
another constant (decisions row 203). So a path explains the walk's verdict, and no other
relation's.

**The search is untrusted; the answer is checked.** A breadth-first walk proposes a shortest
edge list. `Tools.Graph.Walk.read?` must accept it between the two endpoints, so the answer is a
`Walk` whose edges are the proposed list exactly (`Walk.edges_of_read?`), and every edge is read
again from the environment under the policy (`edgeRead`). A refused list is an error, never a
shorter answer. "No path" is the walk's answer after it read every constant the source reaches;
a walk that runs out of its step budget says so and answers nothing.

Placement: tooling over the planning graph of decisions rows 203 and 207. Its consumers are a
landing's audit (`#axiom_audit`) and a seat's planning (`#why`, `#goal_impact`), and the axiom gate. It is the next
consumer the checked graph tools' receipt names
(`docs/research/2026-10-10-checked-graph-tools/README.md`). It establishes no property of a
proof: a path is evidence of one dependency in this environment.
-/
namespace ProofGraph
open Lean Elab Command Meta
open Tools.Semantics (Claim Requirement registry)

/-- An edge of the dependency relation: a constant, and one constant its content names. -/
abbrev DepEdge := Name × Name

/-- A dependency path from `a` to `b`, its endpoints in its type. -/
abbrev DepPath (a b : Name) := Tools.Graph.Walk (fun e : DepEdge => e) a b

/-- Whether the walk reads edge `e`: its source is no leaf under `stop`, and its content names
the edge's target. -/
def edgeRead (env : Environment) (stop : Name → Bool) (e : DepEdge) : Bool :=
  !stop e.1 && match env.find? e.1 with
    | some ci => (usedConstantsOf ci).contains e.2
    | none => false

/-- What a search answers. -/
inductive Found
  /-- a proposed edge list, not yet checked -/
  | path (edges : List DepEdge)
  /-- no constant the source reaches is a target; the count of constants read -/
  | absent (read : Nat)
  /-- the step budget ran out -/
  | exhausted

/-- The search's bound on the constants it reads: an engineering limit, far above the law graph
(the plan's `walkBudget`). Running out is an answer of its own. -/
def searchBudget : Nat := 10000000

/-- The edges from `source` to `target` along the parents a search recorded. -/
private def trace (parent : Std.HashMap Name Name) (source target : Name) : List DepEdge := Id.run do
  let mut edges : List DepEdge := []
  let mut c := target
  for _ in [0:parent.size + 1] do
    if c == source then break
    let some p := parent[c]? | break
    edges := (p, c) :: edges
    c := p
  return edges

/-- Breadth-first from `source` to the first constant `target` selects, through the edges the
walk reads under `stop`: a shortest proposed edge list. -/
def proposePath (env : Environment) (stop : Name → Bool) (target : Name → Bool) (source : Name) :
    Found := Id.run do
  if target source then return .path []
  let mut parent : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[source]
  let mut head := 0
  for _ in [0:searchBudget] do
    let some c := queue[head]? | return .absent queue.size
    head := head + 1
    if c != source && stop c then continue
    let some ci := env.find? c | continue
    for d in usedConstantsOf ci do
      if d == source || parent.contains d then continue
      parent := parent.insert d c
      if target d then return .path (trace parent source d)
      queue := queue.push d
  return .exhausted

/-- Check a proposed edge list: `Walk.read?` accepts it from `a` to `b`, and the walk reads each
edge under `stop` (the source itself is never a leaf). -/
def checkPath (env : Environment) (stop : Name → Bool) (a b : Name) (edges : List DepEdge) :
    Except String (DepPath a b) :=
  match Tools.Graph.Walk.read? (fun e : DepEdge => e) a b edges with
  | none => .error s!"the proposed path does not chain from {a} to {b}"
  | some path =>
    match edges.find? fun e => !edgeRead env (fun c => c != a && stop c) e with
    | some (x, y) => .error s!"the walk does not read the edge {x} → {y}"
    | none => .ok path

/-- The walk's stopping policy for a path from `a` to `b`: a planned goal other than the two
endpoints is a leaf. -/
def pathStop (env : Environment) (a b : Name) (c : Name) : Bool :=
  c != a && c != b && isGoal env c

/-- A checked path from `a` to `b` under the walk's policy, or why there is none. -/
def whyPath (env : Environment) (a b : Name) : Except String (DepPath a b) :=
  let stop := pathStop env a b
  match proposePath env stop (· == b) a with
  | .exhausted => .error s!"the walk from {a} ran out of its step budget"
  | .absent _ => .error s!"{a} does not depend on {b}: the walk read every constant {a} \
      reaches, entering no planned goal"
  | .path edges => checkPath env stop a b edges

/-- The module that declares a constant, or the current one. -/
def declaringModule (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- Whether a constant is the toolchain's: declared under `Init`, `Lean`, `Std` or `Lake`. -/
def isToolchain (env : Environment) (c : Name) : Bool :=
  [`Init, `Lean, `Std, `Lake].contains (declaringModule env c).getRoot

/-- The hops a path prints: a run of more than five toolchain constants keeps its first hop and its
last two, and counts the rest. The first is where the tree's code enters the toolchain; the last
two are how the target is reached. The path itself keeps every edge. -/
def shownHops (env : Environment) (hops : List Name) : List (Name ⊕ Nat) :=
  let flush (run : List Name) : List (Name ⊕ Nat) :=
    if run.length > 5 then
      [.inl run.head!, .inr (run.length - 3)] ++ (run.drop (run.length - 2)).map .inl
    else run.map .inl
  let (out, run) := hops.foldl (init := (([] : List (Name ⊕ Nat)), ([] : List Name)))
    fun (out, run) c => if isToolchain env c then (out, run ++ [c]) else (out ++ flush run ++ [.inl c], [])
  out ++ flush run

/-- A path as lines: the source, then each constant it reaches, with the module that declares it;
long runs inside the toolchain are counted, not listed (`shownHops`). -/
def renderPath (env : Environment) {a b : Name} (path : DepPath a b) : MessageData :=
  let hop : Name ⊕ Nat → MessageData
    | .inl c => m!"{c}  ({declaringModule env c})"
    | .inr k => m!"⋯ {k} more toolchain constants"
  match shownHops env (a :: path.edges.map (·.2)) with
  | [] => m!""
  | first :: rest => MessageData.joinSep (hop first :: rest.map fun h => m!"→ " ++ hop h) Format.line

/-- The planned goals and the axioms outside the ceiling that `a` reaches, under the walk's policy;
`none` when the axiom walk ran out of its budget. -/
def reachedLeaves (env : Environment) (a : Name) : Option (Array Name) :=
  match ((reachedWithGoals env a).run {}).1 with
  | none => none
  | some (axioms, goals) => some (goals ++ disallowedAxioms axioms)

/-- `#why A B`: a checked shortest path from `A` to `B`. `#why A`: one for each planned goal and
each axiom outside `[propext, Quot.sound]` that `A` reaches. -/
syntax (name := why) "#why " ident (ppSpace ident)? : command

@[command_elab why] def elabWhy : CommandElab := fun stx => do
  let report ← liftTermElabM do
    let env ← getEnv
    let a ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let targets ← match stx[2].getOptional? with
      | some b => pure #[← realizeGlobalConstNoOverloadWithInfo b]
      | none =>
        if isGoal env a then throwError "#why: {a} is a planned goal"
        match reachedLeaves env a with
        | none => throwError "#why: the axiom walk from {a} ran out of its budget"
        | some leaves => pure leaves
    if targets.isEmpty then
      return m!"{a} rests on no planned goal and reaches no axiom outside [propext, Quot.sound]"
    let mut out : Array MessageData := #[]
    for b in targets do
      match whyPath env a b with
      | .error e => throwError "#why: {e}"
      | .ok path => out := out.push m!"{b}, {path.edges.length} step(s):{indentD (renderPath env path)}"
    return MessageData.joinSep out.toList (Format.line ++ Format.line)
  logInfo report

/-! ## The causes of an audit's refusal -/

/-- The offenders that no other offender stands under: those whose content names no other
offender. Each reaches its axiom through constants outside the offending set. -/
def offenderRoots (env : Environment) (offenders : Array Name) : Array Name :=
  let set : Std.HashSet Name := Std.HashSet.ofArray offenders
  offenders.filter fun o => match env.find? o with
    | some ci => !(usedConstantsOf ci).any fun d => d != o && set.contains d
    | none => true

/-- The causes of a refusal: each root offender with a checked path to the first axiom of
`outside` it reaches, at most `limit` of them. -/
def auditCauses (env : Environment) (offenders : Array (Name × Array Name)) (limit : Nat := 8) :
    MessageData := Id.run do
  let roots := offenderRoots env (offenders.map (·.1))
  let mut lines : Array MessageData := #[]
  for root in roots.toList.take limit do
    let some (_, outside) := offenders.find? (·.1 == root) | continue
    let some axiomName := outside[0]? | continue
    match whyPath env root axiomName with
    | .ok path => lines := lines.push (renderPath env path)
    | .error e => lines := lines.push m!"{root}: {e}"
  let more := if roots.size > limit then m!" (the first {limit} shown)" else m!""
  let verb := if roots.size == 1 then "stands" else "stand"
  return m!"{roots.size} of them {verb} under no other{more}; each one's path to its axiom:" ++
    indentD (MessageData.joinSep lines.toList Format.line)

/-! ## What a goal blocks -/

/-- What each planned goal blocks: the ids of the claims and of the requirements whose nodes rest
on it, and the count of claim witnesses this environment does not hold. One axiom memo serves
every walk, so the table costs one walk per node, not one per goal. -/
structure GoalTable where
  claims : Std.HashMap Name (Array String) := {}
  requirements : Std.HashMap Name (Array String) := {}
  missing : Nat := 0

/-- The table over a registry's claims and requirements. A node rests on the goals its walk
reaches with goals as leaves (`reachedWithGoals`), and a goal named as a node rests on itself. -/
def goalTable (env : Environment) (claims : List Claim) (requirements : List Requirement) :
    GoalTable := Id.run do
  let mut memo : AxiomMemo := {}
  let mut goalsOf : Std.HashMap Name (Array Name) := {}
  let mut names : Array Name := #[]
  for c in claims do
    if let .witness n := c.pointer then names := names.push n
  for r in requirements do names := names ++ r.top.toArray
  for n in names do
    if goalsOf.contains n || (env.find? n).isNone then continue
    let (reached, memo') := (reachedWithGoals env n).run memo
    memo := memo'
    let own := if isGoal env n then #[n] else #[]
    goalsOf := goalsOf.insert n (own ++ ((reached.map (·.2)).getD #[]))
  let push (m : Std.HashMap Name (Array String)) (g : Name) (id : String) :=
    let ids := m.getD g #[]
    if ids.contains id then m else m.insert g (ids.push id)
  let mut table : GoalTable := {}
  for c in claims do
    if let .witness n := c.pointer then
      if (env.find? n).isNone then table := { table with missing := table.missing + 1 }
      for g in goalsOf.getD n #[] do
        table := { table with claims := push table.claims g c.id }
  for r in requirements do
    for n in r.top do
      for g in goalsOf.getD n #[] do
        table := { table with requirements := push table.requirements g r.id }
  return table

/-- `#goal_impact G`: the registry's claims and requirements whose nodes rest on the planned goal
`G`. `#goal_impact`: every planned goal of the registry's plan scope, ranked by what it blocks,
the most first: the planning view of which goal to prove next. Both read this environment; a
claim whose witness it does not hold is counted apart, never as unblocked. -/
syntax (name := goalImpact) "#goal_impact" (ppSpace ident)? : command

@[command_elab goalImpact] def elabGoalImpact : CommandElab := fun stx => do
  let report ← liftTermElabM do
    let env ← getEnv
    let table := goalTable env registry.claims registry.requirements
    let blocks (g : Name) : MessageData :=
      let cs := table.claims.getD g #[]
      let rs := table.requirements.getD g #[]
      if cs.isEmpty && rs.isEmpty then m!"{g}: blocks no claim" else
        m!"{g}: {cs.size} claim(s) {cs.toList}, requirements {rs.toList}"
    let absent := if table.missing == 0 then m!"" else
      m!"\n{table.missing} claim witness(es) are not in this environment; import their modules to read them"
    match stx[1].getOptional? with
    | some id =>
      let g ← realizeGlobalConstNoOverloadWithInfo id
      unless isGoal env g do throwError "#goal_impact: {g} is not a planned goal"
      return blocks g ++ absent
    | none =>
      let mut goals : Array Name := #[]
      for i in [0:env.header.moduleNames.size] do
        if registry.planScope.any (·.isPrefixOf env.header.moduleNames[i]!) then
          goals := goals ++ PersistentEnvExtension.getModuleEntries goalExt env i
      let size (g : Name) := (table.claims.getD g #[]).size + (table.requirements.getD g #[]).size
      let ranked := goals.qsort fun a b =>
        size a > size b || (size a == size b && a.toString < b.toString)
      return m!"{goals.size} planned goal(s) in the plan scope {registry.planScope}, by what they \
        block:{indentD (MessageData.joinSep (ranked.toList.map blocks) Format.line)}" ++ absent
  logInfo report

end ProofGraph
