import ProofGraph.Population
import ProofGraph.Goal
import ProofGraph.Audit

/-!
# `#statement_census`: duplicate theorem statements across named modules

`#statement_census M₁ M₂ …` walks every authored theorem declared in the named modules (`isAuxiliary`
and planned goals excluded), normalizes each statement after `instantiateMVars`, and groups theorems
whose normalized statements are equal. For each group of two or more, it prints one line with the
theorems' names, their declaring modules, and each theorem's number of uses across the named
modules' proof terms.

`#statement_census reducible M₁ M₂ …` is the opt-in second mode. After grouping exact normalized
matches, it compares group representatives whose conclusion head constants agree under reducible
unfolding (`Meta.withReducible` `Meta.isDefEq`). This mode finds copies whose statements differ
only by an `abbrev` or `@[reducible]` definition, such as `Path.lt` beside `Field.ltKey`.

## What the census detects and what it misses

- **Detects (default mode)**: theorems whose statements after `instantiateMVars` are syntactically
  equal once binder names, binder annotations (`default`, `implicit`, `strictImplicit`,
  `instImplicit`), `let` non-dependence flags, metadata, and universe parameter names are erased.
- **Detects (`reducible` mode)**: theorems whose conclusions share a head constant and whose
  statements are definitionally equal under reducible unfolding (`withReducible` `isDefEq`),
  including type aliases and `abbrev` wrappers.
- **Misses**:
  - a copy stated with its arguments or hypotheses in another order (for example, `∀ a b, P a b`
    beside `∀ b a, P a b`, or a commuted equality `a = b` beside `b = a`);
  - a special case stated apart from a general theorem (for example, a theorem instantiated at
    `NativeOp` beside one polymorphic in `Op`, or one direction `P → Q` beside `P ↔ Q`);
  - copies that differ by semireducible definitions (ordinary `def`s rather than `abbrev`s),
    currying (`A × B → C` beside `A → B → C`), or isomorphic carriers.
-/

namespace ProofGraph
open Lean Meta Elab Command

/-- A theorem declaration collected for the statement census. -/
structure CensusTheorem where
  name : Name
  module : Name
  levelParams : List Name
  type : Expr
  value : Expr
  deriving Inhabited

/-- Canonical universe parameters `_u.0, _u.1, …` for a theorem's `levelParams` list. -/
def canonicalLevelParams (params : List Name) : List Level :=
  (List.range params.length).map fun i => .param (.num `_u i)

/-- Erase any non-canonical universe parameter or metavariable names from a level expression. -/
def normalizeLevel : Level → Level
  | .zero => .zero
  | .succ l => .succ (normalizeLevel l)
  | .max l₁ l₂ => .max (normalizeLevel l₁) (normalizeLevel l₂)
  | .imax l₁ l₂ => .imax (normalizeLevel l₁) (normalizeLevel l₂)
  | .param (.num `_u i) => .param (.num `_u i)
  | .param _ => .param .anonymous
  | .mvar _ => .param .anonymous

/-- Erase binder names, binder annotations, metadata, and raw universe parameter names. -/
def normalizeStatement : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort u => .sort (normalizeLevel u)
  | .const name us => .const name (us.map normalizeLevel)
  | .app f a => .app (normalizeStatement f) (normalizeStatement a)
  | .lam _ t b _ => .lam .anonymous (normalizeStatement t) (normalizeStatement b) .default
  | .forallE _ t b _ => .forallE .anonymous (normalizeStatement t) (normalizeStatement b) .default
  | .letE _ t v b _ =>
    .letE .anonymous (normalizeStatement t) (normalizeStatement v) (normalizeStatement b) false
  | .lit l => .lit l
  | .mdata _ b => normalizeStatement b
  | .proj name i b => .proj name i (normalizeStatement b)

/-- Normalize a theorem's statement after `instantiateMVars` and canonicalizing `levelParams`. -/
def normalizedTheoremType (thm : CensusTheorem) : MetaM Expr := do
  let inst ← instantiateMVars thm.type
  let leveled := inst.instantiateLevelParams thm.levelParams (canonicalLevelParams thm.levelParams)
  return normalizeStatement leveled

/-- The head constant of an expression after stripping binders and unfolding reducible heads. -/
def headConstUnfolded? (env : Environment) : Nat → Expr → MetaM (Option Name)
  | 0, _ => return none
  | fuel + 1, .forallE _ _ b _ => headConstUnfolded? env (fuel + 1) b
  | fuel + 1, .lam _ _ b _ => headConstUnfolded? env (fuel + 1) b
  | fuel + 1, .letE _ _ _ b _ => headConstUnfolded? env (fuel + 1) b
  | fuel + 1, .mdata _ b => headConstUnfolded? env (fuel + 1) b
  | _, .proj typeName _ _ => return some typeName
  | fuel + 1, e => do
    match e.getAppFn with
    | .const name _ =>
      if ← isReducible name then
        match env.find? name with
        | some (.defnInfo d) =>
          match ← headConstUnfolded? env fuel d.value with
          | some inner => return some inner
          | none => return some name
        | _ => return some name
      else return some name
    | _ => return none

/-- Strip leading `forallE`, `letE` and metadata, returning the binder count and body. -/
def stripForalls : Nat → Expr → Nat × Expr
  | n, .forallE _ _ b _ => stripForalls (n + 1) b
  | n, .letE _ _ _ b _ => stripForalls n b
  | n, .mdata _ b => stripForalls n b
  | n, e => (n, e)

/-- Bucket key for reducible statement comparison: binder count, first binder type head,
conclusion head constant, and (for connectives) the unfolded head constants of the primary
arguments. -/
def reducibleBucketKey? (env : Environment) (e : Expr) :
    MetaM (Option (Nat × Option Name × Name × Option Name × Option Name)) := do
  let firstDomHead ← match e with
    | .forallE _ d _ _ => headConstUnfolded? env 32 d
    | _ => pure none
  let (arity, body) := stripForalls 0 e
  let some head ← headConstUnfolded? env 32 body | return none
  let args := body.getAppArgs
  let (arg1?, arg2?) : Option Expr × Option Expr :=
    if head == ``Eq && args.size ≥ 3 then (some args[1]!, some args[2]!)
    else if (head == ``Iff || head == ``And || head == ``Or) && args.size ≥ 2 then
      (some args[0]!, some args[1]!)
    else if head == ``Not && args.size ≥ 1 then
      (some args[0]!, none)
    else if args.size ≥ 1 then
      (some args[args.size - 1]!, none)
    else (none, none)
  let h1 ← match arg1? with
    | some s => headConstUnfolded? env 32 s
    | none => pure none
  let h2 ← match arg2? with
    | some s => headConstUnfolded? env 32 s
    | none => pure none
  return some (arity, firstDomHead, head, h1, h2)

/-- The authored theorems of `modules`, read from the imported module headers and `mainModule`. -/
def censusTheorems (env : Environment) (modules : Array Name) : Array CensusTheorem := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array CensusTheorem := #[]
  for h : i in [0:env.header.modules.size] do
    let module := env.header.modules[i].module
    if modules.contains module then
      for name in env.header.moduleData[i]!.constNames do
        if seen.contains name || Audit.moduleOf? env name != some module then continue
        seen := seen.insert name
        if isAuxiliary env name || isGoal env name then continue
        if let some (.thmInfo thm) := env.find? name then
          out := out.push
            { name, module, levelParams := thm.levelParams, type := thm.type, value := thm.value }
  if modules.contains env.mainModule then
    let localTheorems := env.constants.map₂.foldl (init := #[]) fun acc name info =>
      if seen.contains name || isAuxiliary env name || isGoal env name then acc
      else match info with
        | .thmInfo thm =>
          acc.push
            { name, module := env.mainModule, levelParams := thm.levelParams,
              type := thm.type, value := thm.value }
        | _ => acc
    for thm in localTheorems do
      seen := seen.insert thm.name
      out := out.push thm
  return out

/-- The constants used in a theorem's proof term, looking through generated auxiliaries (`_proof_1`,
matchers) so extracted subproofs still credit the theorem that uses a lemma. -/
def proofUsedConstants (env : Environment) (value : Expr) : Array Name := Id.run do
  let mut seenAux : Std.HashSet Name := {}
  let mut used : Std.HashSet Name := {}
  let mut stack : Array Name := value.getUsedConstants
  for _ in [0:4096] do
    let some c := stack.back? | break
    stack := stack.pop
    if isAuxiliary env c then
      if seenAux.contains c then continue
      seenAux := seenAux.insert c
      if let some info := env.find? c then
        if let some auxVal := info.value? (allowOpaque := true) then
          stack := stack ++ auxVal.getUsedConstants
    else
      used := used.insert c
  return used.toArray

/-- For each constant, the number of walked theorems in `theorems` whose proof terms use it. -/
def countProofUses (env : Environment) (theorems : Array CensusTheorem) : Std.HashMap Name Nat :=
  Id.run do
    let mut counts : Std.HashMap Name Nat := {}
    for thm in theorems do
      for c in proofUsedConstants env thm.value do
        counts := counts.insert c (counts.getD c 0 + 1)
    return counts

abbrev ReducibleKey := Nat × Option Name × Name × Option Name × Option Name

/-- Merge exact-statement buckets under `withReducible` `isDefEq` when their head keys agree. -/
def mergeReducibleBuckets (env : Environment)
    (buckets : Array (Expr × Array CensusTheorem)) :
    MetaM (Array (Array CensusTheorem)) := do
  let mut byHead : Std.HashMap ReducibleKey (Array (Expr × Array CensusTheorem)) := {}
  let mut headOrder : Array ReducibleKey := #[]
  let mut noHead : Array (Array CensusTheorem) := #[]
  for (rep, members) in buckets do
    match ← reducibleBucketKey? env rep with
    | some key =>
      unless byHead.contains key do headOrder := headOrder.push key
      byHead := byHead.insert key ((byHead.getD key #[]).push (rep, members))
    | none =>
      noHead := noHead.push members
  let mut merged : Array (Array CensusTheorem) := noHead
  for key in headOrder do
    let groupBuckets := byHead.getD key #[]
    if groupBuckets.size == 1 then
      merged := merged.push groupBuckets[0]!.2
    else
      let mut clusters : Array (Expr × Array CensusTheorem) := #[]
      for (rep, members) in groupBuckets do
        let mut placed := false
        for idx in [0:clusters.size] do
          let (clusterRep, clusterMembers) := clusters[idx]!
          let eq ← withoutModifyingState <| withReducible <| isDefEq rep clusterRep
          if eq then
            clusters := clusters.set! idx (clusterRep, clusterMembers ++ members)
            placed := true
            break
        unless placed do
          clusters := clusters.push (rep, members)
      for (_, members) in clusters do
        merged := merged.push members
  return merged

/-- `#statement_census M₁ M₂ …`: group theorems in the named modules whose normalized statements are
equal. `#statement_census reducible M₁ M₂ …` also merges groups whose conclusion head constants
agree and whose statements are definitionally equal under reducible unfolding (`withReducible`
`isDefEq`). -/
syntax (name := statementCensus) "#statement_census" (&" reducible")? (ppSpace ident)+ : command

@[command_elab statementCensus] def elabStatementCensus : CommandElab := fun stx => do
  let reducibleMode := !stx[1].isNone
  let modules := stx[2].getArgs.map (·.getId)
  let env ← getEnv
  for module in modules do
    unless module == env.mainModule || (env.getModuleIdx? module).isSome do
      throwError "#statement_census: the module {module} is not imported"
  let theorems := censusTheorems env modules
  let uses := countProofUses env theorems
  let groups ← liftTermElabM <| MetaM.run' do
    let mut exactMap : Std.HashMap Expr (Array CensusTheorem) := {}
    let mut exactOrder : Array Expr := #[]
    for thm in theorems do
      let norm ← normalizedTheoremType thm
      unless exactMap.contains norm do exactOrder := exactOrder.push norm
      exactMap := exactMap.insert norm ((exactMap.getD norm #[]).push thm)
    let exactBuckets := exactOrder.map fun norm => (norm, exactMap.getD norm #[])
    let rawGroups ← if reducibleMode then
        mergeReducibleBuckets env exactBuckets
      else
        pure (exactBuckets.map (·.2))
    let dupGroups := rawGroups.filterMap fun g =>
      if g.size ≥ 2 then
        some (g.qsort (·.name.toString < ·.name.toString))
      else none
    return dupGroups.qsort fun g₁ g₂ => g₁[0]!.name.toString < g₂[0]!.name.toString
  let tag := if reducibleMode then "#statement_census reducible" else "#statement_census"
  let lines : List MessageData := groups.toList.map fun g =>
    let parts := g.toList.map fun thm =>
      m!"{thm.name} ({thm.module}, {uses.getD thm.name 0} uses)"
    MessageData.joinSep parts m!", "
  if lines.isEmpty then
    logInfo m!"{tag}: {theorems.size} theorems in {modules.size} modules; 0 duplicate groups"
  else
    logInfo m!"{tag}: {theorems.size} theorems in {modules.size} modules; \
      {groups.size} duplicate groups:{indentD (MessageData.joinSep lines Format.line)}"

end ProofGraph
