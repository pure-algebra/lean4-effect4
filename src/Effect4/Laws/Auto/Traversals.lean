import Effect4.Laws.Auto.Census

/-!
# Laws.Auto.Traversals — which definitions read a free object, and how?

`#traversal_census Effect4.Program.Eff` lists every definition of the imported `Effect4.*`
modules that takes a value of the named inductive — or of any type declared mutually with it,
the *family* — and says how the definition reads that value:

- `fold`       through a declared fold (`cataFam`, `cata_eff`, `cata_ty`, …), naming the algebra;
- `generated`  by its own recursion, but in a module `tools/Effect4Gen/manifest.json` generates
               from the signature (`foldMap_*`, `view_*`, the `Canonical` encoders);
- `structural` by its own `match` or structural recursion on the family;
- `wf`         by well-founded recursion with its own `match`;
- `delegates`  it never looks inside: it hands the value to other rows of the census, named;
- `opaque`     it neither looks inside nor hands it on (it stores or returns the value).

The instrument for "every traversal is a fold or generated from the signature": the
`structural` and `wf` rows are the exemption list, and their count is the distance from the
principle. Helpers the compiler makes for an inductive (`noConfusion`, `ctorIdx`, `brecOn.go`,
a derived `decEq_n`) are not rows. `#traversal_census T under
Some.Prefix` restricts the modules scanned (default `Effect4`). Nothing is changed.
-/

open Lean Elab Meta Command

namespace Effect4.Laws.Auto

inductive TraversalKind
  | fold
  | generated
  | structural
  | wf
  | delegates
  | opaque
deriving DecidableEq, Repr, Inhabited

def TraversalKind.label : TraversalKind → String
  | .fold => "fold"
  | .generated => "generated"
  | .structural => "structural"
  | .wf => "wf"
  | .delegates => "delegates"
  | .opaque => "opaque"

structure TraversalRow where
  name : Name
  mod : Name
  line : Nat
  /-- The family member the definition takes. -/
  domain : Name
  kind : TraversalKind
  /-- The algebra(s) of a fold; the rows a delegate hands the value to. -/
  detail : String
  isInstance : Bool
deriving Inhabited

/-- The inductive and everything declared mutually with it. -/
def familyOf (root : Name) : CoreM (Array Name) := do
  match (← getEnv).find? root with
  | some (.inductInfo info) => return info.all.toArray
  | _ => throwError "#traversal_census: {root} is not an inductive type"

/-- The family member a binder of `type` ranges over, if any; abbreviations and computed
carriers (`EffSelfCarrier Op .eff`) are unfolded first. -/
def domainOf (family : Array Name) (type : Expr) : MetaM (Option Name) :=
  forallTelescopeReducing type fun xs _ => do
    for x in xs do
      let t ← whnf (← inferType x)
      if let some n := t.getAppFn.constName? then
        if family.contains n then return some n
    return none

/-- A recursor, `casesOn`, `brecOn`, `below`, … of a family member. -/
def isFamilyRecursor (env : Environment) (family : Array Name) (c : Name) : Bool :=
  family.contains c.getPrefix &&
    (isAuxRecursor env c || (env.find? c matches some (.recInfo _)) ||
      ["rec", "brecOn", "casesOn", "recOn", "below", "binductionOn"].any fun stem =>
        stem.isPrefixOf c.getString!)

/-- Whether a matcher (`foo.match_1`) among `used` destructs a family member. -/
def matchesFamily (env : Environment) (family : Array Name) (used : Array Name) : Bool :=
  used.any fun m =>
    isMatcherCore env m &&
      match env.find? m with
      | some info =>
        (info.value?.map fun v => v.getUsedConstants.any (isFamilyRecursor env family)).getD false
      | none => false

/-- The number of binders before the first explicit one: where a fold's algebra argument sits. -/
def leadingImplicits : Expr → Nat
  | .forallE _ _ body bi => if bi == .default then 0 else leadingImplicits body + 1
  | _ => 0

/-- Read the algebra an application passes to a fold. -/
def describeAlgebra (env : Environment) (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.ctorInfo _) => "inline literal"
    | _ =>
      if e.getAppNumArgs == 0 then n.toString
      else
        -- a builder such as `EffAlgebra.ofLayer layer`: name the builder and its last argument
        let last := e.getAppArgs.back!
        match last.getAppFn with
        | .const m _ => s!"{n} {m}"
        | _ => s!"{n} …"
  | .fvar _ | .bvar _ => "(an argument)"
  | .lam .. => "inline"
  | _ => "?"

/-- Every algebra passed to a fold in `foldArity` anywhere inside `e`, structurally. -/
def algebrasIn (env : Environment) (foldArity : NameMap Nat) : Expr → Array String → Array String
  | e@(.app fn arg), acc =>
    let acc :=
      match e.getAppFn with
      | .const n _ =>
        match foldArity.find? n with
        | some i =>
          let args := e.getAppArgs
          if h : i < args.size then
            let d := describeAlgebra env args[i]
            if acc.contains d then acc else acc.push d
          else acc
        | none => acc
      | _ => acc
    algebrasIn env foldArity arg (algebrasIn env foldArity fn acc)
  | .lam _ t b _, acc => algebrasIn env foldArity b (algebrasIn env foldArity t acc)
  | .forallE _ t b _, acc => algebrasIn env foldArity b (algebrasIn env foldArity t acc)
  | .letE _ t v b _, acc =>
    algebrasIn env foldArity b (algebrasIn env foldArity v (algebrasIn env foldArity t acc))
  | .mdata _ e, acc => algebrasIn env foldArity e acc
  | .proj _ _ e, acc => algebrasIn env foldArity e acc
  | _, acc => acc

/-- A helper the compiler makes for an inductive or a derived instance, not something a person
wrote: `noConfusion`, `ctorIdx`, `brecOn.go`, `decEq_3`, … -/
def isCompilerHelper (name : Name) : Bool :=
  let stems := ["noConfusion", "ctorIdx", "toCtorIdx", "ctorElim", "brecOn", "binductionOn",
    "below", "casesOn", "recOn", "decEq", "sizeOf", "ofNat", "toNat"]
  name.components.any fun c => stems.any fun stem => stem.isPrefixOf c.toString

/-- The module a constant was declared in. -/
def moduleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- The definitions (not theorems, matchers, recursors, generated details) of the modules
under `under`, with their values. -/
def definitionsUnder (env : Environment) (under : Name) : Array (Name × Name × Expr × Expr) :=
  env.constants.map₁.fold (init := #[]) fun acc name info =>
    match info with
    | .defnInfo d =>
      if name.isInternalDetail || name.isInternal || isMatcherCore env name ||
          isAuxRecursor env name || isCompilerHelper name then acc
      else
        match moduleOf env name with
        | some m => if under.isPrefixOf m then acc.push (name, m, d.type, d.value) else acc
        | none => acc
    | .opaqueInfo d =>
      if name.isInternalDetail || name.isInternal || isCompilerHelper name then acc
      else
        match moduleOf env name with
        | some m => if under.isPrefixOf m then acc.push (name, m, d.type, d.value) else acc
        | none => acc
    | _ => acc

/-- The declared folds of the family: every `cata…` definition whose type mentions a family
member, and every `cata…` definition whose value uses one of those (`cataFam` over the
carrier-computing `EffSelfCarrier`), with the position of its algebra argument. -/
def foldsOf (family : Array Name) (defs : Array (Name × Name × Expr × Expr)) : NameMap Nat := Id.run do
  let candidates := defs.filter fun (n, _, _, _) => "cata".isPrefixOf n.getString!
  let mut folds : NameMap Nat := {}
  for (n, _, type, _) in candidates do
    if type.getUsedConstants.any family.contains then
      folds := folds.insert n (leadingImplicits type)
  for (n, _, type, value) in candidates do
    if !folds.contains n && value.getUsedConstants.any folds.contains then
      folds := folds.insert n (leadingImplicits type)
  return folds

/-- The modules the generator writes, read from its manifest (`Out` paths become module names);
empty when the manifest is not where the build runs from. -/
def generatedModules (manifest : System.FilePath := "tools/Effect4Gen/manifest.json") :
    IO (Array Name) := do
  unless ← manifest.pathExists do return #[]
  let text ← IO.FS.readFile manifest
  let .ok json := Json.parse text | return #[]
  let .ok groups := json.getObjVal? "groups" | return #[]
  let .ok groups := groups.getArr? | return #[]
  let mut out := #[]
  for g in groups do
    let .ok path := g.getObjValAs? String "Out" | continue
    -- `src\Effect4\Program\Fold.lean` → `Effect4.Program.Fold`
    let parts := (path.replace "\\" "/").splitOn "/"
    let parts := parts.filter (· != "src")
    let stem := ".".intercalate parts
    let stem := if stem.endsWith ".lean" then (stem.dropEnd 5).toString else stem
    out := out.push (String.toName stem)
  return out

syntax (name := traversalCensus) "#traversal_census " ident (" under " ident)? : command

@[command_elab traversalCensus] def elabTraversalCensus : CommandElab := fun stx => do
  let root := stx[1].getId
  let scope := if stx[2].isNone then `Effect4 else stx[2][1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let defs := definitionsUnder env scope
  let folds := foldsOf family defs
  let generated ← generatedModules
  -- pass 1: which definitions take a family value (the census set)
  let mut takers : Array (Name × Name × Expr × Expr × Name) := #[]
  for (n, m, type, value) in defs do
    if folds.contains n then continue
    if let some d ← liftTermElabM (domainOf family type) then
      takers := takers.push (n, m, type, value, d)
  let census : NameSet := takers.foldl (fun s (n, _, _, _, _) => s.insert n) {}
  -- pass 2: classify
  let mut rows : Array TraversalRow := #[]
  for (n, m, _, value, d) in takers do
    let used := value.getUsedConstants
    let algebras := algebrasIn env folds value #[]
    let hands := used.filter fun c => c != n && census.contains c
    let recurses := used.any (isFamilyRecursor env family) || matchesFamily env family used
    let kind :=
      if !algebras.isEmpty then TraversalKind.fold
      else if recurses then
        if generated.contains m then .generated
        else if used.contains ``WellFounded.fix then .wf else .structural
      else if !hands.isEmpty then .delegates
      else .opaque
    let detail :=
      match kind with
      | .fold => ", ".intercalate algebras.toList ++
          (if hands.isEmpty then "" else s!"; hands to {hands.toList}")
      | .delegates => s!"→ {hands.toList}"
      | _ => if hands.isEmpty then "" else s!"hands to {hands.toList}"
    let line := (← liftCoreM (declaredAt n)).getD 0
    let inst ← liftCoreM (isInstance n)
    rows := rows.push ⟨n, m, line, d, kind, detail, inst⟩
  let sorted := rows.qsort fun a b =>
    a.kind.label < b.kind.label || (a.kind.label == b.kind.label &&
      (a.mod.toString < b.mod.toString ||
        (a.mod == b.mod && a.line < b.line)))
  let count (k : TraversalKind) := sorted.filter (·.kind == k) |>.size
  let mut report := m!"#traversal_census {root} (family {family.toList}) under {scope}: \
    {sorted.size} definitions take a family value — \
    fold {count .fold}, generated {count .generated}, structural {count .structural}, \
    wf {count .wf}, delegates {count .delegates}, opaque {count .opaque}; \
    declared folds: {folds.toList.map (·.1)}"
  for r in sorted do
    let inst := if r.isInstance then " [instance]" else ""
    report := report ++ m!"\n  {r.kind.label}\t{r.mod}:{r.line}\t{r.name}{inst}\t\
      ({r.domain.getString!})\t{r.detail}"
  logInfo report

end Effect4.Laws.Auto
