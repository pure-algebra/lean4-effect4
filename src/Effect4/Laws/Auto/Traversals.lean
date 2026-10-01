import Effect4.Laws.Auto.Census

/-!
# Laws.Auto.Traversals — which definitions read a free object, and how?

`#traversal_census Effect4.Program.Eff` lists every definition of the imported `Effect4.*`
modules that takes a value of the named inductive — or of any type declared mutually with it,
the *family* — and says how the definition reads that value:

- `fold`       through a declared fold (`cataFam`, `cata_eff`, `cata_ty`, …), naming the algebra;
- `generated`  by its own case analysis, in a module `tools/Effect4Gen/manifest.json` generates
               from the signature (`foldMap_*`, `view_*`, the `Canonical` encoders);
- `structural` by its own case analysis under structural recursion (a `brecOn`): on the family,
               or on another argument the family value is read in step with;
- `wf`         by its own case analysis under well-founded recursion (`WellFounded.fix`,
               `WellFounded.Nat.fix`);
- `one-level`  by its own case analysis with no recursion: a `match` on the value;
- `delegates`  it never looks inside: it hands the value to other rows of the census, named;
- `opaque`     it neither looks inside nor hands it on (it stores or returns the value).

A definition's *own code* is its value and the helpers the compiler made for it, followed
transitively: the matcher (`foo.match_1`), the sparse `casesOn` a `match` with a catch-all
compiles through (shared, and named after whichever definition first needed it:
`Ty.isFactor.match_1` uses `Ty.infer._sparseCasesOn_13`), the `_unary`/`_mutual` helper a
well-founded definition of two or more arguments compiles to, the `_f` functional of a structural
one. Never a definition a person wrote (handing a value to one is `delegates`), never the
family's own recursors, never a derived `sizeOf`. A private definition is a row under the name it
was written with, marked `[private]`.

The instrument for "every traversal is a fold or generated from the signature": the
`structural` and `wf` rows are the exemption list, and their count is the distance from the
principle. A `one-level` row is listed by name and not counted: a case analysis that does not
recurse is already a fold whose arms ignore the recursive results (`fold_of` reads it as one,
pairing the value in), and what a new constructor costs it is measured by the exhaustiveness
inventory (`#exhaustive_gate`) and the case-site policy. Helpers the compiler makes for an
inductive (`noConfusion`, `ctorIdx`, `brecOn.go`, a derived `decEq_n`, a match splitter) are not
rows. `#traversal_census T under Some.Prefix` restricts the modules scanned (default `Effect4`);
`#traversal_class T for a b …` prints the class of the named definitions only (the red controls
of `Test/Audit/TraversalCensus.lean`). Nothing is changed.
-/
open Lean Elab Meta Command

namespace Effect4.Laws.Auto

inductive TraversalKind
  | fold
  | generated
  | structural
  | wf
  | oneLevel
  | delegates
  | opaque
deriving DecidableEq, Repr, Inhabited

def TraversalKind.label : TraversalKind → String
  | .fold => "fold"
  | .generated => "generated"
  | .structural => "structural"
  | .wf => "wf"
  | .oneLevel => "one-level"
  | .delegates => "delegates"
  | .opaque => "opaque"

structure TraversalRow where
  /-- The name the definition was written with (a private definition's user name). -/
  name : Name
  mod : Name
  line : Nat
  /-- The family member the definition takes. -/
  domain : Name
  kind : TraversalKind
  /-- The algebra(s) of a fold; the rows a delegate hands the value to. -/
  detail : String
  isInstance : Bool
  isPrivate : Bool
  /-- `fold_of` left `<name>.eq_cata` beside it: a hand traversal with its fold. -/
  converted : Bool
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

/-- The number of binders before the first explicit one: where a fold's algebra argument sits. -/
def leadingImplicits : Expr → Nat
  | .forallE _ _ body bi => if bi == .default then 0 else leadingImplicits body + 1
  | _ => 0

/-- The name a definition was written with: a private definition's user name. -/
def writtenName (name : Name) : Name := (privateToUserName? name).getD name

/-- Read the algebra an application passes to a fold. -/
def describeAlgebra (env : Environment) (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.ctorInfo _) => "inline literal"
    | _ =>
      if e.getAppNumArgs == 0 then (writtenName n).toString
      else
        -- a builder such as `EffAlgebra.ofLayer layer`: name the builder and its last argument
        let last := e.getAppArgs.back!
        match last.getAppFn with
        | .const m _ => s!"{writtenName n} {writtenName m}"
        | _ => s!"{writtenName n} …"
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

/-- A helper the compiler makes for an inductive, a derived instance or a `match`, not something a
person wrote: `noConfusion`, `ctorIdx`, `brecOn.go`, `decEq_3`, `foo.match_1.splitter`, … -/
def isCompilerHelper (name : Name) : Bool :=
  let stems := ["noConfusion", "ctorIdx", "toCtorIdx", "ctorElim", "brecOn", "binductionOn",
    "below", "casesOn", "recOn", "decEq", "sizeOf", "ofNat", "toNat", "splitter"]
  name.components.any fun c => stems.any fun stem => stem.isPrefixOf c.toString

/-- The module a constant was declared in. -/
def moduleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Whether a person wrote the declaration: not a detail the compiler or an elaborator made
(`foo._unary`, `foo.match_1`, `foo.proof_2`, a match splitter, a recursor, `noConfusion`, …).
Judged on the name it was written with, so a private definition is authored. -/
def isAuthored (env : Environment) (name : Name) : Bool :=
  let written := writtenName name
  !(written.isInternalDetail || written.isInternal || isMatcherCore env name ||
    isAuxRecursor env name || isCompilerHelper written)

/-- The authored definitions (not theorems, matchers, recursors, generated details), private ones
included, of the modules under `under`, with their types and values. -/
def definitionsUnder (env : Environment) (under : Name) : Array (Name × Name × Expr × Expr) :=
  env.constants.map₁.fold (init := #[]) fun acc name info =>
    let body : Option (Expr × Expr) :=
      match info with
      | .defnInfo d => some (d.type, d.value)
      | .opaqueInfo d => some (d.type, d.value)
      | _ => none
    match body with
    | some (type, value) =>
      if isAuthored env name then
        match moduleOf env name with
        | some m => if under.isPrefixOf m then acc.push (name, m, type, value) else acc
        | none => acc
      else acc
    | none => acc

/-- A sparse `casesOn`: what a `match` with a catch-all compiles through. -/
def isSparseCases (c : Name) : Bool :=
  c.components.any fun s => "_sparseCasesOn".isPrefixOf s.toString

/-- A helper the compiler made for some definition, opened when reading that definition's own
code: a matcher, a `_unary`/`_mutual`/`_f` helper, a sparse `casesOn` — anything whose written name
is an internal detail — except a derived `sizeOf` (a fold the compiler wrote for the type). -/
def isMadeHelper (env : Environment) (c : Name) : Bool :=
  let written := writtenName c
  (isMatcherCore env c || written.isInternalDetail) &&
    !(written.components.any fun s => "_sizeOf".isPrefixOf s.toString)

/-- A definition's own code: every constant its value uses and every constant the compiler-made
helpers it reaches use, transitively. A sparse `casesOn` is recorded and not opened: its value is
the family's recursor at a constant motive, a case analysis and not a recursion. -/
def ownCode (env : Environment) (value : Expr) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := value.getUsedConstants.toList
  -- each constant is opened at most once; the bound is far above any definition here
  for _ in [0:1000000] do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if isMadeHelper env c && !isSparseCases c then
        match env.find? c with
        | some (.defnInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | some (.opaqueInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | _ => pure ()
  return seen

/-- What a definition's own code does to the family: a case analysis on a member (its `casesOn`,
recursor, or a sparse `casesOn` over it); structural recursion (any `brecOn`/`binductionOn`, or a
recursor used directly); well-founded recursion (`WellFounded.fix`, `WellFounded.Nat.fix`). -/
structure Reading where
  cases : Bool
  structural : Bool
  wellFounded : Bool

def readingOf (env : Environment) (family : Array Name) (code : NameSet) : Reading :=
  let cs := code.toList
  let sparseOverFamily (c : Name) : Bool :=
    isSparseCases c &&
      match env.find? c with
      | some (.defnInfo d) => d.value.getUsedConstants.any (isFamilyRecursor env family)
      | _ => false
  { cases := cs.any fun c => isFamilyRecursor env family c || sparseOverFamily c
    structural := cs.any fun c =>
      (c.components.any fun s =>
        "brecOn".isPrefixOf s.toString || "binductionOn".isPrefixOf s.toString) ||
      (env.find? c matches some (.recInfo _))
    wellFounded := cs.any fun c =>
      c == ``WellFounded.fix || c == ``WellFounded.Nat.fix || c == ``WellFounded.fixF }

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

/-- The census of one family over the modules under `scope`: the family, its declared folds and
one row per definition that takes a family value. -/
def censusRows (root scope : Name) :
    CommandElabM (Array Name × NameMap Nat × Array TraversalRow) := do
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
  -- pass 2: classify by what the definition's own code does
  let mut rows : Array TraversalRow := #[]
  for (n, m, _, value, d) in takers do
    let code := ownCode env value
    let reading := readingOf env family code
    let algebras := algebrasIn env folds value #[]
    let hands := code.toList.filter fun c => c != n && census.contains c
    let kind :=
      if !algebras.isEmpty then TraversalKind.fold
      else if reading.cases then
        if generated.contains m then .generated
        else if reading.structural then .structural
        else if reading.wellFounded then .wf
        else .oneLevel
      else if !hands.isEmpty then .delegates
      else .opaque
    -- a hand traversal with its fold beside it: `fold_of` left `<name>.eq_cata`
    let converted := env.contains (n ++ `eq_cata)
    let handNames := hands.map writtenName
    let detail :=
      match kind with
      | .fold => ", ".intercalate algebras.toList ++
          (if hands.isEmpty then "" else s!"; hands to {handNames}")
      | .delegates => s!"→ {handNames}"
      | _ =>
        let written := writtenName n
        (if converted then s!"converted: {written ++ `alg} with {written ++ `eq_cata}" else "") ++
          (if hands.isEmpty then "" else s!" hands to {handNames}")
    let line := (← liftCoreM (declaredAt n)).getD 0
    -- an instance, or a definition nested under one (a derived instance's implementation,
    -- `instReprTy.repr`): generated from the signature by a deriving handler, or a hand
    -- instance — marked, and counted apart from the hand traversals
    let inst ← liftCoreM (do pure ((← isInstance n) || (← isInstance n.getPrefix)))
    rows := rows.push ⟨writtenName n, m, line, d, kind, detail, inst, isPrivateName n, converted⟩
  return (family, folds, rows)

/-- The marks a row's name carries in a report. -/
def TraversalRow.marks (r : TraversalRow) : String :=
  (if r.isInstance then " [instance]" else "") ++ (if r.isPrivate then " [private]" else "")

syntax (name := traversalCensus) "#traversal_census " ident (" under " ident)? : command

@[command_elab traversalCensus] def elabTraversalCensus : CommandElab := fun stx => do
  let root := stx[1].getId
  let scope := if stx[2].isNone then `Effect4 else stx[2][1].getId
  let (family, folds, rows) ← censusRows root scope
  let sorted := rows.qsort fun a b =>
    a.kind.label < b.kind.label || (a.kind.label == b.kind.label &&
      (a.mod.toString < b.mod.toString ||
        (a.mod == b.mod && a.line < b.line)))
  let count (k : TraversalKind) := sorted.filter (·.kind == k) |>.size
  let besideFold (k : TraversalKind) := sorted.filter (fun r => r.kind == k && r.converted) |>.size
  let instImpl := sorted.filter (fun r => r.kind == .structural && r.isInstance) |>.size
  let privates := sorted.filter (·.isPrivate) |>.size
  let mut report := m!"#traversal_census {root} (family {family.toList}) under {scope}: \
    {sorted.size} definitions take a family value ({privates} private) — \
    fold {count .fold}, generated {count .generated}, structural {count .structural} \
    (of which {besideFold .structural} with a fold beside them, {instImpl} instance implementations), \
    wf {count .wf} (of which {besideFold .wf} with a fold beside them), \
    one-level {count .oneLevel} (of which {besideFold .oneLevel} with a fold beside them), \
    delegates {count .delegates}, opaque {count .opaque}; \
    declared folds: {folds.toList.map (·.1)}"
  for r in sorted do
    -- no trailing tab when the detail is empty, so a pinned report needs no whitespace marker
    let detail := if r.detail.isEmpty then "" else s!"\t{r.detail}"
    report := report ++ m!"\n  {r.kind.label}\t{r.mod}:{r.line}\t{r.name}{r.marks}\t\
      ({r.domain.getString!}){detail}"
  logInfo report

syntax (name := traversalClass) "#traversal_class " ident (" under " ident)? " for " ident+ :
  command

/-- The class the census gives each named definition, by the name it was written with, in the
order given; `not a row` when it takes no family value or is not an authored definition. The red
controls of the instrument are stated with it (`Test/Audit/TraversalCensus.lean`). -/
@[command_elab traversalClass] def elabTraversalClass : CommandElab := fun stx => do
  let root := stx[1].getId
  let scope := if stx[2].isNone then `Effect4 else stx[2][1].getId
  let (_, _, rows) ← censusRows root scope
  let mut lines : Array String := #[]
  for id in stx[4].getArgs do
    let n := id.getId
    match rows.find? (·.name == n) with
    | some r => lines := lines.push s!"{r.kind.label}\t{n}{r.marks}"
    | none => lines := lines.push s!"not a row\t{n}"
  logInfo m!"#traversal_class {root} under {scope}:\n{"\n".intercalate lines.toList}"

end Effect4.Laws.Auto
