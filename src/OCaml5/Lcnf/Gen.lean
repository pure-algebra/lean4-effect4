import Lean
import OCaml5.Lcnf.Index
import OCaml5.Lcnf.Census
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Export
import OCaml5.Lcnf.Public
import OCaml5.Lcnf.Identity

/-!
# OCaml5.Lcnf.Gen

**What it is.** One LCNF artifact made from its command's arguments: the closure translated
(`translateClosureInferring`), the types generated (`generate`), the declarations emitted, the
module checked (`Ml.checkModule`, `hygieneProblems`, the extern ledger), rendered and written, with
its closure manifest. The recipe (`ocaml/gen/roots.json`) lists the artifacts, the plan checker
(`OCaml5.Lcnf.Export`) admits its export classes, and `argvOf` turns each entry into the command its
header carries. The driver `OCaml5.Tools.LcnfGen` runs one artifact, or every artifact of the recipe
in one process.

An artifact may serve several consumers (`--consumer`, the recipe's `consumers`): its closure is
one walk of every consumer's roots, one phase per consumer in the recipe's order, and each
consumer gets a facade, a unit of its own that includes the artifact
(`include Lanes_gen`) and whose inferred interface keeps that consumer's roots and the types they
name.

**Scopes (D1).** With `--closure`, the walk's own nodes (those the artifact's own roots reach,
the walk's first phase) are compiled once, in the closure unit, and `--out` is a facade over it
(`include Closure_gen`) whose interface keeps the artifact's public and linkage roots and seals
its packages. With `--tests`, the nodes only the consumers' roots reach are compiled in a second
unit that includes the closure, and the consumers' facades include that unit. One walk names
every type once: the closure's types first, as the artifact alone names them, then the tests
unit's types, which take no name of the closure's. So each declaration is lowered and compiled
once. The test lanes are the consumers of the api artifact: the closure is
`ocaml/gen/closure_gen.ml`, a package-private library of `effect4_gen`, and the tests unit is
`ocaml/engine/test/lanes/lanes_gen.ml`, which nothing installs.

**Depends on.** `OCaml5.Lcnf.Translate`, `OCaml5.Lcnf.Types`, `OCaml5.Lcnf.Externs`, `OCaml5.Ml`,
`OCaml5.Lcnf.Index` and `OCaml5.Lcnf.Census` (the mono index and the construct census of the manifest),
`OCaml5.Lcnf.Export` (the typed recipe and its plan checker), `OCaml5.Lcnf.Public` (the public
names' manifest and the facade), `OCaml5.Lcnf.Identity` (the manifest's identity line).

**Properties.**
* **The header is the command.** An artifact's header carries the command that makes it alone
  (`commandOf`), whether the run made it alone or with the recipe's others. The recipe's argv
  order is fixed (`argvOf`), so the two runs write the same bytes — *by construction*; *tested*
  by `make gen-lcnf`, which runs the recipe and refuses no byte.
* **A run that fails writes nothing.** Every refusal (the frontier, a missing declaration, a
  translation or clock refusal, a type-name collision, a module diagnostic, a capture, a stale
  extern row) is raised before the artifact or its manifest is written — *by construction*.
* **Each artifact starts from the imported environment.** A recipe run imports each set of
  modules once and gives each artifact a fresh `MetaM` state over it, as a run of its own
  would — *by construction*.
* **The interface follows the classes.** An artifact's interface exports its `public` and `linkage`
  roots and hides its `internal` and `coverage` roots (`Export.ExportClass.exported`); a recipe whose
  classes contradict each other makes no artifact (`Export.readChecked`) — *by construction*;
  *tested* by `make check-ocaml`, whose hand code compiles only through the exported roots.
* **The public face is append-only.** The artifact that holds the public roots (`--facade`) also
  writes the manifest of every public name and the facade over it. A manifest that moves or drops
  a committed path at one version refuses the run before anything is written
  (`Public.breaches`) — *tested* (`OCaml5.Lcnf.Public`'s controls).
* **Consumers share one closure.** A declaration that two consumers reach is translated once, in
  the earlier consumer's phase, and the manifest's `consumers` column names every consumer whose
  roots reach it; the manifest's first line states the unit's identity
  (`Identity.identityLine`) — *by construction*. Each consumer's facade includes the artifact and
  exports that consumer's roots alone — *tested* by the lanes' dune tests and by
  `Ml.checkModule` on the facade.
* **Each node is compiled once (scopes).** With `--closure` and `--tests`, the closure unit
  emits the walk's first phase and the tests unit the later phases, so no declaration is emitted
  twice; a name both units would bind is refused, since the tests unit includes the closure; the
  tests unit declares no type the closure declares, and a type the closure holds as a placeholder
  that a tests node constructs or destructs is refused; the manifest's `unit` column names where
  each declaration is compiled — *by construction*; *tested* by `Ml.checkModule` on each unit,
  `ocamlopt` before publication and the install lane's red controls, which keep the closure
  unbound outside `ocaml/`.
-/

namespace OCaml5.Lcnf.Gen

open Lean

/-- One artifact's arguments, as its command spells them. -/
structure Args where
  /-- The artifact's path; a run without one is refused. -/
  out : String := ""
  types : Array Name := #[]
  cap : Nat := 60
  /-- The `public` roots: every word of the command that is no option. -/
  roots : Array Name := #[]
  /-- The `linkage` roots (`--linkage`): exported by the interface, for hand code to call. -/
  linkage : Array Name := #[]
  /-- The `internal` roots (`--internal`): translated for the artifact's own code, hidden. -/
  internal : Array Name := #[]
  /-- The `coverage` roots (`--coverage`): translated for coverage, hidden. -/
  coverage : Array Name := #[]
  /-- Whole packages made abstract by the inferred OCaml interface. -/
  abstractTypes : Array Name := #[]
  /-- Roots whose public values keep their original nominal types (`--nominal-roots`). -/
  nominalRoots : Array Name := #[]
  /-- Modules to import before looking the roots up; a run without one is refused. -/
  imports : Array Name := #[]
  /-- The `Extract Constant` table (`--externs <file>`). None means the flat, unseamed output. -/
  externs : Option String := none
  /-- Hand OCaml spliced verbatim inside the functor, after the type group (`--prelude <file>`).
  It is where a row whose Lean body applies a builtin to a carrier field lives, because only
  there can it see both the carrier parameters and the generated record types. -/
  prelude : Option String := none
  /-- An OCaml module that declares some of this artifact's types (`--open <Module>`): the
  artifact opens it and declares none of them. -/
  opens : Option String := none
  /-- The types the opened module's own artifact requests (`--open-types A,B,…`). This run
  generates them as that artifact does, so the two agree on every name. -/
  openTypes : Array Name := #[]
  /-- `--modules`: this artifact is the program types' owner, and declares each type of its
  closure as its own module (`OCaml5.Lcnf.generateInFull`, `Generated.items`). It declares types
  alone: no roots and no `--open`. -/
  modules : Bool := false
  /-- `--facade <path>`: this artifact implements the public facade, written at the path. -/
  facade : Option String := none
  /-- `--public-manifest <path>`: the committed manifest of the public names. -/
  publicManifest : Option String := none
  /-- `--public-version <n>`: the manifest's version; a larger one declares a break. -/
  publicVersion : Nat := 0
  /-- `--consumer <out> <roots>`, repeatable: a consumer's facade, written at `out`, and the
  `linkage` roots it re-exports from this artifact, comma-joined. -/
  consumers : Array (String × Array Name) := #[]
  /-- `--closure <path>`: the unit that compiles the walk's own nodes; `--out` is then a facade
  over it, whose interface keeps the artifact's exported roots and seals its packages. -/
  closure : Option String := none
  /-- `--tests <path>`: the unit that compiles the nodes only the consumers' roots reach. It
  includes the closure unit, and the consumers' facades include it. -/
  tests : Option String := none

/-- The arguments of one artifact's command. Every word that is no option is a root. -/
def Args.parse : List String → Args → Args
  | "--out" :: p :: rest, a => Args.parse rest { a with out := p }
  | "--closure" :: p :: rest, a => Args.parse rest { a with closure := some p }
  | "--tests" :: p :: rest, a => Args.parse rest { a with tests := some p }
  | "--consumer" :: p :: ns :: rest, a =>
    Args.parse rest { a with consumers := a.consumers.push (p, ((ns.splitOn ",").map String.toName).toArray) }
  | "--types" :: ts :: rest, a =>
    Args.parse rest { a with types := a.types ++ ((ts.splitOn ",").map String.toName).toArray }
  | "--coverage" :: ns :: rest, a =>
    Args.parse rest { a with coverage := a.coverage ++ ((ns.splitOn ",").map String.toName).toArray }
  | "--internal" :: ns :: rest, a =>
    Args.parse rest { a with internal := a.internal ++ ((ns.splitOn ",").map String.toName).toArray }
  | "--linkage" :: ns :: rest, a =>
    Args.parse rest { a with linkage := a.linkage ++ ((ns.splitOn ",").map String.toName).toArray }
  | "--abstract-types" :: ns :: rest, a =>
    Args.parse rest { a with abstractTypes := a.abstractTypes ++ ((ns.splitOn ",").map String.toName).toArray }
  | "--nominal-roots" :: ns :: rest, a =>
    Args.parse rest { a with nominalRoots := a.nominalRoots ++ ((ns.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => Args.parse rest { a with cap := n.toNat! }
  | "--import" :: m :: rest, a =>
    Args.parse rest { a with imports := a.imports ++ ((m.splitOn ",").map String.toName).toArray }
  | "--externs" :: p :: rest, a => Args.parse rest { a with externs := some p }
  | "--prelude" :: p :: rest, a => Args.parse rest { a with prelude := some p }
  | "--open" :: m :: rest, a => Args.parse rest { a with opens := some m }
  | "--open-types" :: ts :: rest, a =>
    Args.parse rest { a with openTypes := a.openTypes ++ ((ts.splitOn ",").map String.toName).toArray }
  | "--modules" :: rest, a => Args.parse rest { a with modules := true }
  | "--facade" :: p :: rest, a => Args.parse rest { a with facade := some p }
  | "--public-manifest" :: p :: rest, a => Args.parse rest { a with publicManifest := some p }
  | "--public-version" :: n :: rest, a => Args.parse rest { a with publicVersion := n.toNat! }
  | r :: rest, a => Args.parse rest { a with roots := a.roots.push r.toName }
  | [], a => a

/-- The roots of the artifact's consumers, each consumer's in turn, every root once. -/
def Args.consumerRoots (a : Args) : Array Name :=
  a.consumers.foldl (fun acc (_, ns) => ns.foldl (fun acc n => if acc.contains n then acc else acc.push n) acc) #[]

/-- The roots an artifact's interface exports: the `public` roots, then the `linkage` roots, then
its consumers' roots, which their facades re-export. With a tests unit (`--tests`) the consumers'
roots are that unit's, so `--out`'s interface exports the first two alone. -/
def Args.exported (a : Args) : Array Name :=
  if a.tests.isSome then a.roots ++ a.linkage
  else a.roots ++ a.linkage ++ a.consumerRoots.filter (fun n => !(a.roots ++ a.linkage).contains n)

/-- Every root of the artifact, each once: those `--out`'s interface exports, then its consumers'. -/
def Args.allRoots (a : Args) : Array Name :=
  a.exported ++ a.consumerRoots.filter (fun n => !a.exported.contains n)

/-- The artifact's own roots, in the order the closure walk starts from them: `public`, `linkage`,
`internal`, then `coverage` (`Export.ExportClass.all`). Its consumers' roots follow in phases. -/
def Args.translated (a : Args) : Array Name := a.roots ++ a.linkage ++ a.internal ++ a.coverage

/-- The walk's later phases: each consumer's roots, in the recipe's order (`collectClosure`). -/
def Args.phases (a : Args) : Array (Array Name) := a.consumers.map (·.2)

/-- Whether the artifact translates anything: own roots or a consumer's. -/
def Args.hasRoots (a : Args) : Bool := !a.translated.isEmpty || !a.consumers.isEmpty

/-- The command an artifact's header carries: the driver run on this artifact alone. -/
def commandOf (argv : List String) : String :=
  "lake exe lcnfgen " ++ " ".intercalate argv

/-- One recipe entry's argv, in the recipe's fixed order: `--out`, the scopes' units
(`--closure`, `--tests`, when the entry names them), one `--import` per module,
`--cap`, `--types` (comma-joined, when any), `--modules` (when the entry is the program types'
owner, `"modules": true`), `--externs`, `--prelude`, `--open` and `--open-types` (when the entry
opens another artifact's module), the public face (`--facade`, `--public-manifest` and
`--public-version`, for the artifact that holds the public roots), the hidden roots (`--coverage`,
`--internal`), the `--linkage` roots, one `--consumer` per consumer in the recipe's order, then the
`public` roots, each class in the order listed. The classes and each consumer's roots are the
checked plan's (`Export.CheckedPlan.ownRootsOf`, `consumerRoots`), so a contradictory recipe never
reaches a command. It is the text of the artifact's header. `typesOf` gives an artifact's requested
types by its `out`, so an `open` names the artifact once and its types are read from it. -/
def argvOf (plan : Export.CheckedPlan) (face : List String) (typesOf : String → Option (List String))
    (entry : Json) : Except String (List String) := do
  let out ← entry.getObjValAs? String "out"
  let imports := (entry.getObjValAs? (List String) "import").toOption.getD []
  let cap ← entry.getObjValAs? Nat "cap"
  let types := (entry.getObjValAs? (List String) "types").toOption.getD []
  let nominalRoots := (entry.getObjValAs? (List String) "nominal").toOption.getD []
  let abstractTypes := (entry.getObjValAs? (List String) "abstract").toOption.getD []
  let unit := Export.unitOf out
  -- the recipe's own spelling: no `«»` escape, so `Effect4.Live.open` stays as the recipe writes it
  let spell (ns : List Name) : List String := ns.map (·.toString (escape := false))
  let classOf (cls : Export.ExportClass) : List String := spell (plan.ownRootsOf unit cls)
  let consumers ← match Export.consumersOf entry with
    | .ok cs => pure (cs.map (·.1))
    | .error r => throw r.message
  let consumerArgs := consumers.flatMap fun c =>
    ["--consumer", c, ",".intercalate (spell (plan.consumerRoots unit (Export.unitOf c)))]
  let listed (option : String) (cls : Export.ExportClass) : List String :=
    if (classOf cls).isEmpty then [] else [option, ",".intercalate (classOf cls)]
  let flag (name : String) : List String :=
    match entry.getObjValAs? String name with
    | .ok value => if value.isEmpty then [] else ["--" ++ name, value]
    | .error _ => []
  let opens ← match entry.getObjVal? "open" with
    | .error _ => pure []
    | .ok spec => do
      let m ← spec.getObjValAs? String "module"
      let from_ ← spec.getObjValAs? String "artifact"
      let some ts := typesOf from_
        | throw s!"{out} opens the module of {from_}, which is no artifact of the recipe"
      pure ["--open", m, "--open-types", ",".intercalate ts]
  let modules := (entry.getObjValAs? Bool "modules").toOption.getD false
  return ["--out", out] ++ flag "closure" ++ flag "tests"
    ++ imports.flatMap (fun m => ["--import", m]) ++ ["--cap", toString cap]
    ++ (if types.isEmpty then [] else ["--types", ",".intercalate types])
    ++ (if modules then ["--modules"] else [])
    ++ (if nominalRoots.isEmpty then [] else ["--nominal-roots", ",".intercalate nominalRoots])
    ++ (if abstractTypes.isEmpty then [] else ["--abstract-types", ",".intercalate abstractTypes])
    ++ flag "externs" ++ flag "prelude" ++ opens
    ++ (if (classOf .«public»).isEmpty then [] else face)
    ++ listed "--coverage" .coverage ++ listed "--internal" .internal ++ listed "--linkage" .linkage
    ++ consumerArgs ++ classOf .«public»

/-- The recipe's artifacts, each as its argv, in the recipe's order. A recipe the plan checker
refuses (`Export.readChecked`: another format, a misspelt class, a root in two classes, a public
root in two artifacts, a failed `facade_resolves` or `public_excludes_coverage`) makes none. -/
def recipeArgvs (recipe : Json) : Except String (Array (List String)) := do
  let plan ← match Export.readChecked recipe with
    | .ok p => pure p
    | .error r => throw r.message
  -- The public facade's own client names are the public paths (`publicName`): two public roots
  -- with one path refuse the recipe by both names, and `facade_resolves` holds under that
  -- spelling (R6.1, at the public consumer).
  let names ← match publicNames (plan.plan.publicRoots.map (.value, ·)) with
    | .ok ns => pure ns
    | .error r => throw r.message
  let client (n : Name) : Name := ((names.find? (·.source == n)).map (·.asName)).getD n
  if let some n := (plan.plan.unresolvedAt plan.plan.facadeModule client).head? then
    throw (Export.PlanRefusal.unresolved plan.plan.facadeModule n).message
  let spec ← recipe.getObjVal? "facade"
  let face ← match spec.getObjValAs? String "out", spec.getObjValAs? String "manifest",
      spec.getObjValAs? Nat "version" with
    | .ok out, .ok manifest, .ok version =>
      unless Export.unitOf out == plan.plan.facadeModule do
        throw s!"the facade {out} is no module {plan.plan.facadeModule}"
      pure ["--facade", out, "--public-manifest", manifest, "--public-version", toString version]
    | _, _, _ => pure []
  let entries ← recipe.getObjValAs? (Array Json) "artifacts"
  let typesOf (out : String) : Option (List String) :=
    entries.findSome? fun e =>
      if (e.getObjValAs? String "out").toOption == some out then
        some ((e.getObjValAs? (List String) "types").toOption.getD [])
      else none
  entries.mapM (argvOf plan face typesOf)

/-- The `--out` paths of the recipe's artifacts, whose closure manifests are data in
`GENERATED_PATHS` at `ocaml/gen/closure-<stem>.tsv` (decisions row 70). -/
def recipeOutsOf (recipe : Json) : List String :=
  match recipe.getObjVal? "artifacts" with
  | .ok (.arr rows) => rows.toList.filterMap fun r => (r.getObjValAs? String "out").toOption
  | _ => []

/-- Where a run writes its closure manifest: in `ocaml/gen/` for one of the committed recipe's
artifacts (row 70, all of them in one folder, named after the artifact's stem), and beside `--out`
for any other run, a probe's recipe included, so a probe never writes into the tree (decisions
row 174 (i)). -/
def manifestPathFor (out : String) (recipeOuts : List String) : String :=
  let stem := (System.FilePath.mk out).fileStem.getD "closure"
  if recipeOuts.contains out then s!"ocaml/gen/closure-{stem}.tsv"
  else ((System.FilePath.mk out).parent.getD "." / s!"closure-{stem}.tsv").toString

/-- Each translated declaration's consumers: every consumer one of whose roots reaches it in the
translated graph, in the order of `groups`. The graph's edges are `Translated.callees` read
through `globalName` and the extern dependencies, as `emissionGroups` reads them. A group is a
consumer and the roots it sees: the artifact's interface (its exported roots), the public facade
(its public roots) and each consumer's facade (its own roots). An `internal` or `coverage` root
belongs to no group, so a declaration only such a root reaches has no consumer. -/
def reachedBy (ds : Array Translated) (groups : List (String × Array Name)) :
    Array (List String) := Id.run do
  let byName : Std.HashMap String Nat :=
    (ds.foldl (fun (m, i) t => (m.insert t.ocamlName i, i + 1)) (({} : Std.HashMap String Nat), 0)).1
  let adj : Array (Array Nat) := ds.map fun t =>
    (t.callees.filterMap fun c => byName[globalName c]?) ++ t.externDeps.filterMap fun n => byName[n]?
  let mut out : Array (List String) := ds.map fun _ => []
  for (consumer, roots) in groups do
    let mut queue : Array Nat := roots.filterMap fun r => ds.findIdx? (·.userName == r)
    let mut seen : Std.HashSet Nat := {}
    let mut k := 0
    while k < queue.size do
      let i := queue.getD k 0
      k := k + 1
      if seen.contains i then continue
      seen := seen.insert i
      queue := queue ++ adj.getD i #[]
    for i in seen do
      out := out.modify i fun cs => if cs.contains consumer then cs else cs ++ [consumer]
  return out

/-- One row of the closure manifest: the Lean constant, the OCaml name it became, whether the
emitted binding is recursive, the twenty-six mono-LCNF construct counts of its body
(`constructs`, in that order), `DeclHash`'s hash of the whole `Decl` (the identity of the *code*,
stable across runs of one build), its user-facing name, whether it is a root of the artifact
(`roots`: a `public`, `linkage` or consumer's root), the consumers that reach it (`reachedBy`),
comma-joined, and the unit that compiles it (the closure unit, or the tests unit for a node only
the consumers reach). The manifest's first line states what every row of the walk shares
(`Identity.identityLine`): the type owner, the target profile and the catalogue.

The mono declaration is read the way `translateClosure` reads it, out of `monoExt`'s module
entries (`persistedMonoIndex`), never through `getMonoDecl?`: the module system's
export filter makes the two disagree (`tools/Conform/Lcnf/Validity.lean`, the section on reading
`monoExt`'s local state). A declaration the closure translated and the index cannot find is
fatal, not a blank row. -/
private def manifestRow (env : Environment) (mono : MonoIndex)
    (roots : Array Name) (t : Translated) (consumers : List String) (unit : String) :
    MetaM String := do
  let some d := mono.findIn? env t.leanName
    | throwError s!"closure manifest: no mono declaration for {t.leanName}"
  let census := Census.ofDecl {} d
  return "\t".intercalate
    ([toString t.leanName, t.ocamlName, toString t.recursive]
      ++ constructs.map (fun k => toString (census.get k))
      ++ [toString (hash d), toString t.userName, toString (roots.contains t.userName),
          ",".intercalate consumers, unit])

/-- A public root's original type after proof and type parameters erase. Unlike mono types,
this type keeps the package names that an OCaml interface makes abstract. An unspelled binder
or result refuses the root; the generator never falls back to its erased representation. -/
private def nominalRootType (ex : Externs) (tn : TypeNames) (root : Name) :
    MetaM (Ml.Ty × Array Name) := withCurrHeartbeats do
  let info ← getConstInfo root
  Meta.forallTelescope info.type fun xs result => do
    let mut params : ParamVars := {}
    let mut domains : List Ml.Ty := []
    let mut refs : Array Name := #[]
    for x in xs do
      let domain ← Meta.inferType x
      if isTypeParameter domain then
        params := { params with vars := params.vars.insert x.fvarId! s!"a{params.vars.size}" }
      else if !(← Meta.isProp domain) then
        let (some ty, used) ← kernelTy ex tn params domain
          | throwError s!"nominal root {root}: cannot spell source parameter {← Meta.ppExpr domain}"
        domains := domains ++ [ty]
        refs := refs ++ used
    let (some resultTy, used) ← kernelTy ex tn params result
      | throwError s!"nominal root {root}: cannot spell source result {← Meta.ppExpr result}"
    return (domains.foldr Ml.Ty.arrow resultTy, refs ++ used)

/-- The requested source signatures and every type they need. -/
private def nominalRootTypes (ex : Externs) (tn : TypeNames) (roots : Array Name) :
    MetaM (Array (Name × Ml.Ty) × Array Name) := do
  let mut types : Array (Name × Ml.Ty) := #[]
  let mut refs : Array Name := #[]
  for root in roots do
    let (ty, used) ← nominalRootType ex tn root
    types := types.push (root, ty)
    refs := refs ++ used
  return (types, refs)

/-- Instantiate an alias before reading its runtime function arity. -/
private def substituteTy (vars : List (String × Ml.Ty)) : Ml.Ty → Ml.Ty
  | .var name => (vars.lookup name).getD (.var name)
  | .con name args => .con name (args.map (substituteTy vars))
  | .arrow dom cod => .arrow (substituteTy vars dom) (substituteTy vars cod)
  | .tuple parts => .tuple (parts.map (substituteTy vars))
  | .anon => .anon
  | .labelled name dom cod => .labelled name (substituteTy vars dom) (substituteTy vars cod)

/-- Read arrows through generated aliases. A bounded alias cycle refuses a root signature. -/
private def runtimeArity (types : List Ml.TypeDecl) : Nat → Ml.Ty → Except String Nat
  | 0, _ => .error "nominal root type alias expansion exhausted its bound"
  | fuel + 1, .arrow _ cod | fuel + 1, .labelled _ _ cod =>
    (· + 1) <$> runtimeArity types fuel cod
  | fuel + 1, .con name args =>
    match types.find? (·.name == name) with
    | some { params, body := .alias ty, .. } =>
      if params.length == args.length then
        runtimeArity types fuel (substituteTy (params.zip args) ty)
      else .error s!"nominal root alias {name}: parameter arity mismatch"
    | _ => .ok 0
  | _ + 1, _ => .ok 0

/-- Rebind each selected public root with its entire source type. The right-hand side reads
the preceding binding, so no argument, wrapper or cast changes its implementation. The OCaml
compiler checks the complete ascription before the producer publishes either file. -/
private def nominalRootBindings (decls : Array Translated) (types : List Ml.TypeDecl)
    (roots : Array (Name × Ml.Ty)) : MetaM (List Ml.Decl) := do
  let mut items : List Ml.Decl := []
  for (root, ty) in roots do
    let some found := decls.find? (·.userName == root)
      | throwError s!"nominal root {root}: no translated public binding"
    let sourceArity ← match runtimeArity types 128 ty with
      | .ok n => pure n
      | .error message => throwError s!"nominal root {root}: {message}"
    let resultArity ← match runtimeArity types 128 (found.bind.result.getD .anon) with
      | .ok n => pure n
      | .error message => throwError s!"nominal root {root}: {message}"
    let monoArity := found.bind.params.length + resultArity
    unless sourceArity == monoArity do
      throwError s!"nominal root {root}: source/mono arity mismatch ({sourceArity} versus {monoArity})"
    let binding : Ml.Bind := { name := found.ocamlName, result := some ty, body := .var found.ocamlName }
    items := items ++ [.letD false [binding], .blank]
  return items

/-- Milliseconds between two readings of `IO.monoNanosNow`. -/
private def millis (a b : Nat) : Nat := (b - a) / 1000000

/-- One artifact, made from its argv and written with its closure manifest; the report goes to
standard output, the last line its phases' times. `recipeOuts` places the manifest
(`manifestPathFor`). -/
def run (argv : List String) (recipeOuts : List String)
    (stage : Option System.FilePath := none) : MetaM Unit := do
  let args := Args.parse argv {}
  if args.out.isEmpty || args.imports.isEmpty then
    throwError "LcnfGen: `--out <path>` and at least one `--import <module>` are required"
  -- the scopes: the tests unit includes the closure unit and holds the consumers' nodes, and a
  -- functor (`--externs`) or the types' owner (`--modules`) keeps one unit
  if args.tests.isSome && args.closure.isNone then
    throwError "LcnfGen: `--tests` includes the closure unit, so it needs `--closure`"
  if args.tests.isSome && args.consumers.isEmpty then
    throwError "LcnfGen: `--tests` holds the nodes only consumers reach, so it needs a `--consumer`"
  if args.closure.isSome && (args.externs.isSome || args.modules) then
    throwError "LcnfGen: `--closure` splits a flat artifact; `--externs` and `--modules` keep one unit"
  for root in args.nominalRoots do
    unless args.exported.contains root do
      throwError s!"nominal root {root}: it is not an exported root (public or linkage)"
  let handEx : Externs ← match args.externs with
    | none => pure {}
    | some path => do
      match Externs.parse (← IO.FS.readFile path) with
      | .ok e => pure e
      | .error msg => throwError s!"{path}: {msg}"
  let preludeText : Option String ← match args.prelude with
    | none => pure none
    | some path => pure (some (← IO.FS.readFile path))
  let t0 ← IO.monoNanosNow
  -- Two Lean type constants can share a short name (`Effect4.Api.Outcome` and
  -- `Effect4.Machine.Outcome` are both `outcome`). Renaming one *after* the annotations and
  -- constructors are rendered makes them disagree, so the collisions are discovered on a
  -- first pass and fed back as `TypeNames` before anything is written; the loop repeats in
  -- case a fallback name collides in its turn. A renaming pass translates the declarations
  -- again (`retranslate`): the walk, the carrier rows and the clock boundary read no name.
  -- The opened module's types, generated as its own artifact generates them (no table, the same
  -- renaming loop), so every name agrees. A placeholder there would hide a type this run must
  -- declare in full, so the opened artifact must declare each of its types in full.
  let mut tn : TypeNames := {}
  let mut provided : NameSet := {}
  -- the opened unit's modules, each with the declaration it holds: what its `open` brings
  let mut openedModules : List (String × List Ml.TypeDecl) := []
  -- the opened unit's types at their owner, each with its module: the facade's program types
  let mut ownerTypes : List (Name × String × Ml.TypeDecl) := []
  if args.opens.isSome then
    let (og, otn) ← generateInFull args.openTypes
    tn := otn
    provided := (og.full ++ og.aliases).foldl (·.insert ·) {}
    openedModules := og.entries.toList.filterMap fun (n, d, _) => (otn.modules[n]?).map fun m => (m, [d])
    ownerTypes := og.entries.toList.filterMap fun (n, d, _) => (otn.modules[n]?).map fun m => (n, m, d)
  if args.modules && (args.hasRoots || args.opens.isSome) then
    throwError "LcnfGen: `--modules` declares the program types alone: no roots and no `--open`"
  -- one walk: the artifact's own roots, then each consumer's roots as a later phase
  let (closure0, ex, inferred) ←
    translateClosureInferring args.translated args.cap tn handEx args.phases
  let t1 ← IO.monoNanosNow
  let mut closure := closure0
  let (_, nominalRefs) ← nominalRootTypes ex tn args.nominalRoots
  -- The emission scopes (`--tests`): the walk's own nodes, its first phase, and the nodes only the
  -- consumers reach, its later phases. The closure's types are named as the artifact alone names
  -- them. The tests unit's types come after, with every closure type provided, so a tests type
  -- that takes a closure type's name is a collision, renamed as any other.
  let ownCount (c : Closure) : Nat := if args.tests.isSome then c.ownCount else c.decls.size
  let scopes (c : Closure) (tn : TypeNames) : MetaM (Generated × Generated) := do
    let (ownReal, ownNamed) := typesOfDecls (c.decls.extract 0 (ownCount c))
    let own ← generate (ownReal ++ args.types ++ args.abstractTypes ++ nominalRefs) ownNamed tn ex provided
    if args.tests.isNone then return (own, {})
    let (testReal, testNamed) := typesOfDecls (c.decls.extract (ownCount c) c.decls.size)
    let declared := own.entries.foldl (fun s (n, _, _) => s.insert n) provided
    return (own, ← generate testReal testNamed tn ex declared)
  let (gen0, testGen0) ← scopes closure tn
  let mut gen := gen0
  let mut testGen := testGen0
  let t2 ← IO.monoNanosNow
  let mut renamed : Array (String × Name × Name) := #[]
  for _ in [:4] do
    let collisions := gen.collisions ++ testGen.collisions
    if collisions.isEmpty then break
    renamed := renamed ++ collisions
    for (_, _, n) in collisions do tn := { tn with renamed := tn.renamed.insert n (fullTypeName n) }
    closure ← retranslate closure tn ex
    let (g, tg) ← scopes closure tn
    gen := g
    testGen := tg
  -- the owner: every type of its closure at its owner, one module each, as an opening artifact
  -- reads them (`generateInFull`)
  if args.modules then
    let (og, otn) ← generateInFull args.types
    gen := og
    tn := otn
  let t3 ← IO.monoNanosNow
  let header := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/*.lean) from the mono-phase LCNF "
    ++ "of " ++ ", ".intercalate (args.imports.toList.map toString)
    ++ ", Lean " ++ Lean.versionString ++ ". Do not edit. Regenerate with:\n   " ++ commandOf argv
  let own := closure.decls.extract 0 (ownCount closure)
  let tests := closure.decls.extract (ownCount closure) closure.decls.size
  let emitted ← match emit own with
    | .ok items => pure items
    | .error message => throwError message
  let testEmitted ← match emit tests with
    | .ok items => pure items
    | .error message => throwError message
  -- one OCaml name per node across the scopes: the tests unit includes the closure, so a name
  -- that both bound would shadow the closure's node there
  if let .error message := emissionGroups closure.decls then
    throwError s!"the closure and the tests unit: {message}"

  -- An artifact whose closure needs no type of its own (every type is the opened module's)
  -- declares no group: an empty `type` item is no OCaml. The owner declares one module per type.
  let typeItems : List Ml.Decl := if args.modules then gen.items tn else [gen.item, .blank]
  let (nominalTypes, _) ← nominalRootTypes ex tn args.nominalRoots
  let nominalBindings ← nominalRootBindings closure.decls gen.decls.toList nominalTypes
  let body : List Ml.Decl :=
    (if gen.decls.isEmpty then [] else typeItems)
      ++ (match preludeText with | none => [] | some t => [.rawD t, .blank])
      ++ emitted ++ nominalBindings
  -- Without a table the file is what it always was; with one, the type group mentions the
  -- carrier parameters, so the whole body moves inside the functor (A1 §1.5).
  -- The three warnings the generated code is allowed, measured on every artifact of the recipe:
  -- 27, a parameter a body does not read (LCNF keeps erased and unused parameters, so the
  -- arity is Lean's), and 30, a record label claimed by two of the generated record types of
  -- one group (each use is annotated with its type); 32, coverage values intentionally
  -- hidden by the inferred root-only interface. Every other warning is on, and the
  -- estate builds with warnings as errors, so a new kind fails the build where it appears.
  let opened : List Ml.Decl :=
    match args.opens with | none => [] | some m => [.openD m, .blank]
  let items : List Ml.Decl :=
    if args.externs.isNone then
      [.floatingAttrD "warning \"-27-30-32\"", .blank] ++ opened ++ body
    else
      [.floatingAttrD "warning \"-27-30-32\"", .blank] ++ opened ++
      carrierSignatures ++ [.blank, .moduleD "Make" carrierParams body]
  -- the closure unit: `--closure` when the artifact names one, else `--out` itself
  let closurePath := args.closure.getD args.out
  let stem (path : String) : String := (System.FilePath.mk path).fileStem.getD "lcnf_gen"
  let m : Ml.Module := { name := stem closurePath, header := some header, items := items }
  let closureUnit := Export.unitOf closurePath
  -- the facade over the closure (`--out`, with `--closure`) and the tests unit (`--tests`)
  let facadeHeader := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/Gen.lean): the facade over "
    ++ closureUnit ++ ", the artifact's one compiled closure. Its interface keeps the artifact's "
    ++ "public and linkage roots and seals its packages (ocaml/gen/roots.json). Do not edit. "
    ++ "Regenerate with:\n   " ++ commandOf argv
  let outModule : Option Ml.Module := args.closure.map fun _ =>
    { name := stem args.out, header := some facadeHeader, items := [.includeD closureUnit] }
  let testsHeader := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/*.lean) from the mono-phase LCNF "
    ++ "of " ++ ", ".intercalate (args.imports.toList.map toString)
    ++ ", Lean " ++ Lean.versionString ++ ": the nodes only the consumers' roots reach, over "
    ++ closureUnit ++ ", which it includes. Do not edit. Regenerate with:\n   " ++ commandOf argv
  let testsModule : Option Ml.Module := args.tests.map fun path =>
    { name := stem path, header := some testsHeader,
      items := [.floatingAttrD "warning \"-27-30-32\"", .blank] ++ opened
        ++ [.includeD closureUnit, .blank]
        ++ (if testGen.decls.isEmpty then [] else [testGen.item, .blank]) ++ testEmitted }
  let t4 ← IO.monoNanosNow
  -- The closure as DATA (tooling plan 4.1): one manifest per artifact, all of them in
  -- `ocaml/gen/`, named after the artifact's own stem, so a declaration entering or leaving the
  -- engine's closure, or a body whose shape changed, is a diff at review time. It is BUILT here
  -- and WRITTEN with the artifact, below every fatal check: a manifest beside an artifact the
  -- run never wrote would be the drift it exists to catch.
  let env ← getEnv
  let monoIndex := persistedMonoIndex env
  let manifestPath := manifestPathFor args.out recipeOuts
  let unitModule := Export.unitOf args.out
  let testsUnit := args.tests.map Export.unitOf
  let identity : Identity.UnitKey :=
    { unit := closureUnit, profile := Identity.profileOf args.externs args.prelude,
      catalogue := Identity.catalogue }
  let manifestHeader := "\t".intercalate
    (["lean", "ocaml", "recursive"] ++ constructs ++ ["declHash", "user", "root", "consumers", "unit"])
  -- who reaches each declaration: the artifact's interface, the public facade, each consumer
  let groups : List (String × Array Name) :=
    [(unitModule, args.exported)]
      ++ (match args.facade with
          | some f => [(Export.unitOf f, args.roots)]
          | none => [])
      ++ args.consumers.toList.map fun (f, ns) => (Export.unitOf f, ns)
  let reached := reachedBy closure.decls groups
  let mut manifestRows : Array String := #[]
  let mut index := 0
  for t in closure.decls, cs in reached do
    let compiledIn := if index < ownCount closure then closureUnit else testsUnit.getD closureUnit
    manifestRows := manifestRows.push (← manifestRow env monoIndex args.allRoots t cs compiledIn)
    index := index + 1
  let manifestText := String.intercalate "\n"
    (Identity.identityLine identity :: manifestHeader :: manifestRows.toList) ++ "\n"
  IO.println s!"closure: {closure.decls.size} of --cap {args.cap} \
    ({args.cap - closure.decls.size} of headroom); manifest {manifestPath}"
  let t5 ← IO.monoNanosNow
  IO.println s!"missing (no mono decl): {closure.missing}"
  IO.println s!"wrapper referenced directly: {closure.wrapperRefs}"
  IO.println s!"todos ({closure.todos.size}):"
  for t in closure.todos do IO.println s!"  {t}"
  IO.println s!"types in full: {gen.full}"
  IO.println s!"types as abbreviations: {gen.aliases}"
  IO.println s!"types as placeholders: {gen.placeholders}"
  IO.println s!"requested but not inductive: {gen.notInductive}"
  IO.println s!"field types not spelled: {gen.unknown}"
  if let some u := testsUnit then
    IO.println s!"{u}'s types in full: {testGen.full}; as abbreviations: {testGen.aliases}; \
      as placeholders: {testGen.placeholders}"
  IO.println s!"type-name collisions renamed to their full path: {renamed}"
  IO.println s!"type-name collisions left unresolved: {gen.collisions ++ testGen.collisions}"
  -- A non-empty frontier means the artifact calls a declaration the cap stopped at: the
  -- emitted file names a function it does not define, and only `ocamlc` would say so. The
  -- headroom is printed above, so raising the artifact's `cap` in `ocaml/gen/roots.json` is
  -- the repair.
  unless closure.frontier.isEmpty do
    throwError s!"closure did not close at --cap {args.cap} (fatal): {closure.frontier}"
  unless closure.missing.isEmpty do
    throwError s!"missing mono declarations (fatal): {closure.missing}"
  unless closure.problems.isEmpty do
    throwError s!"todos remaining in closure (fatal): {closure.problems}"
  unless (gen.collisions ++ testGen.collisions).isEmpty do
    throwError s!"unresolved type-name collisions (fatal): {gen.collisions ++ testGen.collisions}"
  unless (gen.unknown ++ testGen.unknown).isEmpty do
    throwError s!"unspelled field types (fatal): {gen.unknown ++ testGen.unknown}"
  -- A type the closure declares as a placeholder cannot be declared again in full by the tests
  -- unit, which includes the closure: a tests node that constructs or destructs one is refused.
  let shallow := (typesOfDecls tests).1.filter gen.placeholders.contains
  unless shallow.isEmpty do
    throwError s!"the tests unit constructs or destructs types its closure declares as \
      placeholders (fatal): {shallow}; request them in the artifact's `types`"
  -- The module's own well-formedness, FATAL (tooling plan 4.3), for every artifact. The opened
  -- unit's interface is its types, as its own artifact declares them: the `open` reads as a
  -- scope, and the value names past it are checked.
  let units : List Ml.Interface := match args.opens with
    | none => []
    | some m => [{ name := m, modules := openedModules }]
  let diags := Ml.checkModule m units
  unless diags.isEmpty do
    throwError s!"Ml.checkModule (fatal): {diags.length} diagnostic(s)\n  " ++
      "\n  ".intercalate (diags.map Ml.Diag.toLine)
  IO.println "Ml.checkModule: PASS (0 diagnostics)"
  -- The names, FATAL. `Ml.checkModule` decides that every name is bound; it cannot decide
  -- that a name is bound by the declaration the translator meant. `hygieneProblems` reads
  -- each translated declaration against the names its body leaves free.
  let captures := hygieneProblems closure.decls
  unless captures.isEmpty do
    throwError s!"name hygiene (fatal): {captures.length} problem(s)\n  " ++
      "\n  ".intercalate captures
  IO.println "name hygiene: PASS (0 problems)"
  -- G10: the extern ledger. Every row is reported; a row nothing hit is fatal, because a
  -- stale row is a claim about the generated file that the generated file does not make.
  if args.externs.isSome then
    let fnRows := ex.fns.toList
    let tyRows := ex.tys.toList
    let fieldRows := ex.fields.toList
    let elemRows := ex.elems.toList
    IO.println s!"extern rows: {fnRows.length} fn, {tyRows.length} type, \
      {fieldRows.length} field, {elemRows.length} elem"
    IO.println s!"fn rows used ({closure.usedExterns.size}):"
    for k in closure.usedExterns do
      IO.println s!"  {k} -> {(ex.fns[k]?.map (·.head)).getD "?"}"
    IO.println s!"type rows used ({gen.usedTys.size}): {gen.usedTys}"
    IO.println s!"field rows used ({gen.usedFields.size}): {gen.usedFields}"
    IO.println s!"elem rows used ({gen.usedElems.size}): {gen.usedElems}"
    IO.println s!"ops rows: {ex.ops.size}, used ({closure.usedOps.size}): {closure.usedOps}"
    IO.println s!"carg rows: {handEx.cargs.size} stated, used ({closure.usedCargs.size}): \
      {closure.usedCargs}"
    IO.println s!"carg rows inferred from the call sites ({inferred.size}):"
    for row in inferred do IO.println s!"  {row}"
    -- Every place a carrier had to be copied back into the Lean list. It is correct and it
    -- is O(depth); the list is printed so that a missing `carg` row is visible here rather
    -- than only in a bench.
    IO.println s!"carrier to_list sites ({closure.toLists.size}):"
    for t in closure.toLists do IO.println s!"  {t}"
    let mut stale : Array String := #[]
    for (n, row) in fnRows do
      unless row.optional || closure.usedExterns.contains n do stale := stale.push s!"fn {n}"
    for (n, _) in tyRows do
      unless gen.usedTys.contains n do stale := stale.push s!"type {n}"
    for (n, _) in fieldRows do
      unless gen.usedFields.contains n do stale := stale.push s!"field {n}"
    for (n, _) in elemRows do
      unless gen.usedElems.contains n do stale := stale.push s!"elem {n}"
    for (n, _) in ex.ops.toList do
      unless closure.usedOps.contains n do stale := stale.push s!"ops {n}"
    for (n, _) in handEx.cargs.toList do
      unless closure.usedCargs.contains n do stale := stale.push s!"carg {n}"
    unless stale.isEmpty do
      throwError "extern rows no declaration hit (a stale ledger): {stale}"
  -- The interface exports the public and linkage roots (`Export.ExportClass.exported`); the
  -- internal and coverage roots contribute code only.
  let mut rootNames : Array String := #[]
  for root in args.exported do
    let some translated := closure.decls.find? (·.userName == root)
      | throwError s!"exported root {root}: no translated binding"
    rootNames := rootNames.push translated.ocamlName
  -- With `--closure`, `--out`'s interface is read off the closure's typed tree (`from`), so its
  -- types are the closure's declarations, not aliases of them, and a sealed package seals.
  let interfaceData := Json.mkObj ([
    ("roots", toJson rootNames),
    ("abstract", toJson (args.abstractTypes.map (typeNameIn tn)))]
    ++ (match args.closure with | some path => [("from", Json.str path)] | none => []))
  -- The closure's own interface holds what its two scopes call: `--out`'s roots, the consumers'
  -- roots it compiles, and every node of it that a tests node names. Its types are all exported
  -- and none sealed, so the tests unit builds the records the facade seals.
  let ownNames : Std.HashSet String := own.foldl (fun s t => s.insert t.ocamlName) {}
  let mut testRefs : Array String := #[]
  for t in tests do
    for n in t.freeRefs ++ t.callees.map globalName do
      if ownNames.contains n && !testRefs.contains n then testRefs := testRefs.push n
  let mut closureRoots : Array String := rootNames
  for root in args.consumerRoots do
    if let some translated := own.find? (·.userName == root) then
      unless closureRoots.contains translated.ocamlName do
        closureRoots := closureRoots.push translated.ocamlName
  for n in testRefs do
    unless closureRoots.contains n do closureRoots := closureRoots.push n
  let closureData := Json.mkObj [("roots", toJson closureRoots), ("abstract", toJson ([] : List String))]
  let closureInterface : Ml.Interface :=
    { name := closureUnit, types := gen.decls.toList, values := closureRoots.toList }
  -- The tests unit's interface keeps every consumer's root and every type it can name.
  let mut testsRoots : Array String := #[]
  for root in args.consumerRoots do
    let some translated := closure.decls.find? (·.userName == root)
      | throwError s!"consumer root {root}: no translated binding"
    unless testsRoots.contains translated.ocamlName do testsRoots := testsRoots.push translated.ocamlName
  let testsData := Json.mkObj [("roots", toJson testsRoots), ("abstract", toJson ([] : List String))]
  -- The facade over the closure and the tests unit, each FATAL as the closure is: the facade
  -- includes the closure; the tests unit opens the program types' owner and includes the closure,
  -- so a type it declared again would be a duplicate, and each closure node it names must be one
  -- the closure exports.
  for scopeModule in outModule.toList ++ testsModule.toList do
    let diags := Ml.checkModule scopeModule (units ++ [closureInterface])
    unless diags.isEmpty do
      throwError s!"Ml.checkModule of {scopeModule.name} (fatal): {diags.length} diagnostic(s)\n  " ++
        "\n  ".intercalate (diags.map Ml.Diag.toLine)
  if let some u := testsUnit then
    IO.println s!"scopes: {own.size} declarations compiled in {closureUnit}, {tests.size} in {u}; \
      {closureUnit}'s interface exports {closureRoots.size} values, {testRefs.size} of them for \
      the nodes of {u}; Ml.checkModule: PASS"
  -- The public face (R6.2), built and checked before anything is written: the manifest of every
  -- public name, append-only against the committed one, and the facade module over it.
  let face ← match args.facade, args.publicManifest with
    | some facadePath, some manifestPath => do
      let mut values : List (Name × String) := []
      for root in args.roots do
        let some translated := closure.decls.find? (·.userName == root)
          | throwError s!"public root {root}: no translated binding"
        values := values ++ [(root, translated.ocamlName)]
      let mut sealed : List (Name × String × List String) := []
      for n in args.abstractTypes do
        let spelled := typeNameIn tn n
        let some d := gen.decls.find? (·.name == spelled)
          | throwError s!"sealed package {n}: no declaration {spelled}"
        sealed := sealed ++ [(n, spelled, d.params)]
      let inputs : Public.Inputs :=
        { unit := Export.unitOf args.out, values := values, owner := args.opens.getD "",
          ownerTypes := ownerTypes, sealed := sealed }
      let rows ← match Public.rows (← getEnv) inputs with
        | .ok rs => pure rs
        | .error e => throwError e
      let fresh := (args.publicVersion, rows.map Public.Row.line)
      let mut kept := 0
      if ← System.FilePath.pathExists manifestPath then
        let old ← match Public.parse (← IO.FS.readFile manifestPath) with
          | .ok o => pure o
          | .error e => throwError s!"{manifestPath}: {e}"
        let breaches := Public.breaches old fresh
        unless breaches.isEmpty do
          throwError s!"the public manifest is append-only (fatal): {breaches.length} breach(es)\n  " ++
            "\n  ".intercalate (breaches.map Public.Breach.message)
        kept := (old.2.filter fun o => fresh.2.contains o).length
      let facadeModule ← match Public.facadeModule (Export.unitOf facadePath) Public.facadeComment rows with
        | .ok m => pure m
        | .error e => throwError e
      let facadeDiags := Ml.checkModule facadeModule
      unless facadeDiags.isEmpty do
        throwError s!"Ml.checkModule of the facade (fatal): {facadeDiags.length} diagnostic(s)\n  " ++
          "\n  ".intercalate (facadeDiags.map Ml.Diag.toLine)
      let count (k : String) : Nat := (rows.filter (·.kind == k)).length
      IO.println s!"public face: {count "value"} values, {count "type"} program types, \
        {count "abstract"} sealed packages, {count "constructor"} constructors, {count "field"} fields; \
        manifest version {args.publicVersion}, {kept} committed rows unchanged; Ml.checkModule: PASS"
      let facadeValues := (rows.filter (·.kind == "value")).map (·.name.localName)
      pure (some (facadePath, Ml.render facadeModule, manifestPath,
        Public.render args.publicVersion rows,
        Json.mkObj [("roots", toJson facadeValues.eraseDups), ("abstract", toJson ([] : List String))]))
    | none, none => pure none
    | _, _ => throwError "LcnfGen: `--facade` and `--public-manifest` come together"
  -- Each consumer's facade (R6.1, step 3), built and checked before anything is written: a unit
  -- that includes the unit that compiles its nodes (the tests unit, else the closure), whose
  -- inferred interface keeps the consumer's roots and the types they name
  -- (`"types": "reachable"`). It is a view of the one closure, never a copy of it.
  let baseUnit := testsUnit.getD closureUnit
  let unitInterface : Ml.Interface :=
    if testsUnit.isSome then
      { name := baseUnit, types := gen.decls.toList ++ testGen.decls.toList,
        values := closureRoots.toList ++ tests.toList.map (·.ocamlName) }
    else
      { name := baseUnit, types := gen.decls.toList, values := closure.decls.toList.map (·.ocamlName) }
  let mut facades : Array (String × String × Json) := #[]
  for (facadeOut, roots) in args.consumers do
    let consumer := Export.unitOf facadeOut
    let mut names : Array String := #[]
    for root in roots do
      let some translated := closure.decls.find? (·.userName == root)
        | throwError s!"consumer {consumer}: root {root}: no translated binding"
      names := names.push translated.ocamlName
    let comment := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/Gen.lean): the facade of the consumer "
      ++ consumer ++ " over " ++ baseUnit ++ ", which compiles its nodes. Its interface "
      ++ "keeps this consumer's roots (ocaml/gen/roots.json, `consumers`) and the types they name. "
      ++ "Do not edit. Regenerate with:\n   " ++ commandOf argv
    let fm : Ml.Module := { name := consumer, header := some comment, items := [.includeD baseUnit] }
    let diags := Ml.checkModule fm [unitInterface]
    unless diags.isEmpty do
      throwError s!"Ml.checkModule of the facade {consumer} (fatal): {diags.length} diagnostic(s)\n  " ++
        "\n  ".intercalate (diags.map Ml.Diag.toLine)
    facades := facades.push (facadeOut, Ml.render fm,
      Json.mkObj [("roots", toJson names), ("abstract", toJson ([] : List String)),
                  ("types", Json.str "reachable")])
  unless args.consumers.isEmpty do
    let facadeUnits := args.consumers.map (Export.unitOf ·.1)
    let sharedCount := (reached.filter fun cs => (cs.filter facadeUnits.contains).length ≥ 2).size
    IO.println s!"consumers: {args.consumers.size} facades over {baseUnit}; \
      {sharedCount} of {closure.decls.size} declarations are reached by two consumers or more"
  let t6 ← IO.monoNanosNow
  -- The units this run writes, each with its interface data: the closure (`--out` itself when
  -- the artifact names no `--closure`), the facade over it, and the tests unit.
  let written : List (String × String × Json) :=
    (match outModule with
      | some facadeModule =>
        [(closurePath, Ml.render m, closureData), (args.out, Ml.render facadeModule, interfaceData)]
      | none => [(args.out, Ml.render m, interfaceData)])
    ++ (match args.tests, testsModule with
        | some path, some testsMod => [(path, Ml.render testsMod, testsData)]
        | _, _ => [])
  -- Staging changes destinations only. Commands and manifests retain their canonical paths.
  let destination (path : String) : System.FilePath :=
    match stage with | none => path | some directory => directory / path
  if stage.isSome && written.any (fun (path, _, _) => (System.FilePath.mk path).isAbsolute) then
    throwError "LcnfGen: a staged artifact requires a relative output path"
  for (path, text, data) in written do
    let output := destination path
    IO.FS.createDirAll (output.parent.getD ".")
    IO.FS.writeFile output text
    -- The staged producer reads this build artifact. It is never a committed interface snapshot.
    if stage.isSome then
      IO.FS.writeFile (output.toString ++ ".interface.json") (data.pretty ++ "\n")
  -- An artifact with no roots declares types only: it translates nothing, so it has no closure
  -- to record.
  if args.hasRoots then
    let manifest := destination manifestPath
    IO.FS.createDirAll (manifest.parent.getD ".")
    IO.FS.writeFile manifest manifestText
  for (facadeOut, facadeText, facadeInterface) in facades do
    let path := destination facadeOut
    IO.FS.createDirAll (path.parent.getD ".")
    IO.FS.writeFile path facadeText
    if stage.isSome then
      IO.FS.writeFile (path.toString ++ ".interface.json") (facadeInterface.pretty ++ "\n")
    IO.println s!"wrote {facadeOut}"
  if let some (facadePath, facadeText, publicPath, publicText, facadeInterface) := face then
    let facadeOut := destination facadePath
    IO.FS.createDirAll (facadeOut.parent.getD ".")
    IO.FS.writeFile facadeOut facadeText
    if stage.isSome then
      IO.FS.writeFile (facadeOut.toString ++ ".interface.json") (facadeInterface.pretty ++ "\n")
    let publicOut := destination publicPath
    IO.FS.createDirAll (publicOut.parent.getD ".")
    IO.FS.writeFile publicOut publicText
    IO.println s!"wrote {facadePath} and {publicPath}"
  let t7 ← IO.monoNanosNow
  let writtenPaths := ", ".intercalate (written.map (·.1))
  IO.println s!"wrote {writtenPaths} and {manifestPath}"
  IO.println s!"time (ms): closure {millis t0 t1}, types {millis t1 t2}, renaming {millis t2 t3}, \
    emission {millis t3 t4}, manifest {millis t4 t5}, checks {millis t5 t6}, \
    rendering {millis t6 t7}"


/-! ## Controls of the recipe's public face -/

private def recipeWith (publicRoots : String) : Json :=
  (Json.parse ("{\"format\": \"effect4-lcnf-roots-v3\", \"facade\": {\"module\": \"Effect4\", \
    \"out\": \"ocaml/gen/facade/effect4.ml\", \"manifest\": \"ocaml/gen/public-names.tsv\", \
    \"version\": 0}, \"artifacts\": [{\"out\": \"ocaml/gen/api_gen.ml\", \"import\": [\"Effect4.Api\"], \
    \"cap\": 10, \"public\": [" ++ publicRoots ++ "], \"coverage\": [\"Effect4.Machine.drive\"]}]}")).toOption.getD Json.null

-- green: the artifact that holds the public roots carries the public face in its command
#guard match recipeArgvs (recipeWith "\"Effect4.Run.Tree.ofProgram\"") with
  | .ok argvs => argvs.toList == [["--out", "ocaml/gen/api_gen.ml", "--import", "Effect4.Api", "--cap", "10",
      "--facade", "ocaml/gen/facade/effect4.ml", "--public-manifest", "ocaml/gen/public-names.tsv",
      "--public-version", "0", "--coverage", "Effect4.Machine.drive", "Effect4.Run.Tree.ofProgram"]]
  | .error _ => false
-- red (R6.2): two public roots with one public path refuse the recipe by both names, before any
-- command is made, so no manifest and no previous mapping is touched
#guard match recipeWith "\"Test.Names.aB\", \"Test.Names.a_b\"" |> recipeArgvs with
  | .error e => e == (NameRefusal.collision `Test.Names.aB `Test.Names.a_b).message
  | .ok _ => false

/-! ## Controls of the consumers (R6.1, step 3) -/

private def lanesRecipe : Json :=
  (Json.parse ("{\"format\": \"effect4-lcnf-roots-v3\", \"facade\": {\"module\": \"Effect4\"}, \
    \"artifacts\": [{\"out\": \"t/lanes_gen.ml\", \"import\": [\"Test.A\"], \"cap\": 10, \
    \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\", \"S.image\"]}, \
    {\"out\": \"t/modeled/modeled_gen.ml\", \"linkage\": [\"M.encode\", \"S.image\"]}]}]}")).toOption.getD Json.null

-- each consumer is one `--consumer` with its roots, in the recipe's order, after the artifact's
-- own classes; a root both consumers name is in both, and the argv reads back to one walk
-- whose phases are the consumers
#guard match recipeArgvs lanesRecipe with
  | .ok argvs => argvs.toList == [["--out", "t/lanes_gen.ml", "--import", "Test.A", "--cap", "10",
      "--consumer", "t/todo/todo_gen.ml", "T.serve,S.image",
      "--consumer", "t/modeled/modeled_gen.ml", "S.image,M.encode"]]
  | .error _ => false
#guard match recipeArgvs lanesRecipe with
  | .ok argvs => argvs.toList.all fun argv =>
      let a := Args.parse argv {}
      a.translated.isEmpty && a.hasRoots
        && a.phases == #[#[`T.serve, `S.image], #[`S.image, `M.encode]]
        && a.exported == #[`T.serve, `S.image, `M.encode]
  | .error _ => false

/-! ## Controls of the scopes (D1) -/

private def scopedRecipe : Json :=
  (Json.parse ("{\"format\": \"effect4-lcnf-roots-v3\", \"facade\": {\"module\": \"Effect4\"}, \
    \"artifacts\": [{\"out\": \"g/api_gen.ml\", \"closure\": \"g/closure_gen.ml\", \
    \"tests\": \"t/lanes_gen.ml\", \"import\": [\"Test.A\"], \"cap\": 10, \"linkage\": [\"A.load\"], \
    \"consumers\": [{\"out\": \"t/todo/todo_gen.ml\", \"linkage\": [\"T.serve\", \"A.load\"]}]}]}")).toOption.getD Json.null

-- the scopes' units follow `--out`; the entry's own linkage root stays its own when the consumer
-- names it too, so `--out`'s interface exports it, and the consumer's facade re-exports both
#guard match recipeArgvs scopedRecipe with
  | .ok argvs => argvs.toList == [["--out", "g/api_gen.ml", "--closure", "g/closure_gen.ml",
      "--tests", "t/lanes_gen.ml", "--import", "Test.A", "--cap", "10", "--linkage", "A.load",
      "--consumer", "t/todo/todo_gen.ml", "A.load,T.serve"]]
  | .error _ => false
#guard match recipeArgvs scopedRecipe with
  | .ok argvs => argvs.toList.all fun argv =>
      let a := Args.parse argv {}
      a.closure == some "g/closure_gen.ml" && a.tests == some "t/lanes_gen.ml"
        && a.exported == #[`A.load] && a.allRoots == #[`A.load, `T.serve]
        && a.phases == #[#[`A.load, `T.serve]]
  | .error _ => false
-- without a tests unit, `--out`'s interface exports its consumers' roots too, as before
#guard match recipeArgvs lanesRecipe with
  | .ok argvs => argvs.toList.all fun argv => (Args.parse argv {}).exported == (Args.parse argv {}).allRoots
  | .error _ => false

end OCaml5.Lcnf.Gen
