import Lean
import Lean.Util.CollectAxioms
import Effect4

/-!
# Effect4 axiom allowlist gate

This command inspects every declaration compiled from the authored `Effect4`
and `Test` sources, including definitions, instances, generated declarations
and private helper declarations. The build fails on an `unsafe` or `partial`
declaration, a declared axiom, an `@[extern]` or `@[implemented_by]` body, a
bodyless `opaque`, or any declaration that reaches an axiom outside the
library's current ceiling: propositional extensionality and quotient soundness.

The gate is intentionally exhaustive over the compiled namespace rather than
maintaining a hand-written theorem list. Until 2026-09-13 thirty-four
`*AxiomReport.lean` files under `Test/` repeated `#print axioms` for 1,697
declarations as a human-readable receipt; every one was a subset of what this
command audits, so they were retired. A receipt for one declaration is
`#print axioms` at the prompt.

## What the gate reads

The compiled environment, not the source text. Until 2026-09-19 a source pass
tokenized, then parsed, every audited file to catch a trust token inside an
`example`, which leaves no constant; the owner retired it together with the
proof-shape ceiling (deep-dive review §11). What that pass caught is a
declaration this command sees, except a `sorry` or `native_decide` inside an
`example`, which is a warning the build shows; `-DwarningAsError=true` would make
it an error once the tree's 237 warnings (unused `simp` arguments, mostly) are
cleared.

## The policy on `example`

An `example` stays an `example` when it is a sanity check — a shape that would
read the same as a comment, and that nothing cites.

A *receipt* becomes a named `theorem` where it is cited. A receipt that leaves
no constant cannot be named by an axiom report, joined by
`Test/Audit/RuntimeCoverage.lean`, or listed by a proof-graph trust
edge: it is checked once at its declaration site and then vanishes. The six
DB-06 modality receipts in `git:c407ab7:Effect4Test/Semantics/LogicContract.lean` and the
per-program receipt `git:c407ab7:Effect4/Meta/Derive.lean` emits for every `effect_program`
were `example`s and are theorems now.

## The ruling on `opaque`

`opaque f : T := body` is admitted. The kernel checks `body`, the constant
denotes it, and hiding the unfolding costs the ceiling nothing.

`opaque f : T` with no body is refused. Lean synthesises `default_or_ofNonempty%`
for the missing value (`Lean/Elab/DefView.lean`), so the constant denotes an
arbitrary inhabitant nobody chose: it is an uninterpreted symbol wearing a
definition's clothes, and every receipt stated about it is a receipt about
nothing. `AGENTS.md` already requires an authored admission for an
opaque trust boundary; this is the enforcement.

The two shapes are told apart by the synthesised value's head constant, which
is `Inhabited.default` or `Classical.ofNonempty` and nothing else.
-/

open Lean

namespace Test.Audit

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound]

private def auditImplementationAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/--
Modules whose declarations are audit *implementation* — metaprogramming that
inspects the environment — rather than semantic or test content.

`Classical.choice` is unavoidable in `MetaM`, so these modules are bound by
`auditImplementationAxioms` instead of `allowedAxioms`. The list is explicit
rather than a namespace prefix on purpose: a prefix would let any file dropped
into the audit tree silently acquire `Classical.choice`, which is the trust
boundary this gate exists to hold.

The list is checked for staleness below. A module named here that no longer
needs the exemption fails the gate, so an entry cannot outlive its reason.
-/
private def auditImplementationModules : List Name :=
  [ `Test.Audit.AxiomGate
  , `Test.Audit.RuntimeCoverage
  -- The authoring scope tactic: a tactic elaborator, meta code, no theorem in the module.
  , `Effect4.Laws.Program.Authoring.Tactic
  -- The proof census (`#auto_census`): a command elaborator that re-proves a module's
  -- theorems in a rolled-back environment and reports; meta code, no theorem in the module.
  , `Effect4.Laws.Auto.Census
  -- The traversal census (`#traversal_census`): a command elaborator that classifies every
  -- definition reading a free object (fold / generated / structural / …); meta code, no theorem.
  , `Effect4.Laws.Auto.Traversals
  -- The exhaustiveness inventory (`#exhaustive_gate`): a command elaborator that reads every
  -- match on a free object out of the matcher's own type and says which have no catch-all;
  -- meta code, no theorem in the module.
  , `Effect4.Laws.Auto.Exhaustive
  -- The named aesop banks (tooling plan 1.1): `declare_aesop_rule_sets` expands to a
  -- binder-free `initialize`, and the initializer that registers the rule set with aesop's
  -- environment extension crosses to `Classical.choice`. The module declares no theorem and
  -- states this entry's condition in its own header.
  , `Effect4.Laws.Auto.RuleSets
  -- The converter (`fold_of`): a command elaborator that adds a hand traversal's algebra, its
  -- homomorphism witness and `eq_cata` to the environment; meta code, no theorem of its own.
  , `Effect4.Program.FoldOf
  -- The position census, its totality gate and the typed-state skeleton emitter: commands over
  -- the environment and declaration constructors; meta code, no theorem in the modules.
  , `Effect4.Laws.Auto.Positions
  , `Effect4.Laws.Program.Typed.PositionGate
  , `Effect4.Laws.Program.Typed.TypedStateDecl
  , `Effect4.Laws.Auto.Frames
  , `Effect4.Laws.Auto.Obligations
  , `Effect4.Laws.Program.Typed.TypedSources
  , `Effect4.Laws.Auto.AnswerGate
  ]

/--
The modules bound by `auditImplementationAxioms` rather than `allowedAxioms`.

Seven target modules used to be listed here too, on the grounds that
non-semantic rendering must traverse Lean `String` values and Lean's character
folds carry `Classical.choice` through the proof backing UTF-8 decoding. That
was a module admission wearing an exact admission's clothes: it named 1 099
declarations to excuse the far smaller number that actually cross, and the
comment justifying it — "declares no theorem", "no semantic law" — was false of
`Effect4.Target.TypeScript.Skeleton`, which declares `emitNode_eq` and
`emitWith_eq`, the bridge saying Effect4's emitter *is* the pinned package's
emitter node for node. Those two are clean, and with the module admission gone
the gate is what says so rather than a comment.

`Skeleton.lean` has since been split (survey finding H28): the renderer and the
two call builders it needs moved to
`git:c407ab7:Effect4/Target/TypeScript/SkeletonRender.lean`, so the `String`-free IR and its
two bridge theorems are a module with *no* declaration reaching
`Classical.choice`, and the boundary is a file boundary as well as a list of
names. The crossings kept their names, so this list did not move.

The crossings are now `choiceImplementationDeclarations` below, one exact name
each. `#effect4_print_choice_reachers` prints the list, so re-pinning it after a
target change is one command.
-/
private def choiceImplementationModules : List Name :=
  auditImplementationModules

/--
Exact crossings from no-choice syntax generation to string rendering and its
output-text receipt, one declaration per name.

Lean's standard character folds carry `Classical.choice` through the proof
backing UTF-8 decoding, so anything that traverses a Lean `String` inherits it.
That is an implementation fact about rendering, not a semantic admission: every
admission and structured-lowering declaration in the same modules stays at the
semantic/test ceiling, and this list is what says which is which. The field
receipt's statement itself uses the renderer and `String.contains`; it is not a
semantic admission theorem. `docs/research/TYPESCRIPT-TARGET-DAG.md` records this
implementation boundary.

`#effect4_print_choice_reachers` prints this list and the private one below.
Every entry is checked for staleness: a name that no longer reaches
`Classical.choice`, or no longer exists, fails the gate.
-/
private def choiceImplementationDeclarations : List Name :=
  -- The raw Schema and annotated-field generators: source text out.
  [ ``Effect4.Codegen.Schema.jsonSource
  , ``Effect4.Codegen.Schema.representationSource
  , ``Effect4.Codegen.Schema.documentSource
  , ``Effect4.Codegen.Schema.multiDocumentSource
  , ``Effect4.Codegen.Schema.source?
  , ``Effect4.Codegen.Schema.generate?
  , ``Effect4.Codegen.EffectfulField.source?
  , ``Effect4.Codegen.EffectfulField.generate?
  , ``Effect4.Codegen.EffectfulField.source_contains_directional_rows
  -- The codegen crossing to bytes (`docs/research/2026-09-04-codegen-api-design.md` §3.1):
  -- JSON text folds over `String`s for escaping, and the artefact renderer is one call to
  -- the pinned package's renderer or to it. `JsonText.number` is deliberately not here: it
  -- writes digits without traversing a `String` and stays at the ceiling.
  , ``Effect4.Codegen.JsonText.escape
  , ``Effect4.Codegen.JsonText.render
  , ``Effect4.Codegen.JsonText.renderList
  , ``Effect4.Codegen.JsonText.renderEntries
  , ``Effect4.Codegen.renderJson
  , ``Effect4.Codegen.Artefact.render
  -- The configuration algebra's `String`-side instantiations
  -- (`docs/research/2026-09-04-production-standards-spike.md` §10, finding 1): the rc.112
  -- scalar codecs (`String.toNat?`), the `_`-splitting env embedding (`String.splitOn`),
  -- and `constantCase` (`String.toUpper` over `toList`). Every theorem of the module is
  -- parametric in the name type and takes these as supplied hooks; nothing here is a law.
  , ``Effect4.Program.Config.stdScalars
  , ``Effect4.Program.Config.segOfString
  , ``Effect4.Program.Config.splitUnderscore
  , ``Effect4.Program.Config.fromEnvRecord
  , ``Effect4.Program.Config.configCase
  , ``Effect4.Program.Config.segCase
  , ``Effect4.Program.Config.Provider.constantCase
  ]

/-- Private rendering helpers are identified by exact owner and original name,
never a namespace prefix or Lean's unstable private-name counter. -/
private def choiceImplementationPrivateDeclarations : List (Name × Name) :=
  [ (`Effect4.Codegen.EffectfulField,
      `Effect4.Codegen.EffectfulField.directionalRowsPresent)
  -- The `E4-CONF-CE-006` witnesses (`constantCase` then `nested`, and the reverse) and the
  -- residual receipt's env entries, in the module and in its contract battery; each is an
  -- executable over `fromEnvRecord`, checked by `#guard`, never by a theorem.
  , (`Effect4.Program.Config, `Effect4.Program.Config.ce006Late)
  , (`Effect4.Program.Config, `Effect4.Program.Config.ce006Early)
  , (`Effect4.Program.Config, `Effect4.Program.Config.entriesOf)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.ce006Late)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.ce006Early)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.entriesOf)
  ]

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- The synthesised values Lean gives a bodyless `opaque`. -/
private def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

/-- Resolve each `(owner, original name)` exemption to the one private
declaration that carries it, and refuse anything but exactly one.

One pass over the constants, not one pass per exemption. Being private is a
rare shape, so the pairing is decided per declaration and the twelve
exemptions are matched against the handful of candidates that survive; the
array itself is walked once. Filtering the whole array once per exemption
costs `#exemptions × #constants` calls to `privateToUserName?` and
`moduleOf?`, which with twelve exemptions is minutes rather than seconds — the
difference between a gate that gets run and one that gets skipped. -/
private def resolveChoiceImplementationDeclarations
    (environment : Environment) (declarations : Array Name) : Except String (List Name) := do
  let mut candidates : List (Name × Name × Name) := []
  for declaration in declarations do
    if let some userName := privateToUserName? declaration then
      if let some owner := moduleOf? environment declaration then
        if choiceImplementationPrivateDeclarations.contains (owner, userName) then
          candidates := (owner, userName, declaration) :: candidates
  let mut resolved := choiceImplementationDeclarations
  for (owner, originalName) in choiceImplementationPrivateDeclarations do
    let owned := candidates.filterMap fun (candidateOwner, candidateName, declaration) =>
      if candidateOwner == owner && candidateName == originalName then some declaration else none
    match owned with
    | [declaration] => resolved := resolved ++ [declaration]
    | _ => throw s!"Effect4 axiom gate: private implementation exemption {owner}/{originalName} matched {owned.length} declarations; expected exactly one"
  return resolved

/-- The ancestors reachable by walking up while the parent stays in the same
module as the declaration. A definition's `match_<n>`, `proof_<n>` and private
helpers land beside it, under its own author's control, so they are judged by
it. The walk stops at the first parent that lives elsewhere. -/
private def sameModuleAncestors
    (environment : Environment) (declarationModule : Option Name) : Name → List Name
  | .anonymous => []
  | .str parent _ =>
      if moduleOf? environment parent == declarationModule then
        parent :: sameModuleAncestors environment declarationModule parent
      else []
  | .num parent _ =>
      if moduleOf? environment parent == declarationModule then
        parent :: sameModuleAncestors environment declarationModule parent
      else []

/--
The ancestors whose admission a declaration may inherit. Two shapes, and
nothing else.

* A parent in the *same module*, per `sameModuleAncestors`.
* The immediate parent of a name Lean itself *reserves* for it. An equation
  lemma is minted in whichever module first unfolds `f`, so `f.eq_def` and
  `f.eq_<n>` genuinely live somewhere else, and this is the only way admission
  crosses a module boundary.

The second clause reads `Lean.isReservedName` rather than the spelling, and
that distinction is the whole of it. Measured against this tree: a foreign
module can declare `Skeleton.render.proof_1`, `Skeleton.render.match_1` and
`Skeleton.render._spec_1` — they are ordinary names Lean reserves nothing about
— while `Skeleton.render.eq_1` and `Skeleton.render.eq_9999` are refused
outright, `is a reserved name`. A suffix-spelling test would therefore have
handed `Classical.choice` to any of the first three;
`test/fixtures/trust-gate/forged-auxiliary.lean.txt` is the fixture that says
it does not.

Without any cross-module clause the gate refuses 32 real equation lemmas:
`Skeleton.render.eq_<n>` and its siblings are minted in
`Effect4.Target.TypeScript.StructureLaws`, the module that first unfolds the
renderer. All 32 are reserved names.

`admitted` reads the module an *ancestor* lives in, so an unrestricted prefix
list would let any constant whose name happens to equal an admitted module's —
a `structure Skeleton` in namespace `Effect4.Target.TypeScript`, say — hand
`Classical.choice` to every declaration under that namespace tree-wide. Neither
clause above can reach across a module boundary for an authored name.
-/
private def admissionAncestors (environment : Environment) (declaration : Name) : List Name :=
  let sameModule :=
    sameModuleAncestors environment (moduleOf? environment declaration) declaration
  if Lean.isReservedName environment declaration then
    declaration.getPrefix :: sameModule
  else
    sameModule

/-- Strip the binders a parameterised `opaque` puts in front of its value.
`opaque f (n : Nat) : Nat` has value `fun n => default`, and the head constant
is what the ruling reads. The bound is generous; no authored signature in this
tree approaches it. -/
private def stripBinders : Nat → Expr → Expr
  | 0, value => value
  | fuel + 1, value =>
      if value.isLambda then stripBinders fuel value.bindingBody! else value

/-- Whether an `opaque` declaration's value is the one Lean synthesised for a
missing body rather than one an author wrote. See the ruling in the module
header. -/
private def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (stripBinders 64 value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  (`Effect4).isPrefixOf moduleName || (`Test).isPrefixOf moduleName

/-- Where a module's source lives: the library under `src/`, the batteries at the root (`lakefile.toml`). -/
private def modulePath (projectRoot : System.FilePath) (moduleName : Name) : System.FilePath :=
  if (`Effect4).isPrefixOf moduleName then
    (Lean.modToFilePath (projectRoot / "src") moduleName "lean").normalize
  else
    (Lean.modToFilePath projectRoot moduleName "lean").normalize

private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "lakefile.toml").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Effect4 axiom gate: could not locate the project root"
  throw <| IO.userError "Effect4 axiom gate: project-root search exceeded 64 parents"

private def auditedSources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let effect4 ← (projectRoot / "src" / "Effect4").walkDir
  let effect4 := effect4.filter fun path => path.extension == some "lean"
  -- `Test/fixtures/` holds fixtures (`scripts/test-trust-boundaries.sh`'s planted declarations,
  -- sample trees), not battery modules.
  let fixturesRoot := (projectRoot / "Test" / "fixtures").toString
  let tests ← (projectRoot / "Test").walkDir
  let tests := tests.filter fun path =>
    path.extension == some "lean" && !path.toString.startsWith fixturesRoot
  return effect4 ++ tests |>.push (projectRoot / "src" / "Effect4.lean")

/-- Follow the compiled import graph, including indirect dependencies. Each round
discovers the next frontier; the finite graph bounds the number of rounds. This
uses module metadata, so comments or quoted examples of imports are not edges. -/
private def moduleImportClosure
    (graph : Array (Name × Array Name)) (root : Name) : Array Name := Id.run do
  let mut reached := #[root]
  let mut frontier := #[root]
  for _ in [:graph.size + 1] do
    let mut next := #[]
    for name in frontier do
      if let some (_, imports) := graph.find? (fun entry => entry.1 == name) then
        for imported in imports do
          if !reached.contains imported then
            reached := reached.push imported
            next := next.push imported
    frontier := next
    if frontier.isEmpty then break
  return reached

open Lean Elab Command in
elab "#effect4_axiom_gate" : command => do
  let environment ← getEnv
  -- `lake build` hands the elaborator an absolute file name; `lake env lean Test/All.lean`
  -- hands it the relative one, whose parent walk ends at `Test` and finds no root.
  let named := System.FilePath.mk (← getFileName)
  let workingDirectory ← IO.currentDir
  let sourceFile := if named.isAbsolute then named else workingDirectory / named
  let some sourceDirectory := sourceFile.parent
    | throwError "Effect4 axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    modulePath projectRoot moduleName
  for source in sources do
    if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize then
      throwError
        "Effect4 module-closure gate: {source} is not reachable from the Test.All audit root"

  -- A Test-only import is not a library root. Every library source must belong
  -- to Effect4 or Effect4.Laws, and the application root must never reach Laws.
  for root in #[`Effect4, `Effect4.Laws] do
    unless environment.header.moduleNames.contains root do
      throwError "Effect4 library-root gate: the audit must import {root}"
  let graph := (environment.header.moduleNames.zip environment.header.moduleData).map
    fun (name, data) => (name, data.imports.map (·.module))
  let apiModules := moduleImportClosure graph `Effect4
  let lawsModules := moduleImportClosure graph `Effect4.Laws
  for moduleName in apiModules do
    if (`Effect4.Laws).isPrefixOf moduleName then
      throwError "Effect4 library-root gate: Effect4 reaches {moduleName}"
  let admissionModules := moduleImportClosure graph `Effect4.Program.Admission
  for moduleName in admissionModules do
    if (`Effect4.Codegen).isPrefixOf moduleName then
      throwError "Effect4 module-closure gate: Effect4.Program.Admission reaches {moduleName}"
  let libraryPaths := (apiModules ++ lawsModules).map (modulePath projectRoot)
  let libraryDirectory := (projectRoot / "src" / "Effect4").toString ++
    System.FilePath.pathSeparator.toString
  for source in sources do
    if source.toString.startsWith libraryDirectory then
      unless libraryPaths.contains source.normalize do
        throwError
          "Effect4 library-root gate: {source} is unreachable from Effect4 and Effect4.Laws"
  let apiCount := (apiModules.filter ((`Effect4).isPrefixOf ·)).size
  let lawsCount := (lawsModules.filter fun name =>
    (`Effect4).isPrefixOf name && !apiModules.contains name).size
  logInfo m!"Effect4 library-root gate: {apiCount} API/utility modules, {lawsCount} Laws-only modules; every library source is reachable; Effect4 never reaches Laws"

  let mut declarations : Array Name := #[]
  for (name, info) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if !isGeneratedSafeRecursor environment name then
          if info.isUnsafe then
            throwError "Effect4 trust gate: declaration {name} is unsafe"
          if info.isPartial then
            throwError "Effect4 trust gate: declaration {name} is partial"
          if let .axiomInfo _ := info then
            throwError "Effect4 trust gate: declaration {name} is an axiom; the tree declares none"
          if isExtern environment name then
            throwError "Effect4 trust gate: declaration {name} is `@[extern]`; a checked body is replaced by host code"
          if (Compiler.getImplementedBy? environment name).isSome then
            throwError "Effect4 trust gate: declaration {name} is `@[implemented_by]`; a checked body is replaced by another"
          if let .opaqueInfo opaqueInfo := info then
            if isSynthesizedOpaqueBody opaqueInfo.value then
              throwError
                "Effect4 trust gate: declaration {name} is an `opaque` with no body, so it \
                 denotes an arbitrary inhabitant rather than the value it advertises; give it \
                 a body or make the boundary an authored admission"
        declarations := declarations.push name

  let exactImplementationDeclarations ←
    match resolveChoiceImplementationDeclarations environment declarations with
    | .ok resolved => pure resolved
    | .error message => throwError "{message}"

  let admitted (declaration : Name) : Bool :=
    (moduleOf? environment declaration).any choiceImplementationModules.contains ||
      exactImplementationDeclarations.contains declaration
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    -- An auxiliary or equation lemma inherits the admission of the declaration
    -- it was generated from; see `admissionAncestors` for which parents count.
    let bound :=
      if admitted declaration || (admissionAncestors environment declaration).any admitted then
        auditImplementationAxioms
      else
        allowedAxioms
    for axiomName in axioms do
      if forbiddenAxioms.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches forbidden axiom {axiomName}"
      if !bound.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches unexpected axiom {axiomName}; allowed axioms are {bound}"

  -- The exemption list must not outlive its reason. A named implementation
  -- module that no longer reaches `Classical.choice` is a stale entry and
  -- widens the trust boundary for nothing, so it fails the gate.
  for exempted in choiceImplementationModules do
    let mut used := false
    for declaration in declarations do
      if moduleOf? environment declaration == some exempted then
        if (← collectAxioms declaration).contains ``Classical.choice then
          used := true
    if !used then
      throwError
        "Effect4 axiom gate: stale implementation exemption for {exempted}; no declaration in it reaches Classical.choice, so remove it from choiceImplementationModules"

  for exempted in exactImplementationDeclarations do
    if !(declarations.contains exempted) then
      throwError
        "Effect4 axiom gate: exact implementation exemption names missing declaration {exempted}"
    if !(← collectAxioms exempted).contains ``Classical.choice then
      throwError
        "Effect4 axiom gate: stale exact implementation exemption for {exempted}; it no longer reaches Classical.choice"

  logInfo
    m!"Effect4 module and axiom gate: checked {sources.size} modules and {declarations.size} declarations; semantic/test axioms are {allowedAxioms}; exact implementation boundary ({choiceImplementationModules.length} module(s), {exactImplementationDeclarations.length} declaration(s)) additionally allows Classical.choice"

/-!
## Re-pinning the exact choice list

`#effect4_print_choice_reachers` prints the exact declarations that reach
`Classical.choice`, in the shape `choiceImplementationDeclarations` and
`choiceImplementationPrivateDeclarations` want them.

Re-pinning the exact list after a target change is this one command rather than
manual archaeology, which is what made the blanket module admissions attractive
in the first place. Only *roots* are printed: a declaration whose admission a parent already
carries is dropped, because `admissionAncestors` admits it and an equation
lemma's name is not stable enough to pin. Anything a surviving
`choiceImplementationModules` entry already admits is dropped too, so what the
command prints is exactly the list the exact-declaration boundary still needs.

Run it from a module that imports the whole tree, i.e. beside
`#effect4_axiom_gate` in `Test.lean`.
-/

open Lean Elab Command in
elab "#effect4_print_choice_reachers" : command => do
  let environment ← getEnv
  let mut reachers : Array Name := #[]
  for (name, _) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if (← collectAxioms name).contains ``Classical.choice then
          reachers := reachers.push name
  let isReacher (name : Name) : Bool := reachers.contains name
  let roots := reachers.filter fun name =>
    !(admissionAncestors environment name).any isReacher
  let moduleAdmitted (name : Name) : Bool :=
    (moduleOf? environment name).any choiceImplementationModules.contains
  let roots := roots.filter fun name => !moduleAdmitted name
  let publicRoots := roots.filter fun name => (privateToUserName? name).isNone
  let privateRoots := roots.filter fun name => (privateToUserName? name).isSome
  let sortedPublic := publicRoots.qsort (fun a b => a.toString < b.toString)
  let sortedPrivate := privateRoots.qsort (fun a b => a.toString < b.toString)
  let publicLines := sortedPublic.toList.map fun name =>
    if (`Test).isPrefixOf name then s!"  , `{name}" else s!"  , ``{name}"
  let privateLines := sortedPrivate.toList.map fun name =>
    let owner := (moduleOf? environment name).getD Name.anonymous
    let original := (privateToUserName? name).getD name
    s!"  , (`{owner}, `{original})"
  logInfo m!"choice reachers: {reachers.size} declaration(s), {roots.size} root(s) \
    ({sortedPublic.size} public, {sortedPrivate.size} private)\n\
    -- choiceImplementationDeclarations\n{String.intercalate "\n" publicLines}\n\
    -- choiceImplementationPrivateDeclarations\n{String.intercalate "\n" privateLines}"

end Test.Audit
