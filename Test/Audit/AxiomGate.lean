import Lean
import Lean.Util.CollectAxioms
import ProofGraph.Audit
import ProofGraph.Axioms
import ProofGraph.Goal
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
`example`, which is a warning; since the owner's ruling of 2026-09-19 every library
of `lakefile.toml` builds with `-DwarningAsError=true`, so that warning fails the
build where the `example` is written.

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

open ProofGraph.Audit (moduleOf? isSynthesizedOpaqueBody moduleImportClosure)

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
  , `Effect4.Laws.Program.Typed.TypedSources
  , `Effect4.Laws.Auto.AnswerGate
  -- Semantic concept tags and their census are environment instrumentation.
  -- No semantic theorem or runtime representation is declared here.
  , `Effect4.Laws.Auto.Semantics
  -- The subset and membership decisions (`sub_tac`, `mem_tac`): a tactic elaborator and the
  -- `keys_norm` simp set's initializer; meta code, no theorem in the module (the theory it
  -- applies, `Effect4.Laws.Auto.ListSubset`, is held at the ceiling like any other).
  , `Effect4.Laws.Auto.SubsetTac
  -- The rule-bank census (`#bank_census`): a command over aesop's rule-set extension and the
  -- source text of the `rule_sets` clauses; meta code, no theorem in the module.
  , `Effect4.Laws.Auto.BankCensus
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
semantic/test ceiling, and this list is what says which is which.
`docs/research/TYPESCRIPT-TARGET-DAG.md` records this implementation boundary.

`#effect4_print_choice_reachers` prints this list and the private one below.
Every entry is checked for staleness: a name that no longer reaches
`Classical.choice`, or no longer exists, fails the gate.
-/
private def choiceImplementationDeclarations : List Name :=
  -- The raw Schema generator: source text out.
  [ ``Effect4.Codegen.Schema.jsonSource
  , ``Effect4.Codegen.Schema.representationSource
  , ``Effect4.Codegen.Schema.documentSource
  , ``Effect4.Codegen.Schema.multiDocumentSource
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
  -- The `E4-CONF-CE-006` witnesses (`constantCase` then `nested`, and the reverse) and the
  -- residual receipt's env entries, in the module and in its contract battery; each is an
  -- executable over `fromEnvRecord`, checked by `#guard`, never by a theorem.
  [ (`Effect4.Program.Config, `Effect4.Program.Config.ce006Late)
  , (`Effect4.Program.Config, `Effect4.Program.Config.ce006Early)
  , (`Effect4.Program.Config, `Effect4.Program.Config.entriesOf)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.ce006Late)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.ce006Early)
  , (`Test.Program.ConfigContract, `Test.Program.ConfigContract.entriesOf)
  ]

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

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

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  (`Effect4).isPrefixOf moduleName || (`Test).isPrefixOf moduleName

/-- Where a module's source lives: the library under `src/`, the batteries at the root (`lakefile.toml`). -/
private def modulePath (projectRoot : System.FilePath) (moduleName : Name) : System.FilePath :=
  if (`Effect4).isPrefixOf moduleName then
    (Lean.modToFilePath (projectRoot / "src") moduleName "lean").normalize
  else
    (Lean.modToFilePath projectRoot moduleName "lean").normalize

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "lakefile.toml").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Effect4 axiom gate: could not locate the project root"
  throw <| IO.userError "Effect4 axiom gate: project-root search exceeded 64 parents"

/-- The slow lane (owner, 2026-10-02): the batteries out of the default build, each minutes where
a contract takes seconds. `Test/Slow.lean` imports exactly these with `Test.All` and runs this
gate over them at a sweep (`make check-slow`), where they must be reached like every other source;
from `Test.All` they are admitted unreachable. -/
private def slowLane : List String :=
  ["Test/Slow.lean", "Test/Program/ExitTypeLane.lean", "Test/Api/TraceOrigin.lean",
    "Test/Api/SupervisionContract.lean", "Test/Machine/StepInvRulesRed.lean",
    "Test/Audit/ExhaustiveFixture.lean", "Test/Audit/TraversalFixture.lean",
    "Test/Audit/TraversalCensus.lean", "Test/Program/LayerSharingCertificate.lean"]

private def auditedSources (projectRoot : System.FilePath) (slowRoot : Bool) :
    IO (Array System.FilePath) := do
  let effect4 ← (projectRoot / "src" / "Effect4").walkDir
  let effect4 := effect4.filter fun path => path.extension == some "lean"
  -- `Test/fixtures/` holds fixtures (`scripts/test-trust-boundaries.sh`'s planted declarations,
  -- sample trees), not battery modules.
  let fixturesRoot := (projectRoot / "Test" / "fixtures").toString
  let slow : List System.FilePath :=
    if slowRoot then [] else slowLane.map fun (rel : String) => (projectRoot / rel).normalize
  let tests ← (projectRoot / "Test").walkDir
  let tests := tests.filter fun path =>
    path.extension == some "lean" && !path.toString.startsWith fixturesRoot &&
      !slow.contains path.normalize
  return effect4 ++ tests |>.push (projectRoot / "src" / "Effect4.lean")

/--
The `initialize`d handles admitted by exact name (decisions row 184; ruled 2026-10-01, ratified by
the owner). `initialize x : T ← action` compiles to `opaque x : T` with the
synthesised value and an `[init]` initializer that sets the run-time value: the handle is a
registration object (an attribute's environment extension), never a value a theorem is stated
about, so the ruling on `opaque` above does not reach it. Admitted only while the declaration
exists, is such an opaque, and carries its initializer; an entry that is none of these fails the
gate as stale. A binder-free `initialize` (the aesop banks, `Laws/Auto/RuleSets.lean`) declares
no opaque and needs no entry.
-/
private def admittedInitializedHandles : List Name :=
  [`Effect4.Laws.Auto.semanticsAttribute]

open Lean Elab Command in
elab "#effect4_axiom_gate" : command => do
  let environment ← getEnv
  -- A `module` root imports the exported part of each module: its theorems arrive as axioms and
  -- its private declarations not at all, so the walk below would refuse every theorem or audit
  -- less. Only a non-module root sees every kernel constant (decisions row 200).
  if environment.header.isModule then
    throwError "Effect4 axiom gate: the audit root is a `module`; it sees imported theorems as axioms and no private declaration, so the gate runs only in a non-module root"
  let t0 ← liftIO IO.monoMsNow
  -- `lake build` hands the elaborator an absolute file name; `lake env lean Test/All.lean`
  -- hands it the relative one, whose parent walk ends at `Test` and finds no root.
  let named := System.FilePath.mk (← getFileName)
  let workingDirectory ← IO.currentDir
  let sourceFile := if named.isAbsolute then named else workingDirectory / named
  let some sourceDirectory := sourceFile.parent
    | throwError "Effect4 axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let slowRoot := sourceFile.normalize == (projectRoot / "Test" / "Slow.lean").normalize
  let sources ← liftIO <| auditedSources projectRoot slowRoot
  let importedPaths : Std.HashSet String := environment.header.moduleNames.foldl
    (fun set moduleName => set.insert (modulePath projectRoot moduleName).toString) {}
  for source in sources do
    if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize.toString then
      throwError
        "Effect4 module-closure gate: {source} is not reachable from the Test.All audit root"

  let t1 ← liftIO IO.monoMsNow

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
  let libraryPaths : Std.HashSet String := (apiModules ++ lawsModules).foldl
    (fun set moduleName => set.insert (modulePath projectRoot moduleName).toString) {}
  let libraryDirectory := (projectRoot / "src" / "Effect4").toString ++
    System.FilePath.pathSeparator.toString
  for source in sources do
    if source.toString.startsWith libraryDirectory then
      unless libraryPaths.contains source.normalize.toString do
        throwError
          "Effect4 library-root gate: {source} is unreachable from Effect4 and Effect4.Laws"
  let apiCount := (apiModules.filter ((`Effect4).isPrefixOf ·)).size
  let lawsCount := (lawsModules.filter fun name =>
    (`Effect4).isPrefixOf name && !apiModules.contains name).size
  logInfo m!"Effect4 library-root gate: {apiCount} API/utility modules, {lawsCount} Laws-only modules; every library source is reachable; Effect4 never reaches Laws"

  let t2 ← liftIO IO.monoMsNow
  -- one native fold over the constants: every audited declaration's facts, and the same
  -- declarations by module for the exemption checks below
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts environment belongsToAuditedTree
  unless missing.isEmpty do
    throwError "Effect4 trust gate: modules list declarations the environment does not hold: {missing}"
  for fact in facts do
    let name := fact.name
    if !fact.safeRecursor then
      if fact.isUnsafe then
        throwError "Effect4 trust gate: declaration {name} is unsafe"
      if fact.isPartial then
        throwError "Effect4 trust gate: declaration {name} is partial"
      if fact.isAxiom then
        throwError "Effect4 trust gate: declaration {name} is an axiom; the tree declares none"
      if fact.isExtern then
        throwError "Effect4 trust gate: declaration {name} is `@[extern]`; a checked body is replaced by host code"
      if fact.implementedBy then
        throwError "Effect4 trust gate: declaration {name} is `@[implemented_by]`; a checked body is replaced by another"
      if fact.bodilessOpaque && !(admittedInitializedHandles.contains name && fact.hasInitFn) then
        throwError
          "Effect4 trust gate: declaration {name} is an `opaque` with no body, so it \
           denotes an arbitrary inhabitant rather than the value it advertises; give it \
           a body or make the boundary an authored admission"
  let declarations := facts.map (·.name)

  let t3 ← liftIO IO.monoMsNow
  let exactImplementationDeclarations ←
    match resolveChoiceImplementationDeclarations environment declarations with
    | .ok resolved => pure resolved
    | .error message => throwError "{message}"

  let admitted (declaration : Name) : Bool :=
    (moduleOf? environment declaration).any choiceImplementationModules.contains ||
      exactImplementationDeclarations.contains declaration
  let t4 ← liftIO IO.monoMsNow
  -- one memoized traversal of the dependency graph serves every declaration below. A planned
  -- goal (decisions row 203) is a leaf of the walk: it is reported among the axioms by its name,
  -- and its `sorry` is never entered, so `sorryAx` reaches a declaration only as a goal's body.
  let isGoal := ProofGraph.isGoal environment
  let (reachedAll, memoAll) := ProofGraph.reachedAxiomsMany environment declarations {} isGoal
  let mut memo : ProofGraph.AxiomMemo := memoAll
  let mut goalCount := 0
  let mut resting := 0
  for (declaration, reached) in declarations.zip reachedAll do
    let some axioms := reached
      | throwError "Effect4 axiom gate: axiom collection exhausted its step budget at {declaration}"
    if isGoal declaration then
      -- a goal is a theorem whose body is `sorry`, declared outside the application root
      let some (.thmInfo info) := environment.find? declaration
        | throwError "Effect4 goal gate: goal {declaration} is not a theorem"
      unless ProofGraph.bareSorry info.value do
        throwError "Effect4 goal gate: the body of goal {declaration} is not `sorry`"
      if (moduleOf? environment declaration).any apiModules.contains then
        throwError "Effect4 goal gate: goal {declaration} is in a module the Effect4 root reaches"
      goalCount := goalCount + 1
      continue
    if axioms.any isGoal then resting := resting + 1
    -- An auxiliary or equation lemma inherits the admission of the declaration
    -- it was generated from; see `admissionAncestors` for which parents count.
    let bound :=
      if admitted declaration || (admissionAncestors environment declaration).any admitted then
        auditImplementationAxioms
      else
        allowedAxioms
    for axiomName in axioms do
      if isGoal axiomName then continue
      if forbiddenAxioms.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches forbidden axiom {axiomName}"
      if !bound.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches unexpected axiom {axiomName}; allowed axioms are {bound}"

  let t5 ← liftIO IO.monoMsNow
  -- The exemption list must not outlive its reason. A named implementation
  -- module that no longer reaches `Classical.choice` is a stale entry and
  -- widens the trust boundary for nothing, so it fails the gate.
  for exempted in choiceImplementationModules do
    let mut used := false
    for declaration in byModule.getD exempted #[] do
      let (reached, memo') := (ProofGraph.reachedAxioms environment declaration isGoal).run memo
      memo := memo'
      if (reached.getD #[]).contains ``Classical.choice then
        used := true
    if !used then
      throwError
        "Effect4 axiom gate: stale implementation exemption for {exempted}; no declaration in it reaches Classical.choice, so remove it from choiceImplementationModules"

  for exempted in exactImplementationDeclarations do
    if !(declarations.contains exempted) then
      throwError
        "Effect4 axiom gate: exact implementation exemption names missing declaration {exempted}"
    let (reached, memo') := (ProofGraph.reachedAxioms environment exempted isGoal).run memo
    memo := memo'
    if !(reached.getD #[]).contains ``Classical.choice then
      throwError
        "Effect4 axiom gate: stale exact implementation exemption for {exempted}; it no longer reaches Classical.choice"

  for handle in admittedInitializedHandles do
    match environment.find? handle with
    | some (.opaqueInfo opaqueInfo) =>
      unless isSynthesizedOpaqueBody opaqueInfo.value && (getInitFnNameFor? environment handle).isSome do
        throwError
          "Effect4 trust gate: stale initialized-handle admission for {handle}; it is no longer an initializer-set opaque"
    | _ =>
      throwError
        "Effect4 trust gate: initialized-handle admission names a missing or non-opaque declaration {handle}"

  let t6 ← liftIO IO.monoMsNow
  logInfo
    m!"Effect4 module and axiom gate: checked {sources.size} modules and {declarations.size} declarations; phases (ms): sources and closure {t1 - t0}, library roots {t2 - t1}, declarations {t3 - t2}, resolution {t4 - t3}, axioms {t5 - t4}, exemptions {t6 - t5}; semantic/test axioms are {allowedAxioms}; exact implementation boundary ({choiceImplementationModules.length} module(s), {exactImplementationDeclarations.length} declaration(s)) additionally allows Classical.choice"
  logInfo m!"Effect4 goal gate: {goalCount} planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; {resting} declaration(s) rest on goals; no other declaration reaches sorryAx"

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
  let mut memo : ProofGraph.AxiomMemo := {}
  for (name, _) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        let (reached, memo') := (ProofGraph.reachedAxioms environment name).run memo
        memo := memo'
        if (reached.getD #[]).contains ``Classical.choice then
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
