import Lean
import ProofGraph.Audit
import ProofGraph.Axioms
import ProofGraph.Goal
import Effect4
import Effect4.Laws.Author.Explain

/-! Finite source-extracted admission reader. Its JSON manifest pins every copied block.
This checks admission and axiom filtering only, not the full gate or module closure. -/

namespace ExplainAdmissionProbe
open Lean Elab Command
open ProofGraph.Audit (moduleOf?)

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
  -- The deriving step of `Modeled` (`deriving Modeled`, `derive_modeled`): a command elaborator
  -- and a deriving handler that check a structure and write its instance; meta code, no theorem
  -- in the module. The carrier fold and the class (`Effect4.Schema.Modeled`) and their laws stay
  -- at the ceiling (decisions row 330).
  , `Effect4.Schema.Modeled.Derive
  -- A field reference by name (`field_ref%`): a term elaborator that reads a schema and writes the
  -- positional reference; meta code, no theorem in the module (decisions row 330).
  , `Effect4.Schema.FieldRef.Elab
  -- Named construction and binders elaborate existing indexed step data; no semantic theorem.
  , `Effect4.Step.Elab
  , `Effect4.Step.Elab.Inputs
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
  -- `#explain` and `#obligations` read the environment and render their answers (row 332).
  -- Their exact implementation roots admit their same-module generated descendants.
  -- The answer structures and their derived `modeled_*` certificates retain allowedAxioms.
  , `Tools.Explain.authored
  , `Tools.Explain.boolOf?
  , `Tools.Explain.canonicalJson
  , `Tools.Explain.elabExplain
  , `Tools.Explain.elabExplainJson
  , `Tools.Explain.elabExplainSchema
  , `Tools.Explain.elabObligations
  , `Tools.Explain.elabObligationsJson
  , `Tools.Explain.explain
  , `Tools.Explain.explainSyntax
  , `Tools.Explain.inTree
  , `Tools.Explain.kindOf
  , `Tools.Explain.natOf?
  , `Tools.Explain.neighbours
  , `Tools.Explain.obligations
  , `Tools.Explain.obligationsOf
  , `Tools.Explain.optionNatOf?
  , `Tools.Explain.render
  , `Tools.Explain.schemaText
  , `Tools.Explain.standingOf
  , `Tools.Explain.statementOf
  , `Tools.Explain.stepFacts?
  , `Tools.Explain.stringsOf?
  , `Tools.Explain.tyText
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


def checkDeclaration (environment : Environment) (declaration : Name) (axioms : Array Name) : CoreM Unit := do
  let exactImplementationDeclarations := choiceImplementationDeclarations
  let admitted (declaration : Name) : Bool :=
    (moduleOf? environment declaration).any choiceImplementationModules.contains ||
      exactImplementationDeclarations.contains declaration
  let isGoal := ProofGraph.isGoal environment
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


run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filterMap fun (n, _) =>
    if moduleOf? env n == some `Effect4.Laws.Author.Explain then some n else none).toArray
  let (reached, _) := ProofGraph.reachedAxiomsMany env names {}
  let mut choice : Array Name := #[]
  let mut certs : Array Name := #[]
  for (n, ax) in names.zip reached do
    let some ax := ax | throwError "measurement exhausted its budget at {n}"
    if ax.contains ``Classical.choice then choice := choice.push n
    if ["modeled_checked", "modeled_to_of", "modeled_of_to"].contains n.getString! then
      certs := certs.push n
    liftCoreM <| checkDeclaration env n ax
  logInfo m!"PASS every actual Explain declaration satisfies the extracted policy: {names.size} declarations"
  logInfo m!"MEASURE actual choice reachers: {choice.size}"
  for n in choice.qsort (fun a b => a.toString < b.toString) do logInfo m!"CHOICE {n}"
  let exact := choiceImplementationDeclarations.filter (`Tools.Explain).isPrefixOf
  logInfo m!"MEASURE exact Explain roots: {exact.length}"
  if !false then
    unless exact.length == 24 do throwError "unexpected exact root count"
    for n in exact do
      let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
      unless (ax.getD #[]).contains ``Classical.choice do throwError "stale exact Explain root: {n}"
      if (env.find? n) matches some (.thmInfo _) then throwError "exact root admits a theorem: {n}"
    let inherited := choice.filter fun n => !exact.contains n
    logInfo m!"PASS {inherited.size} non-root reporting declarations use existing ancestor admissions"
  logInfo m!"MEASURE derived certificates: {certs.size}"
  unless certs.size == 12 do throwError "unexpected certificate count"
  for n in certs.qsort (fun a b => a.toString < b.toString) do
    let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
    logInfo m!"CERTIFICATE {n}: {ax}"
    let oldAllowed := (moduleOf? env n).any choiceImplementationModules.contains
    if oldAllowed != false then throwError "unexpected certificate module admission"
  let reporter := ``Tools.Explain.render
  let (ax, _) := (ProofGraph.reachedAxioms env reporter).run {}
  unless (ax.getD #[]).contains ``Classical.choice do throwError "positive reporter uses no choice"
  liftCoreM <| checkDeclaration env reporter (ax.getD #[])
  logInfo "PASS positive reporting declaration remains admitted"

end ExplainAdmissionProbe

open Lean Elab Command in
run_cmd do
  let previous ← searchPathRef.get
  searchPathRef.set (System.FilePath.mk "docs/research/2026-10-08-explain-admission-probe-fixture-mutant" :: previous)
  let env ← importModules #[{ module := `Effect4.Laws.Author.Explain }] (← getOptions)
  searchPathRef.set previous
  let n := `Tools.Explain.AdmissionControl.modeled_checked
  unless ProofGraph.Audit.moduleOf? env n == some `Effect4.Laws.Author.Explain do
    throwError "fixture certificate has the wrong module owner"
  let (ax, _) := (ProofGraph.reachedAxioms env n).run {}
  let some ax := ax | throwError "fixture walk exhausted its budget"
  unless (ax.contains ``Classical.choice) == true do throwError "fixture has the wrong axiom set: {ax}"
  logInfo m!"FIXTURE {n}: {ax}"
  let refusal ← try
      liftCoreM <| ExplainAdmissionProbe.checkDeclaration env n ax
      pure none
    catch ex => pure (some ex.toMessageData)
  match refusal with
  | none =>
    if true then throwError "certificate choice mutant escaped the policy"
    logInfo "PASS fixture certificate accepted"
  | some message =>
    unless true do throwError "unexpected refusal: {message}"
    logInfo m!"PASS certificate choice mutant rejected by the extracted policy: {message}"
