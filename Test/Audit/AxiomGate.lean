import Lean
import Lean.Util.CollectAxioms
import Effect4

/-!
# Effect4 axiom allowlist gate

This command tokenizes every authored `Effect4` source and inspects every
declaration compiled from it, including definitions, instances, generated
declarations, and private helper declarations. The build fails on an authored
trust token, on a bodyless `opaque`, or if any declaration reaches an axiom
outside the library's current ceiling: propositional extensionality and
quotient soundness.

The gate is intentionally exhaustive over the compiled namespace rather than
maintaining a hand-written theorem list. The separate axiom report remains a
human-readable receipt.

## Why the source is tokenized at all

The declaration pass reads `environment.constants`, and Lean's `example` never
enters the environment. Every trust token written inside an `example` is
therefore invisible to it — including `sorry`, which is a warning rather than
an error and leaves the build green. The source pass is what closes that hole:
it visits every token of every audited file whether or not the surrounding
declaration is named. `forbiddenTrustTokens` records what it refuses and why.

## The policy on `example`

An `example` stays an `example` when it is a sanity check — a shape that would
read the same as a comment, and that nothing cites. The tokenizer reaches
inside it now, so nothing trust-relevant hides there.

A *receipt* becomes a named `theorem` where it is cited. A receipt that leaves
no constant cannot be named by an axiom report, joined by
`Test/Audit/RuntimeCoverage.lean`, or listed by a proof-graph trust
edge: it is checked once at its declaration site and then vanishes. The six
DB-06 modality receipts in `Test/Semantics/LogicContract.lean` and the
per-program receipt `Effect4/Meta/Derive.lean` emits for every `effect_program`
were `example`s and are theorems now.

## The ruling on `opaque`

`opaque f : T := body` is admitted. The kernel checks `body`, the constant
denotes it, and hiding the unfolding costs the ceiling nothing.

`opaque f : T` with no body is refused. Lean synthesises `default_or_ofNonempty%`
for the missing value (`Lean/Elab/DefView.lean`), so the constant denotes an
arbitrary inhabitant nobody chose: it is an uninterpreted symbol wearing a
definition's clothes, and every receipt stated about it is a receipt about
nothing. `Effect4/AGENTS.md` already requires an authored admission for an
opaque trust boundary; this is the enforcement.

The refusal is a declaration-level check rather than a token, because the
source tokenizer sees the `opaque` keyword but cannot see whether a `:=`
follows it. The two shapes are told apart by the synthesised value's head
constant, which is `Inhabited.default` or `Classical.ofNonempty` and nothing
else. `test/fixtures/trust-gate/opaque.lean.txt` is the acceptance test.
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
  , `Test.Schema.PayloadSurface
  , `Test.Schema.StructuralAssurance
  , `Test.Data.RowAssurance
  , `Test.Machine.Environment.ContextKeyAssurance
  , `Test.Audit.RuntimeCoverage
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
`Effect4/Target/TypeScript/SkeletonRender.lean`, so the `String`-free IR and its
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
semantic admission theorem. `docs/TYPESCRIPT-TARGET-DAG.md` records this
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
  -- The Effect v4 profile: service-class, method-type and LLM-sheet renderers,
  -- and the module assemblers that concatenate their output. The profile's
  -- own row and spelling *data* are `String`-free and are not here.
  , ``Effect4.Target.EffectV4.ServiceRow.namespaces
  , ``Effect4.Target.EffectV4.ServiceRow.receiver
  , ``Effect4.Target.EffectV4.ServiceRow.sheet
  , ``Effect4.Target.EffectV4.ServiceRow.usesResult
  , ``Effect4.Target.EffectV4.Spelling.mentions
  , ``Effect4.Target.EffectV4.Spelling.namespacesOf
  , ``Effect4.Target.EffectV4.neededNamespaces
  , ``Effect4.Target.EffectV4.atomsModule
  , ``Effect4.Target.EffectV4.module
  , ``Effect4.Target.EffectV4.module?
  , ``Effect4.Target.EffectV4.modules?
  , ``Effect4.Target.EffectV4.source?
  -- The namespace set a generated module imports, computed from the rendered
  -- declarations (`Spelling.namespacesOf` over text), so it crosses like they do.
  , ``Effect4.Target.EffectV4.moduleNamespaces
  , ``Effect4.Target.EffectV4.Script.lower
  , ``Effect4.Target.EffectV4.Lowering.serviceAcquire
  ]

/-- Private rendering helpers are identified by exact owner and original name,
never a namespace prefix or Lean's unstable private-name counter. -/
private def choiceImplementationPrivateDeclarations : List (Name × Name) :=
  [ (`Effect4.Codegen.EffectfulField,
      `Effect4.Codegen.EffectfulField.directionalRowsPresent)
  ]

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/--
The authored trust tokens the source gate refuses, in either shape Lean's
tokenizer can produce for them.

Which shape a word takes depends on the token table of the environment doing
the audit, and the two halves of this list do not agree at this pin: `unsafe`,
`partial`, `sorry` and `axiom` are keywords and arrive as atoms, while
`native_decide`, `extern` and `implemented_by` are ordinary identifiers.
Checking both shapes means the list states a policy rather than tracking
Lean's grammar.

What each one buys:

* `unsafe`, `partial` — the original two; the compiled-environment pass below
  independently confirms `isUnsafe`/`isPartial`, and this catches them inside
  an `example`, where there is no constant to inspect.
* `sorry` — an admitted goal is a warning, not an error, so a `sorry` inside an
  `example` leaves no constant, emits no failure, and keeps the build green.
  Outside an `example` it also reaches `sorryAx`, which `forbiddenAxioms`
  refuses; this is the half that has no declaration behind it.
* `axiom` — a new axiom is only visible to the axiom pass once something
  reaches it. The gate's ceiling is a claim about what the tree *contains*, so
  the declaration is refused where it is written.
* `native_decide` — closes the goal by compiler evaluation and reaches
  `Lean.ofReduceBool`, already in `forbiddenAxioms`; again the point is the
  `example` that leaves nothing to inspect.
* `extern`, `implemented_by` — replace a checked Lean body with host code at
  runtime. Neither moves an axiom, and neither is a claim this tree is entitled
  to make about its own semantics.

An identifier is judged by its *raw* source text, never by its resolved name,
so the escaped `«unsafe»` of `test/fixtures/trust-gate/benign.lean.txt` stays a
name and a string literal stays prose.
-/
private def forbiddenTrustTokens : List String :=
  [ "unsafe", "partial", "sorry", "axiom"
  , "native_decide", "extern", "implemented_by" ]

/--
`admit` is refused only as a keyword.

At this toolchain pin it is not one: the tactic does not exist, so `admit`
tokenizes as an identifier — and it is the name of `Effects.admit`, the flow
admission function the lowering batteries call unqualified. Refusing the
identifier would refuse those batteries, so the entry sits here and fires only
if a future toolchain reintroduces the tactic and puts the word in the token
table. Nothing is lost meanwhile: the tactic expands to `sorry`, which the list
above refuses, and reaches `sorryAx`, which `forbiddenAxioms` refuses.
-/
private def forbiddenTrustKeywords : List String :=
  [ "admit" ]

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
  (`Effect4).isPrefixOf moduleName || (`Test).isPrefixOf moduleName ||
    (`Fixtures).isPrefixOf moduleName

/-- Where a module's source lives: the library under `src/`, the batteries and the
authored fixtures at the root (`lakefile.toml`). -/
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

/-
`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for this source check. Lean's own tokenizer skips comments and
handles ordinary, character, interpolated, and raw string literals, while the
compiled-environment pass below independently confirms declaration safety.
-/
/-- The forbidden word a single token carries, if any. A keyword arrives as an
atom whose value is the word; an ordinary identifier arrives as an ident, and
is judged by the raw source text so that `«unsafe»` and `Foo.unsafe` are names
rather than modifiers. Every other token shape — string, char, and numeric
literals above all — carries none. -/
private def forbiddenToken? (token : Syntax) : Option String :=
  match token with
  | .atom _ value =>
      let value := value.trimAscii.toString
      if forbiddenTrustTokens.contains value || forbiddenTrustKeywords.contains value then
        some value
      else
        none
  | .ident _ rawValue _ _ =>
      let raw := rawValue.toString
      if forbiddenTrustTokens.contains raw then some raw else none
  | _ => none

private def forbiddenTrustToken?
    (environment : Environment)
    (source : System.FilePath) : IO (Option String) := do
  let input ← IO.FS.readFile source
  let inputContext := Parser.mkInputContext input source.toString
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  while !inputContext.atEnd state.pos do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      throw <| IO.userError
        s!"Effect4 source trust gate: tokenization failed in {source}: {error}"
    state := skipped
    if inputContext.atEnd state.pos then
      return none
    -- Documentation comments are syntax nodes rather than whitespace. Consume
    -- them with Lean's own parsers so their prose never becomes audit tokens.
    let docComment := Parser.Command.docComment.fn.run
      inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
      continue
    let moduleDoc := Parser.Command.moduleDoc.fn.run
      inputContext parserContext tokenTable state
    if moduleDoc.errorMsg.isNone then
      state := moduleDoc.popSyntax
      projectionEnd := none
      continue
    -- Lean parses the index in `h.2.trans` and `h |>.2.trans` with
    -- `fieldIdxFn`: the ordinary number tokenizer mistakes `2.trans` for a
    -- decimal. Use the same parser only immediately after a projection dot;
    -- ordinary numerals and every tokenization error retain their usual path.
    let tokenParser :=
      if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
        Parser.fieldIdxFn
      else
        Parser.tokenFn []
    let next := tokenParser.run inputContext parserContext tokenTable state
    if let some error := next.errorMsg then
      let position := inputContext.fileMap.toPosition state.pos
      throw <| IO.userError
        s!"Effect4 source trust gate: tokenization failed in {source}:{position.line}:{position.column + 1}: {error}"
    let token := next.stxStack.back
    if let some found := forbiddenToken? token then
      return some found
    projectionEnd :=
      if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
    state := next.popSyntax
  return none

private def auditSourceTrustModifiers
    (environment : Environment)
    (sources : Array System.FilePath) : IO Unit := do
  for source in sources do
    if let some token ← forbiddenTrustToken? environment source then
      throw <| IO.userError
        s!"Effect4 source trust gate: {source} contains an authored `{token}` trust token"

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "lakefile.toml").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Effect4 axiom gate: could not locate the project root"
  throw <| IO.userError "Effect4 axiom gate: project-root search exceeded 64 parents"

/--
The modules `Test/fixtures/trust-gate/known-red.txt` declares intentionally
red, one per line, `#` comments and blank lines ignored.

The breaker/builder discipline has a phase in which a frozen red battery exists
and its implementation does not. Such a module is correctly *not* imported by
the audit root, so the closure check below would fire on it and the axiom scan
would never be reached — which is why `lake build` was red for as long as any
red phase was open. Reading the declared set keeps the closure check's teeth
(an *undeclared* unreachable module still fails) without letting a sanctioned
red phase defeat it. The entry is checked in the other direction too: a
declared module that the audit root does in fact import has outlived its red
phase and fails the gate.

The file is not optional. A missing one is a gate that checks nothing.

Lake does not trace it — it is not an import — so a `lake build` that replays
the audit root's olean carries the previous reading. `scripts/test-trust-gate.sh`
step 0 is the authority: it compares the declared set against the modules that
actually fail a red-inclusive build, in both directions, and deletes the audit
root's artifact from its probe copy so this check always re-runs there.
-/
private def declaredRedModules (projectRoot : System.FilePath) : IO (List Name) := do
  let path := projectRoot / "Test" / "fixtures" / "trust-gate" / "known-red.txt"
  unless ← path.pathExists do
    throw <| IO.userError
      s!"Effect4 module-closure gate: {path} is missing; the declared-red set is part of the gate, not an optional file"
  let contents ← IO.FS.readFile path
  return contents.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName

private def auditedSources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let effect4 ← (projectRoot / "src" / "Effect4").walkDir
  let effect4 := effect4.filter fun path => path.extension == some "lean"
  -- `Test/fixtures/` holds the gates' own probe sources (forged declarations, planted
  -- trust tokens); they are inputs to `scripts/test-trust-gate.sh`, not battery modules.
  let fixturesRoot := (projectRoot / "Test" / "fixtures").toString
  let tests ← (projectRoot / "Test").walkDir
  let tests := tests.filter fun path =>
    path.extension == some "lean" && !path.toString.startsWith fixturesRoot
  let fixturesDir := projectRoot / "Fixtures"
  let fixtures ← if ← fixturesDir.pathExists then fixturesDir.walkDir else pure #[]
  let fixtures := fixtures.filter fun path => path.extension == some "lean"
  return effect4 ++ tests ++ fixtures |>.push (projectRoot / "src" / "Effect4.lean")

open Lean Elab Command in
elab "#effect4_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "Effect4 axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    modulePath projectRoot moduleName
  let declaredRed ← liftIO <| declaredRedModules projectRoot
  let declaredRedPaths := declaredRed.map fun moduleName =>
    modulePath projectRoot moduleName
  for source in sources do
    if source.normalize != sourceFile.normalize
        && !importedPaths.contains source.normalize
        && !declaredRedPaths.contains source.normalize then
      throwError
        "Effect4 module-closure gate: {source} is not reachable from the Test.All audit root"
  for (moduleName, path) in declaredRed.zip declaredRedPaths do
    if !(sources.map System.FilePath.normalize).contains path then
      throwError
        "Effect4 module-closure gate: {moduleName} is declared red in \
         Test/fixtures/trust-gate/known-red.txt but has no source file at {path}"
    if importedPaths.contains path then
      throwError
        "Effect4 module-closure gate: {moduleName} is declared red in \
         Test/fixtures/trust-gate/known-red.txt but the audit root imports it; \
         its red phase is over, so remove the entry"

  liftIO <| auditSourceTrustModifiers environment sources

  let mut declarations : Array Name := #[]
  for (name, info) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if !isGeneratedSafeRecursor environment name then
          if info.isUnsafe then
            throwError "Effect4 trust gate: declaration {name} is unsafe"
          if info.isPartial then
            throwError "Effect4 trust gate: declaration {name} is partial"
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
