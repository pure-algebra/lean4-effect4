import Lean
import Lean.Util.CollectAxioms
import Effect4

/-!
# Effect4 axiom allowlist gate

This command tokenizes every authored `Effect4` source and inspects every
declaration compiled from it, including definitions, instances, generated
declarations, and private helper declarations. The build fails on authored
`unsafe` or `partial` declaration modifiers, or if any declaration reaches an
axiom outside the library's current ceiling: propositional extensionality and
quotient soundness.

The gate is intentionally exhaustive over the compiled namespace rather than
maintaining a hand-written theorem list. The separate axiom report remains a
human-readable receipt.
-/

open Lean

namespace Effect4Test.Audit

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
  [ `Effect4Test.Audit.AxiomGate
  , `Effect4Test.Schema.PayloadSurface
  , `Effect4Test.Schema.StructuralAssurance
  , `Effect4Test.Data.RowAssurance
  , `Effect4Test.Environment.ContextKeyAssurance
  , `Effect4Test.Concurrency.FiberAssurance
  , `Effect4Test.Audit.RuntimeCoverage
  , `Effect4Test.Target.TypeScript.LoweringCoverage
  ]

/--
Non-semantic target rendering must traverse Lean `String` values. Lean's
standard character folds currently carry `Classical.choice` through the proof
backing UTF-8 decoding. The renderer exemption is exact-module; the Schema
module receives no blanket exemption below.
-/
private def targetImplementationModules : List Name :=
  -- The syntax renderer lives in the `typescript` package, outside this tree.
  -- Two Effect4 modules are admitted exactly: the family DSL (`CommandElabM`
  -- reaches `Classical.choice`; it declares no theorem) and the Effect v4
  -- profile, whose service-class, method-type and LLM-sheet renderers traverse
  -- strings. Neither carries a semantic law; the trace and lowering laws live
  -- in `String`-free modules.
  [ `Effect4.Meta.Derive
  , `Effect4.Target.TypeScript.EffectV4
  , `Effect4.Target.TypeScript.Trace
  -- The dispatch-form renderer (`flowModules?` traverses strings through the
  -- syntax renderer); its lowering functions carry no semantic law.
  , `Effect4.Target.TypeScript.FlowLower
  -- The region lowering: the same renderer, nested scopes; no semantic law.
  , `Effect4.Target.TypeScript.RegionLower
  -- The structured form: the same renderer over structured statements.
  , `Effect4.Target.TypeScript.StructuredLower ]

private def choiceImplementationModules : List Name :=
  auditImplementationModules ++ targetImplementationModules

/-- Exact crossings from no-choice syntax generation to string rendering and
its output-text receipt. Admission and structured lowering in these modules
retain the semantic/test ceiling. The field receipt's statement itself uses
the renderer and `String.contains`; it is not a semantic admission theorem.
`docs/TYPESCRIPT-TARGET-DAG.md` records this implementation boundary. -/
private def choiceImplementationDeclarations : List Name :=
  [ ``Effect4.Target.TypeScript.Schema.jsonSource
  , ``Effect4.Target.TypeScript.Schema.representationSource
  , ``Effect4.Target.TypeScript.Schema.documentSource
  , ``Effect4.Target.TypeScript.Schema.multiDocumentSource
  , ``Effect4.Target.TypeScript.Schema.source?
  , ``Effect4.Target.TypeScript.Schema.generate?
  , ``Effect4.Target.TypeScript.EffectfulField.source?
  , ``Effect4.Target.TypeScript.EffectfulField.generate?
  , ``Effect4.Target.TypeScript.EffectfulField.source_contains_directional_rows
  -- The label-scoping laws whose *statements* name Effect4's printer.
  -- `Skeleton.render` spells `a<block>` and compares `spec.requestTy`, so it
  -- already crosses the boundary above and a theorem about its output inherits
  -- the crossing. The scoping law itself — `emitNode_wellScoped`,
  -- `emitWith_wellScoped` over `Structuring.emitWith`, and its discharge for
  -- Effect4's own lowering, `skeletonBlockWith_wellScoped` and
  -- `skeletonBody_wellScoped` — is `String`-free at the skeleton and stays at
  -- the ceiling; only the four transports through `render` are admitted, by
  -- exact declaration.
  , ``Effect4.Target.Structured.render_wellScoped
  , ``Effect4.Target.Structured.renderList_wellScoped
  , ``Effect4.Target.Structured.renderCases_wellScoped
  , ``Effect4.Target.Structured.structuredBody_wellScoped
  ]

/-- Private rendering helpers are identified by exact owner and original name,
never a namespace prefix or Lean's unstable private-name counter. -/
private def choiceImplementationPrivateDeclarations : List (Name × Name) :=
  [ (`Effect4.Target.TypeScript.EffectfulField,
      `Effect4.Target.TypeScript.EffectfulField.directionalRowsPresent) ]

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

private def resolveChoiceImplementationDeclarations
    (environment : Environment) (declarations : Array Name) : Except String (List Name) := do
  let mut resolved := choiceImplementationDeclarations
  for (owner, originalName) in choiceImplementationPrivateDeclarations do
    let privateCandidates := declarations.toList.filter fun declaration =>
      moduleOf? environment declaration == some owner &&
        privateToUserName? declaration == some originalName
    match privateCandidates with
    | [declaration] => resolved := resolved ++ [declaration]
    | _ => throw s!"Effect4 axiom gate: private implementation exemption {owner}/{originalName} matched {privateCandidates.length} declarations; expected exactly one"
  return resolved

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  (`Effect4).isPrefixOf moduleName || (`Effect4Test).isPrefixOf moduleName

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
    if token.isToken "unsafe" then
      return some "unsafe"
    if token.isToken "partial" then
      return some "partial"
    projectionEnd :=
      if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
    state := next.popSyntax
  return none

private def auditSourceTrustModifiers
    (environment : Environment)
    (sources : Array System.FilePath) : IO Unit := do
  for source in sources do
    if let some modifier ← forbiddenTrustToken? environment source then
      throw <| IO.userError
        s!"Effect4 source trust gate: {source} contains an authored `{modifier}` declaration modifier"

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Effect4.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Effect4 axiom gate: could not locate the project root"
  throw <| IO.userError "Effect4 axiom gate: project-root search exceeded 64 parents"

private def auditedSources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let effect4 ← (projectRoot / "Effect4").walkDir
  let effect4 := effect4.filter fun path => path.extension == some "lean"
  let tests ← (projectRoot / "Effect4Test").walkDir
  let tests := tests.filter fun path => path.extension == some "lean"
  return effect4 ++ tests |>.push (projectRoot / "Effect4.lean")
    |>.push (projectRoot / "Effect4Test.lean")

open Lean Elab Command in
elab "#effect4_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "Effect4 axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    (Lean.modToFilePath projectRoot moduleName "lean").normalize
  for source in sources do
    if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize then
      throwError
        "Effect4 module-closure gate: {source} is not reachable from the Effect4Test audit root"

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
        declarations := declarations.push name

  let exactImplementationDeclarations ←
    match resolveChoiceImplementationDeclarations environment declarations with
    | .ok resolved => pure resolved
    | .error message => throwError "{message}"

  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let bound :=
      if (moduleOf? environment declaration).any choiceImplementationModules.contains ||
          exactImplementationDeclarations.contains declaration then
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

end Effect4Test.Audit
