import Lean
import Lean.Compiler.IR.CompilerM
import Lean.Util.CollectAxioms
import Effect4.Machine.LiveStack

/-!
Compiled inspection for the live-stack packet. The graph is over proof-erased
IR calls, including closure construction and every branch; theorem statements
and erased proof arguments are deliberately not executable dependencies.
The source review remains necessary: an optimizer can erase source provenance.
This file is host audit tooling, not a new semantic declaration or trust waiver.
-/

open Lean Elab Command

namespace LiveStackInspection

private def expectedPublic : Array Name := #[
  `Effect4.FrameFiber.popLive,
  `Effect4.FrameFiber.getContLive,
  `Effect4.FrameFiber.popLive_eq_popFrom,
  `Effect4.FrameFiber.getContLive_eq_getCont,
  `Effect4.FrameFiber.getContLive_false_eq_getCont,
  `Effect4.FrameFiber.getContLive_deferred_kept,
  `Effect4.FrameFiber.getContLive_deferred_discarded,
  `Effect4.FrameFiber.getContLive_while]

private def forbidden : Array Name := #[
  `Effect4.FrameFiber.popFrom, `Effect4.FrameFiber.getCont]

private def owner := `Effect4.Runtime.LiveStack

private def namesJson (names : Array Name) : Json :=
  toJson (names.map toString)

private def sorted (names : Array Name) : Array Name :=
  names.qsort Name.quickLt

private def unique (names : Array Name) : Array Name :=
  names.foldl (fun result name => if result.contains name then result else result.push name) #[]

private def blocked (name : Name) : Bool :=
  forbidden.any (·.isPrefixOf (privateToUserName? name |>.getD name))

private def exprCalls : IR.Expr → Array Name
  | .fap name _ | .pap name _ => #[name]
  | _ => #[]

/-- Explicit finite worklist: exhaustion is a failed audit, never acceptance. -/
private def bodyCalls : Nat → List IR.FnBody → Array Name → Except String (Array Name)
  | _, [], calls => .ok (unique calls)
  | 0, _ :: _, _ => .error "IR body inspection exhausted its node budget"
  | fuel + 1, body :: todo, calls =>
    match body with
    | .vdecl _ _ (.ap _ _) _ =>
      .error "Unresolved dynamic IR call; a named transitive graph cannot certify this route"
    | .vdecl _ _ value next => bodyCalls fuel (next :: todo) (calls ++ exprCalls value)
    | .jdecl _ _ value next => bodyCalls fuel (value :: next :: todo) calls
    | .set _ _ _ next | .setTag _ _ next | .uset _ _ _ next
    | .sset _ _ _ _ _ next | .inc _ _ _ _ next | .dec _ _ _ _ next
    | .del _ next => bodyCalls fuel (next :: todo) calls
    | .case _ _ _ alternatives => bodyCalls fuel (alternatives.toList.map (·.body) ++ todo) calls
    | .ret _ | .jmp _ _ | .unreachable => bodyCalls fuel todo calls

private def findIR? (env : Environment) (name : Name) : Option IR.Decl := do
  -- Load only the requested owner's table and prefer a loaded body over its
  -- exported opaque signature. Compiler-only names have owner metadata too.
  if let some index := env.getModuleIdxFor? name then
    let bodies := IR.declMapExt.getModuleIREntries env index
    let entries := IR.declMapExt.getModuleEntries env index
    bodies.find? (fun decl => decl.name == name && !decl.isExtern) <|>
      entries.find? (fun decl => decl.name == name && !decl.isExtern) <|>
      bodies.find? (fun decl => decl.name == name) <|>
      entries.find? (fun decl => decl.name == name)
  else
    IR.findEnvDecl env name

private structure Graph where
  visited : Array Name := #[]
  edges : Array (Name × Name) := #[]
  externs : Array Name := #[]
  violations : Array Name := #[]

private def graphJson (root : Name) (graph : Graph) : Json := Json.mkObj [
  ("root", toJson root.toString),
  ("visited", namesJson (sorted graph.visited)),
  ("edges", toJson (graph.edges.map fun (a, b) => #[a.toString, b.toString])),
  ("externs", namesJson (sorted graph.externs)),
  ("violations", namesJson (sorted graph.violations))]

private def walk (lookup : Name → Option IR.Decl) :
    Nat → List Name → Graph → Except String Graph
  | _, [], graph => .ok graph
  | 0, _ :: _, _ => .error "IR call graph exhausted its declaration budget"
  | fuel + 1, name :: todo, graph => do
    if graph.visited.contains name then
      return ← walk lookup fuel todo graph
    let graph := { graph with visited := graph.visited.push name }
    if blocked name then
      return ← walk lookup fuel todo { graph with violations := graph.violations.push name }
    let some decl := lookup name
      | throw s!"Missing compiled IR for reachable declaration {name}"
    match decl with
    | .extern _ _ _ details => do
      if details.entries.isEmpty || details.entries.contains .opaque then
        throw s!"Reachable Lean declaration has only an opaque IR signature: {name}"
      if (`Effect4).isPrefixOf (privateToUserName? name |>.getD name) then
        throw s!"Effect4 executable boundary has no inspected IR body: {name}"
      walk lookup fuel todo { graph with externs := graph.externs.push name }
    | .fdecl _ _ _ body _ =>
      let calls ← bodyCalls 100000 [body] #[]
      walk lookup fuel (calls.toList ++ todo)
        { graph with edges := graph.edges ++ calls.map (name, ·) }

private def inspectRoot (lookup : Name → Option IR.Decl) (root : Name) : Except String Graph := do
  let some decl := lookup root
    | throw s!"Missing compiled executable root {root}"
  if decl.isExtern then throw s!"Executable root {root} has no inspected body"
  let graph ← walk lookup 100000 [root] {}
  if graph.visited.isEmpty then throw "Empty compiled dependency discovery"
  return graph

private def requireClean (root : Name) (graph : Graph) : Except String Unit :=
  if graph.violations.isEmpty then .ok ()
  else .error s!"Executable legacy delegation from {root}: {graph.violations}"

/- These isolated executable controls are not reachable from the production
   roots. noinline makes the intended indirect edge independently observable. -/
@[noinline] private def cleanHelper (n : Nat) : Nat := n + 1
@[noinline] private def cleanRoot (n : Nat) : Nat := cleanHelper n

private abbrev TestFiber := Effect4.FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev TestPop := Effect4.FramePop Nat Nat Nat Nat Nat Nat Nat

@[noinline] private def legacyHelper (self : TestFiber) : TestPop :=
  self.getCont .contE true

@[noinline] private def indirectRoot (self : TestFiber) : TestPop := legacyHelper self

@[noinline] private def fallbackHelper (takeFallback : Bool) (self : TestFiber) : TestPop :=
  if takeFallback then
    Effect4.FrameFiber.popFrom .contE true self.stack { self with stack := [] }
  else
    ⟨.empty, [], [], self⟩

@[noinline] private def fallbackRoot (takeFallback : Bool) (self : TestFiber) : TestPop :=
  fallbackHelper takeFallback self

private def controls (lookup : Name → Option IR.Decl) : Except String Json := do
  let clean ← inspectRoot lookup ``cleanRoot
  requireClean ``cleanRoot clean
  let indirect ← inspectRoot lookup ``indirectRoot
  let fallback ← inspectRoot lookup ``fallbackRoot
  for (root, graph) in #[( ``indirectRoot, indirect), (``fallbackRoot, fallback)] do
    if graph.violations.isEmpty then throw s!"Compiled negative was not rejected: {root}"
    if graph.edges.any (fun (caller, target) => caller == root && blocked target) then
      throw s!"Negative {root} is direct; it does not exercise transitive discovery"
    if !(graph.edges.any fun (caller, _) => caller == root) then
      throw s!"Negative {root} has no outgoing helper edge"
  let restored ← inspectRoot lookup ``cleanRoot
  requireClean ``cleanRoot restored
  match inspectRoot lookup `LiveStackInspection.deliberatelyMissingRoot with
  | .ok _ => throw "Missing executable root was accepted"
  | .error _ => pure ()
  let missingHelper name := if name == ``cleanHelper then none else lookup name
  match inspectRoot missingHelper ``cleanRoot with
  | .ok _ => throw "Missing reachable helper was accepted"
  | .error _ => pure ()
  let opaqueHelper name := (lookup name).map fun decl =>
    if name == ``cleanHelper then
      IR.Decl.extern decl.name decl.params decl.resultType { entries := [.opaque] }
    else decl
  match inspectRoot opaqueHelper ``cleanRoot with
  | .ok _ => throw "Opaque reachable helper was accepted"
  | .error _ => pure ()
  if cleanHelper 41 != 42 then throw "Compiled positive control returned the wrong value"
  let sample : TestFiber := ⟨.success 7, [], true, none, false⟩
  if (fallbackRoot false sample).answer != .empty then
    throw "Fallback control did not accept its non-legacy execution path"
  return Json.mkObj [
    ("accepted", graphJson ``cleanRoot clean),
    ("indirectRejected", graphJson ``indirectRoot indirect),
    ("untakenFallbackRejected", graphJson ``fallbackRoot fallback),
    ("fallbackPositiveInput", toJson false),
    ("missingRootRejected", toJson true),
    ("missingHelperRejected", toJson true),
    ("opaqueHelperRejected", toJson true),
    ("restored", graphJson ``cleanRoot restored)]

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def safeRecursorParent (env : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
    match env.find? sourceName with
    | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
    | _ => false

private def checkDeclarationSafety (env : Environment) (name : Name)
    (info : ConstantInfo) (hasSourceRange : Bool) : Except String Bool := do
  -- A suffix is not provenance: authors can spell a private `_unsafe_rec`.
  -- Only a rangeless compiler companion of a safe definition is exempted.
  let generatedSafe := !hasSourceRange && safeRecursorParent env name
  if (info.isUnsafe || info.isPartial) && !generatedSafe then
    throw s!"Declaration {name} is authored unsafe/partial or has no safe generated-recursion provenance"
  return generatedSafe

private def safetyDecoy (n : Nat) : Nat := n
-- Intentionally unsafe audit negative, outside the library/test namespaces.
private unsafe def safetyDecoy._unsafe_rec (n : Nat) : Nat := n

private def safetyControls : CommandElabM Json := do
  let env ← getEnv
  let clean := ``cleanHelper
  let decoy := ``safetyDecoy._unsafe_rec
  let some cleanInfo := env.find? clean | throwError "Missing clean safety control"
  let cleanRange := (← findDeclarationRangesCore? clean).isSome
  let .ok _ := checkDeclarationSafety env clean cleanInfo cleanRange
    | throwError "Clean safety control was rejected"
  let some decoyInfo := env.find? decoy | throwError "Missing compiled safety decoy"
  let decoyRange := (← findDeclarationRangesCore? decoy).isSome
  unless decoyInfo.isUnsafe && decoyRange && safeRecursorParent env decoy do
    throwError "The compiled decoy does not exercise the authored unsafe suffix bypass"
  let .error reason := checkDeclarationSafety env decoy decoyInfo decoyRange
    | throwError "Authored unsafe suffix decoy was accepted as compiler-generated"
  let .ok _ := checkDeclarationSafety env clean cleanInfo cleanRange
    | throwError "Restored clean safety control was rejected"
  return Json.mkObj [
    ("accepted", toJson clean.toString), ("restored", toJson clean.toString),
    ("authoredUnsafeSuffix", Json.mkObj [
      ("name", toJson decoy.toString), ("unsafe", toJson decoyInfo.isUnsafe),
      ("partial", toJson decoyInfo.isPartial), ("sourceRange", toJson decoyRange),
      ("safeParent", toJson (safeRecursorParent env decoy)),
      ("rejected", toJson true), ("reason", toJson reason)])]

private def parseImportHeader (source input : String) : IO HeaderSyntax := do
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input source)
  if messages.hasErrors then
    throw <| IO.userError s!"Invalid Lean import header in {source}"
  return header

private def requiredImports (source : String) (imports : Array Import)
    (required : Array Name) : Except String Unit := do
  if imports.isEmpty then throw s!"Empty parsed import header in {source}"
  for name in required do
    let selected := imports.filter (·.module == name)
    unless selected.size == 1 && selected.all (!·.isMeta) do
      throw s!"Expected exactly one regular import of {name} in {source}, found {selected.size}"

private def checkRootImports : IO Json := do
  let roots : Array (String × Array Name) := #[
    ("Effect4.lean", #[`Effect4.Runtime.LiveStack]),
    ("Test.lean", #[`Test.Runtime.LiveStackContract,
      `Test.Runtime.LiveStackAxiomReport, `Test.Counterexamples.Runtime.LiveStack])]
  let mut receipts : Array Json := #[]
  for (source, required) in roots do
    let input ← IO.FS.readFile source
    let header ← parseImportHeader source input
    let imports := header.imports (includeInit := false)
    if let .error reason := requiredImports source imports required then
      throw <| IO.userError reason
    let nodes := header.raw[2].getArgs
    unless nodes.size == imports.size do
      throw <| IO.userError s!"Incomplete Lean import syntax discovery in {source}"
    let mut negatives : Array Json := #[]
    for omitted in required do
      let some index := imports.findIdx? (·.module == omitted)
        | throw <| IO.userError s!"Missing required import node for {omitted}"
      let some node := nodes[index]?
        | throw <| IO.userError s!"Missing required import syntax for {omitted}"
      let some start := node.getPos?
        | throw <| IO.userError s!"Import {omitted} has no source start"
      let some stop := node.getTailPos?
        | throw <| IO.userError s!"Import {omitted} has no source end"
      let commented := String.Pos.Raw.extract input 0 start ++ "/- " ++
        String.Pos.Raw.extract input start stop ++ " -/" ++
        String.Pos.Raw.extract input stop input.rawEndPos
      let negativeHeader ← parseImportHeader source commented
      let negativeImports := negativeHeader.imports (includeInit := false)
      unless negativeImports.map (·.module) ==
          (imports.filter (·.module != omitted)).map (·.module) do
        throw <| IO.userError s!"Comment control changed imports other than {omitted}"
      let .error reason := requiredImports source negativeImports required
        | throw <| IO.userError s!"Commented-out required import {omitted} was accepted"
      negatives := negatives.push <| Json.mkObj [
        ("omitted", toJson omitted.toString), ("parsed", toJson true),
        ("observedImports", namesJson (negativeImports.map (·.module))),
        ("rejected", toJson true), ("reason", toJson reason)]
    let restored := (← parseImportHeader source input).imports (includeInit := false)
    if let .error reason := requiredImports source restored required then
      throw <| IO.userError s!"Restored header failed: {reason}"
    unless restored.map (·.module) == imports.map (·.module) do
      throw <| IO.userError s!"Restored header changed parsed imports in {source}"
    receipts := receipts.push <| Json.mkObj [
      ("source", toJson source), ("parser", toJson "Lean.Parser.parseHeader"),
      ("required", namesJson required), ("observedImports", namesJson (imports.map (·.module))),
      ("commentedOutControls", toJson negatives), ("restored", toJson true)]
  return toJson receipts

private def getOrFail {α : Type} (result : Except String α) : CommandElabM α :=
  match result with
  | .ok value => pure value
  | .error message => throwError "{message}"

private def inspect : CommandElabM Unit := do
  let env ← getEnv
  let lookup := findIR? env
  let controlReceipt ← getOrFail (controls lookup)
  let safetyReceipt ← safetyControls
  let importReceipt ← liftIO checkRootImports
  let controlsOnly := (← liftIO <| IO.getEnv "EFFECT4_LIVE_STACK_INSPECT_CONTROLS_ONLY") == some "1"
  if controlsOnly then
    liftIO <| IO.println <| (Json.mkObj [
      ("kind", toJson "live-stack-inspection"), ("mode", toJson "controls-only"),
      ("controls", controlReceipt), ("safetyControls", safetyReceipt),
      ("rootImports", importReceipt)]).compress
    return
  let some moduleIndex := env.getModuleIdx? owner
    | throwError "Target module is absent from compiled imports"
  let some moduleData := env.header.moduleData[moduleIndex]?
    | throwError "Target module has no compiled declaration table"
  -- Read the compiler's exact owner table, not a namespace approximation.
  let owned := sorted moduleData.constNames
  if owned.isEmpty then throwError "Empty target declaration discovery"
  let mut rows : Array Json := #[]
  let mut authoredPublic : Array Name := #[]
  for name in owned do
    unless env.getModuleIdxFor? name == some moduleIndex do
      throwError "Declaration {name} has inconsistent compiled module ownership"
    let some info := env.find? name | throwError "Missing owned declaration {name}"
    let ranges ← findDeclarationRangesCore? name
    let safeRecursor ← getOrFail <| checkDeclarationSafety env name info ranges.isSome
    let isPrivate := privateToUserName? name |>.isSome
    if !isPrivate && !name.isInternal && ranges.isSome then
      authoredPublic := authoredPublic.push name
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Quot.sound].contains axiomName do
        throwError "Owned declaration {name} reaches forbidden axiom {axiomName}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind info)),
      ("private", toJson isPrivate), ("internal", toJson name.isInternal),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("generatedSafeRecursor", toJson safeRecursor),
      ("sourceRange", toJson ranges.isSome),
      ("axioms", namesJson (sorted axioms))]
  unless sorted authoredPublic == sorted expectedPublic do
    throwError "Authored public declaration mismatch: expected {expectedPublic}, observed {authoredPublic}"
  let ownedIR := IR.declMapExt.getModuleIREntries env moduleIndex ++
    IR.declMapExt.getModuleEntries env moduleIndex
  let irNames := sorted <| unique (ownedIR.map (·.name))
  if irNames.isEmpty then throwError "Empty target IR declaration discovery"
  let mut roots : Array Json := #[]
  for root in #[`Effect4.FrameFiber.popLive, `Effect4.FrameFiber.getContLive] do
    let graph ← getOrFail (inspectRoot lookup root)
    getOrFail (requireClean root graph)
    roots := roots.push (graphJson root graph)
  -- Repeat the target check after negatives, not just the synthetic control.
  for root in #[`Effect4.FrameFiber.popLive, `Effect4.FrameFiber.getContLive] do
    getOrFail <| requireClean root (← getOrFail (inspectRoot lookup root))
  liftIO <| IO.println <| (Json.mkObj [
    ("kind", toJson "live-stack-inspection"), ("mode", toJson "full"),
    ("module", toJson owner.toString), ("lean", toJson Lean.versionString),
    ("authoredPublic", namesJson (sorted authoredPublic)),
    ("declarations", toJson rows), ("irDeclarations", namesJson irNames),
    ("compiledExtraNames", namesJson (sorted moduleData.extraConstNames)),
    ("roots", toJson roots), ("controls", controlReceipt),
    ("safetyControls", safetyReceipt), ("rootImports", importReceipt),
    ("restoredProduction", toJson true)]).compress

run_cmd inspect

end LiveStackInspection
