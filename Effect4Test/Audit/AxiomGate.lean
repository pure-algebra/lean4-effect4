import Lean
import Lean.Util.CollectAxioms
import Effect4

/-!
# Effect4 axiom allowlist gate

This command inspects every declaration compiled from an `Effect4` module,
including definitions, instances, generated declarations, and private helper
declarations. The build fails if any declaration reaches an axiom outside the
library's current ceiling: propositional extensionality and quotient soundness.

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

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  (`Effect4).isPrefixOf moduleName || (`Effect4Test).isPrefixOf moduleName

private def isGeneratedUnsafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some sourceInfo => !sourceInfo.isUnsafe && !sourceInfo.isPartial
      | none => false

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

  let mut declarations : Array Name := #[]
  for (name, info) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if !isGeneratedUnsafeRecursor environment name then
          if info.isUnsafe then
            throwError "Effect4 trust gate: declaration {name} is unsafe"
          if info.isPartial then
            throwError "Effect4 trust gate: declaration {name} is partial"
        declarations := declarations.push name

  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let bound :=
      if moduleOf? environment declaration == some `Effect4Test.Audit.AxiomGate then
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

  logInfo
    m!"Effect4 module and axiom gate: checked {sources.size} modules and {declarations.size} declarations; semantic/test axioms are {allowedAxioms}; audit implementation additionally allows Classical.choice"

end Effect4Test.Audit
