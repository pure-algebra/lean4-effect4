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

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

private def belongsToEffect4 (moduleName : Name) : Bool :=
  (`Effect4).isPrefixOf moduleName

private partial def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  if ← (directory / "Effect4.lean").pathExists then
    return directory
  match directory.parent with
  | some parent => findProjectRoot parent
  | none => throw <| IO.userError "Effect4 axiom gate: could not locate the project root"

private def effect4Sources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let nested ← (projectRoot / "Effect4").walkDir
  let nested := nested.filter fun path => path.extension == some "lean"
  return nested.push (projectRoot / "Effect4.lean")

open Lean Elab Command in
elab "#effect4_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "Effect4 axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| effect4Sources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    (Lean.modToFilePath projectRoot moduleName "lean").normalize
  for source in sources do
    if !importedPaths.contains source.normalize then
      throwError
        "Effect4 module-closure gate: {source} is not reachable from the Effect4 root module"

  let mut declarations : Array Name := #[]
  for (name, _) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToEffect4 moduleName then
        declarations := declarations.push name

  for declaration in declarations do
    let axioms ← collectAxioms declaration
    for axiomName in axioms do
      if forbiddenAxioms.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches forbidden axiom {axiomName}"
      if !allowedAxioms.contains axiomName then
        throwError
          "Effect4 axiom gate: declaration {declaration} reaches unexpected axiom {axiomName}; allowed axioms are {allowedAxioms}"

  logInfo
    m!"Effect4 module and axiom gate: checked {sources.size} modules and {declarations.size} declarations; allowed axioms are {allowedAxioms}"

#effect4_axiom_gate

end Effect4Test.Audit
