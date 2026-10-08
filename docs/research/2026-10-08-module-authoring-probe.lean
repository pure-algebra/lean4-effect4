import Test.Program.ModuleDefinitions
import Test.Program.AuthoringModule
import Test.Program.AuthoringDefs
import ProofGraph.Audit
import ProofGraph.Axioms

/-!
A narrow receipt probe for declarative module authoring.
It audits declarations in the changed modules and writes four finite host examples.
It is not the whole-library axiom or closure gate.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Effect4.Program.Authoring.Defs, `Effect4.Program.Authoring.Module,
    `Effect4.Modules.Queue.Defs, `Effect4.Modules.Semaphore.Defs,
    `Test.Program.AuthoringDefs, `Test.Program.AuthoringModule, `Test.Program.ModuleDefinitions]
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env modules.contains
  unless missing.isEmpty do throwError "missing audited declarations: {missing}"
  unless facts.size > 0 do throwError "empty audit"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "unexpected trust boundary: {fact.name}"
  let names := facts.filterMap fun fact => if fact.safeRecursor then none else some fact.name
  let (results, _) := ProofGraph.reachedAxiomsMany env names {}
  let allowed := #[``propext, ``Quot.sound]
  let mut seen : Array Name := #[]
  for (name, axioms) in names.zip results do
    let some axioms := axioms | throwError "axiom traversal exhausted: {name}"
    for dependency in axioms do
      unless allowed.contains dependency do throwError "unexpected axiom {dependency} in {name}"
      unless seen.contains dependency do seen := seen.push dependency
  logInfo m!"Narrow authoring audit: {modules.size} modules, {names.size} declarations; axioms {seen}"

open Effect4 Effect4.Program Effect4.Program.Authoring
open Test.Program.ModuleDefinitions

/-- Write source declarations from the same modules that the Lean battery runs. -/
def main (args : List String) : IO Unit := do
  let directory := args.headD "/private/tmp/effect4-module-authoring-host/generated"
  IO.FS.createDirAll directory
  let cases : List (String × Module NativeOp) :=
    [("queue", twoTypesModule), ("semaphore", permits.module immediate),
      ("waiting", permits.module waiting), ("combined", numbers.install (permits.module combined))]
  for (name, source) in cases do
    let .ok built := Api.Author.build source | throw (IO.userError (name ++ ": build refused"))
    let some printed := Api.printModule "main" built.program built.table
      | throw (IO.userError (name ++ ": print refused"))
    IO.FS.writeFile (System.FilePath.mk directory / (name ++ ".ts"))
      (String.join (printed.decls.map (TypeScript.Render.decl TypeScript.house0)))
  IO.println s!"Wrote {cases.length} finite host examples"
