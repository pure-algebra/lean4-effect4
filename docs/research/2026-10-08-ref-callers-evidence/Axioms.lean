import Test.Program.RefFaces
import Lean
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names := environment.constants.toList.filterMap fun (name, _) =>
    if name.toString.startsWith "Test.Program.RefPrograms." ||
        name.toString.startsWith "Test.Program.RefFaces." then some name else none
  let mut rejected := #[]
  for name in names do
    let axioms ← liftCoreM (collectAxioms name)
    for dependency in axioms do
      unless dependency == ``propext || dependency == ``Quot.sound do
        rejected := rejected.push (name, dependency)
  if !rejected.isEmpty then throwError "Rejected axioms: {rejected}"
  logInfo m!"PASS Ref packet axiom audit: {names.length} declarations at [propext, Quot.sound]"
