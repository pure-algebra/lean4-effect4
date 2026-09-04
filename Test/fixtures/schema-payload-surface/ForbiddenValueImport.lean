import Lean
import Effect4.Schema.Pins.Value

/-!
Reaction mutant for the declaration-free import hole. `Schema.Value` currently
exports no declaration, so a declaration lookup cannot observe this edge. The
module header must convict the import itself.
-/

open Lean Elab Command

run_cmd do
  let forbiddenModule := "Effect4.Schema.Value".toName
  let env ← getEnv
  let some valueModuleIndex := env.getModuleIdx? forbiddenModule
    | throwError
        "Schema.Value reaction fixture failed: imported module has no module index"
  let ownedDeclarations := env.const2ModIdx.toList.filterMap fun (name, moduleIndex) =>
    if moduleIndex == valueModuleIndex then some name else none
  unless ownedDeclarations.isEmpty do
    throwError
      "Schema.Value reaction fixture is no longer declaration-free: {ownedDeclarations}"
  let importedModules := env.header.moduleNames
  if importedModules.contains forbiddenModule then
    throwError
      "schema payload import-boundary mismatch: forbidden upward module Effect4.Schema.Value is present in the imported-module list"
  throwError
    "schema payload import-boundary detector failed to observe the injected Effect4.Schema.Value edge"
