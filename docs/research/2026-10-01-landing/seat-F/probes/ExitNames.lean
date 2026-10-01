import Effect4.Laws
import Test.Program.ExitConnector

/-!
Seat F probe (2026-10-01, landing item 4): the two exit judgments after the rename. Counts the
declarations whose type or value mentions each (auxiliaries included, the organization seat's
`NameUses.lean` rule), checks the old meaning-level name is gone, and prints the axioms of the
connector, its red controls and the renamed theorems.
Red control: `Effect4.Program.Typed.ExitOk` must still exist and be mentioned.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  for target in [`Effect4.Program.Denote.ExitHasTy, `Effect4.Program.Denote.ExitOk,
      `Effect4.Program.Typed.ExitOk] do
    let present := env.contains target
    let mut decls : Nat := 0
    let mut perMod : Std.HashMap Name Nat := {}
    for (n, ci) in env.constants.toList do
      let uses := ci.type.getUsedConstants.contains target ||
        (ci.value?.map (·.getUsedConstants.contains target)).getD false
      if uses && n != target then
        decls := decls + 1
        if let some idx := env.getModuleIdxFor? n then
          let m := env.header.moduleNames[idx.toNat]!
          perMod := perMod.insert m (perMod.getD m 0 + 1)
    let rows := perMod.toList.map (fun (m, k) => s!"{m} {k}")
    logInfo m!"{target}: exists {present}; {decls} declarations mention it, in {perMod.size} modules: {rows}"

#print axioms Effect4.Program.Typed.exitHasTy_of_fitsExit
#print axioms Effect4.Program.Denote.ExitHasTy.widen
#print axioms Effect4.Program.Denote.ExitHasTy.later
#print axioms Effect4.Program.Denote.meaning_typed
#print axioms Test.Program.ExitConnector.redA_scope
#print axioms Test.Program.ExitConnector.redB_external
#print axioms Test.Program.ExitConnector.validity_needed
#print axioms Test.Program.ExitConnector.allocation_needed
