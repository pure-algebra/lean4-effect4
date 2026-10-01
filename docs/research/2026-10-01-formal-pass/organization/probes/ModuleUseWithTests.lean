import Effect4
import Effect4.Laws
import Test.All

/-!
Seat ORGANIZATION probe (2026-10-01): which proof-graph modules are used by other modules?
For every module under `Effect4.Laws` (`Test.All` loaded too, so a reference from a battery counts), count its
theorems and definitions, and how many of them are referenced by a declaration of another
module (in its type or value). A module with zero outside references is a leaf of the proof
graph: its content is consumed by nothing in the libraries (it may still be a receipt, a ledger
scope, or a test's subject). Nothing is asserted.
Red control: `Effect4.Laws.Machine.Lift` must show at least four outside references (the guard
driver and the fork-ledger user call `driveState_lift_unit`, `machineFact_stepDecision`; the memo-id
user calls `MachineEdits`, `interruptEdit`). A first run read theorem bodies with `value?`, which
answers `none` for a theorem unless `allowOpaque := true`; it reported Lift at 1 and is discarded.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  -- module index of every constant
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!
  -- referenced-from-another-module set
  let mut usedOutside : NameSet := {}
  for (n, ci) in env.constants.toList do
    let some mn := modOf n | continue
    let consts := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for c in consts do
      if let some mc := modOf c then
        if mc != mn then usedOutside := usedOutside.insert c
  -- per-module counts
  let mut table : Std.HashMap Name (Nat × Nat × Nat) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some mn := modOf n | continue
    unless (`Effect4.Laws).isPrefixOf mn do continue
    let isThmOrDef := match ci with | .thmInfo _ | .defnInfo _ => true | _ => false
    unless isThmOrDef do continue
    let (t, d, u) := table.getD mn (0, 0, 0)
    let t := if ci matches .thmInfo _ then t + 1 else t
    let d := if ci matches .defnInfo _ then d + 1 else d
    let u := if usedOutside.contains n then u + 1 else u
    table := table.insert mn (t, d, u)
  let rows := table.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let lines := rows.map fun (m, t, d, u) => s!"{m}\tthm {t}\tdef {d}\tusedOutside {u}"
  logInfo m!"modules under Effect4.Laws (Test loaded): {rows.size}\n{"\n".intercalate lines.toList}"
