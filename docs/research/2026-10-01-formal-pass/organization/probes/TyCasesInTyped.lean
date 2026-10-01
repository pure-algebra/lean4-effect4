import Effect4
import Effect4.Laws

/-!
Seat ORGANIZATION probe (2026-10-01): row 132's proposed rule says "no case analysis on `Ty`
outside `Laws/Program/Typed/Membership.lean`", checked by the environment, not by grep. For every
declaration of a module under `Effect4.Laws.Program.Typed`, does its type or body use `Ty`'s
recursor, `casesOn`, `recOn`, `brecOn`, or a matcher whose body does? Lists the hits by module.
Red control: `Effect4.Program.Typed.Fits` (Membership) must be a hit.
-/

open Lean Elab Command

def tyElims : List Name := [`Effect4.Program.Ty.rec, `Effect4.Program.Ty.casesOn,
  `Effect4.Program.Ty.recOn, `Effect4.Program.Ty.brecOn, `Effect4.Program.Ty.below]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let usesTy (e : Expr) : Bool :=
    let cs := e.getUsedConstants
    cs.any (fun c => tyElims.contains c) ||
      cs.any (fun c => (Lean.Meta.isMatcherCore env c) &&
        match env.find? c with
        | some (.defnInfo d) => d.value.getUsedConstants.any (fun x => tyElims.contains x)
        | _ => false)
  let mut hits : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let m := mods[i.toNat]!
    unless (`Effect4.Laws.Program.Typed).isPrefixOf m do continue
    let body := (ci.value? (allowOpaque := true)).getD (mkConst `Unit)
    if usesTy ci.type || usesTy body then
      hits := hits.insert m ((hits.getD m #[]).push n)
  let rows := hits.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let lines := rows.map fun (m, ns) => s!"{m}: {ns.size} — {(ns.qsort (fun a b => a.toString < b.toString)).toList.take 8}"
  let red := (hits.getD `Effect4.Laws.Program.Typed.Membership #[]).contains `Effect4.Program.Typed.Fits
  logInfo m!"red control (Typed.Fits is a hit): {red}\n{"\n".intercalate lines.toList}"
