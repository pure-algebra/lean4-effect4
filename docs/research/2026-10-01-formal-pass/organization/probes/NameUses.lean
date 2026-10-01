import Effect4
import Effect4.Laws
import Test.All

/-!
Seat ORGANIZATION probe (2026-10-01): how many declarations (production and `Test`) mention each of
the colliding names, in their type or body, and in how many modules: the size of a rename.
Red control: `Effect4.Program.Typed.Fits` must be mentioned by `Effect4.Program.Typed.fits_hasTy`.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let targets : List Name := [`Effect4.Program.Fits, `Effect4.Program.Typed.Fits,
    `Effect4.Machine.World, `Effect4.Program.Typed.World, `Effect4.Program.Ty.Canonical,
    `Effect4.Store.Canonical, `Effect4.Api.Typed, `Effect4.Laws.Effects.Typed,
    `Effect4.Program.Denote.ExitOk]
  let mut out : Array String := #[]
  for t in targets do
    let mut decls : Nat := 0
    let mut ms : NameSet := {}
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      let uses := ci.type.getUsedConstants.contains t ||
        ((ci.value? (allowOpaque := true)).map (·.getUsedConstants.contains t)).getD false
      if uses then
        decls := decls + 1
        if let some i := env.getModuleIdxFor? n then ms := ms.insert mods[i.toNat]!
    out := out.push s!"{t}: {decls} declarations in {ms.size} modules"
  let red : Bool := match env.find? `Effect4.Program.Typed.fits_hasTy with
    | some ci => ci.type.getUsedConstants.contains `Effect4.Program.Typed.Fits
    | none => false
  logInfo m!"red control (fits_hasTy mentions Typed.Fits): {red}\n{"\n".intercalate out.toList}"
