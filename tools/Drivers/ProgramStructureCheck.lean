import Tools.ProgramStructure
import OCaml5.Eff.World
open Lean Meta Tools.ProgramStructure

def expectRefusal (name : String) (action : MetaM Unit) : MetaM Unit := do
  let refused ← try action; pure false catch _ => pure true
  unless refused do throwError "negative accepted: {name}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native }] {} 0
  let ctx : Core.Context := { fileName := "<structure-controls>", fileMap := default }
  let action : MetaM Unit := do
    let seeds := (allSpecs.map groundType).toArray
    checkProgramSeeds seeds
    checkProgramSeeds seeds.reverse
    expectRefusal "missing Ty" (checkProgramSeeds (seeds.filter (·.getAppFn != mkConst `Effect4.Program.Ty)))
    expectRefusal "wrong Eff parameter" (checkProgramSeeds (seeds.map fun e =>
      if e.getAppFn == mkConst `Effect4.Program.Eff then mkApp (mkConst `Effect4.Program.Eff) (mkConst ``Bool) else e))
    let functionType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
    expectRefusal "function field" (discard <| readShape 128 "Fixture.function" functionType)
    expectRefusal "unknown nominal" (discard <| readShape 128 "Fixture.unknown" (mkConst ``Int))
    expectRefusal "depth budget" (discard <| readShape 0 "Fixture.deep" (mkConst ``Nat))
    match OCaml5.Eff.projectShape "Fixture.row" (.canonicalRow .nat) with
    | .error _ => pure ()
    | .ok _ => throwError "unsupported canonical row accepted"
    IO.println s!"structure: {seeds.size} selected families; permutation accepted; six independent refusals"
  discard <| (action.run' {}).toIO ctx { env := env }
