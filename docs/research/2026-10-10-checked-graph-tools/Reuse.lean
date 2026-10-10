import Tools.View.Flow
import Lean

/-! Bounded compiler inspection of retained layout preparation.
This establishes compiled call structure, not a timing or complexity theorem. -/
set_option autoImplicit false
open Lean Compiler LCNF
open Tools.View.Flow
run_elab do
  let env ← getEnv
  let selected := [``PreparedPlacement.height, ``preparePlacement, ``placeWith, ``assignHeights]
  let mut seen : Array Lean.Name := #[]
  for i in [:env.header.modules.size] do
    for decl in monoExt.getModuleEntries env i do
      if selected.any (·.isPrefixOf decl.name) && !seen.contains decl.name then
        seen := seen.push decl.name
        let .code code := decl.value | throwError "missing compiled body: {decl.name}"
        let counts ← IO.mkRef ((0, 0) : Nat × Nat)
        code.forM fun node => do
          if let .let binding _ := node then
            if let .const name _ _ := binding.value then
              if name == ``preparePlacement then counts.modify fun (p, w) => (p + 1, w)
              if name == ``acceptWaits then counts.modify fun (p, w) => (p, w + 1)
              if [``PreparedPlacement.height].any (·.isPrefixOf decl.name) &&
                  [``preparePlacement, ``acceptWaits, ``assign, ``assignHeights, ``kahn].any
                    (·.isPrefixOf name) then
                throwError "prepared lookup rebuilds through {name}"
        let (prepares, waits) ← counts.get
        if decl.name == ``placeWith && prepares != 1 then
          throwError "placement calls prepare {prepares} times"
        if decl.name == ``preparePlacement && waits != 1 then
          throwError "preparation calls wait analysis {waits} times"
        logInfo m!"{← ppDecl' decl .mono}"
  for name in selected do
    unless seen.contains name do throwError "no persisted compiler body for {name}"
  logInfo "PASS: placement prepares once; preparation analyzes waits once; lookup reads retained data"
