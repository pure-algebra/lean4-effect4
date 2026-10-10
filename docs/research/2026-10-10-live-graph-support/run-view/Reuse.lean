import Tools.View.Run
import Lean
open Lean Compiler LCNF

-- Inspect compiled calls. This checks preparation placement, not a cost bound.
run_elab do
  let env ← getEnv
  let targets := [``Tools.View.Run.prepare, ``Tools.View.Run.framePrepared,
    ``Tools.View.Run.framesBuilt]
  let mut seen : Array Name := #[]
  let mut preparations := 0
  let mut foundEntry := false
  let mut foundLoop := false
  for i in [:env.header.modules.size] do
    for decl in monoExt.getModuleEntries env i do
      if targets.any (·.isPrefixOf decl.name) && !seen.contains decl.name then
        seen := seen.push decl.name
        let .code code := decl.value | throwError "missing compiled body"
        let callRef ← IO.mkRef (#[] : Array Name)
        code.forM fun node => do
          if let .let binding _ := node then
            if let .const name _ _ := binding.value then callRef.modify (·.push name)
        let calls ← callRef.get
        if decl.name == ``Tools.View.Run.framesBuilt then
          foundEntry := true
          preparations := (calls.filter (· == ``Tools.View.Run.prepare)).size
        if (``Tools.View.Run.framesBuilt).isPrefixOf decl.name &&
            decl.name != ``Tools.View.Run.framesBuilt then
          foundLoop := true
          if calls.contains ``Tools.View.Run.prepare then
            throwError "recursive frame helper prepares again: {decl.name}"
        if (``Tools.View.Run.framePrepared).isPrefixOf decl.name then
          if calls.any fun n => [``Tools.View.Run.prepare,
              ``Tools.View.Program.sessionPage, ``Tools.View.Program.codePanel].contains n then
            throwError "dynamic frame prepares again: {decl.name}"
        logInfo m!"{decl.name}: {calls}"
  unless foundEntry && foundLoop && preparations == 1 do
    throwError "preparation count {preparations}, entry {foundEntry}, loop {foundLoop}"
  logInfo "Compiled frame entry prepares once; recursive and dynamic frame helpers do not."
