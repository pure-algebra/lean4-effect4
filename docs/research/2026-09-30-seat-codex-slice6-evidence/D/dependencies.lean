import Lean
import Effect4.Laws.Program.Guard.Driver

open Lean Elab Command

/-- Bounded meta-level dependency walk. Opaque theorem bodies are included explicitly. -/
def closure (env : Environment) (start : Name) : Except String NameSet := Id.run do
  let mut seen : NameSet := ({} : NameSet).insert start
  let mut todo : List Name := [start]
  for _ in [:200000] do
    match todo with
    | [] => pure ()
    | name :: rest =>
      todo := rest
      if let some info := env.find? name then
        let values := (info.value? (allowOpaque := true)).map (·.getUsedConstants)
        let dependencies := info.type.getUsedConstants ++ values.getD #[]
        for dependency in dependencies do
          if !seen.contains dependency then
            seen := seen.insert dependency
            todo := dependency :: todo
  if !todo.isEmpty then return .error "dependency walk exhausted its bound"
  return .ok seen

run_cmd do
  let env ← getEnv
  for root in [`Effect4.Program.Guard.driverContract_of_lift,
      `Effect4.Program.Guard.driverContract] do
    let .ok seen := closure env root | throwError "dependency walk exhausted its bound"
    for expected in [`Effect4.Machine.Lift.driveState_lift,
        `Effect4.Program.Guard.driveStep_invariants] do
      unless seen.contains expected do throwError "positive control failed: {root} -> {expected}"
      logInfo m!"PASS positive: {root} reaches {expected}"
    for forbidden in [`Effect4.Program.Guard.driveState_invariants,
        `Effect4.Program.Guard.reservedKeys_driveState,
        `Effect4.Program.Guard.interruptedAt_driveState,
        `Effect4.Program.Guard.requestOrInterrupted_driveState] do
      if seen.contains forbidden then throwError "old induction still reached: {root} -> {forbidden}"
      if env.contains forbidden then throwError "old induction still declared: {forbidden}"
      logInfo m!"PASS absent: {root} does not reach {forbidden}"
