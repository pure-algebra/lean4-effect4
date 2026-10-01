import Effect4

/-! Seat ORGANIZATION probe: how the compiled `Ty.sub` (well-founded, `termination_by`) looks to an
instrument that reads a definition's value: its used constants, and its helpers' used constants. -/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let show1 (n : Name) : CommandElabM Unit := do
    match env.find? n with
    | some (.defnInfo d) =>
      logInfo m!"{n}: uses {d.value.getUsedConstants.toList}"
    | some (.opaqueInfo _) => logInfo m!"{n}: opaque"
    | some _ => logInfo m!"{n}: other kind"
    | none => logInfo m!"{n}: absent"
  show1 `Effect4.Program.Ty.sub
  show1 `Effect4.Program.Ty.sub._unary
  show1 `Effect4.Program.Ty.sub._mutual
