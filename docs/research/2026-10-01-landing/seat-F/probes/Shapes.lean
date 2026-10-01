import Effect4
import Effect4.Laws

/-! Seat F probe (2026-10-01): the compiled shapes the census reads — `Ty.sub` and its `_unary`, a sparse `casesOn`, `Ty.isFactor`, `Ty.closed`, the fuel walks, the private definitions. -/

open Lean Elab Command

/-- Print the used constants of a definition and of each compiler-made helper it reaches. -/
def showUses (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | some (.defnInfo d) =>
    logInfo m!"{n}: uses {d.value.getUsedConstants.toList}"
  | some (.opaqueInfo d) => logInfo m!"{n}: opaque, uses {d.value.getUsedConstants.toList}"
  | some _ => logInfo m!"{n}: other kind"
  | none => logInfo m!"{n}: absent"


#eval show CommandElabM Unit from do
  showUses `Effect4.Program.Ty.sub
  showUses `Effect4.Program.Ty.sub._unary
  showUses `Effect4.Program.Ty.infer._sparseCasesOn_13
  showUses `Effect4.Program.Ty.isFactor
  showUses `Effect4.Program.Ty.isFactor.match_1
  showUses `Effect4.Program.Ty.closed
  showUses `Effect4.Program.runStmts
  showUses `Effect4.Program.runStmts.yieldOf._mutual
  showUses `Effect4.Program.Sched.walkR
  showUses `Effect4.Program.replayCheckedFrom._unary

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut found : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if isPrivateName n then
      if let some u := privateToUserName? n then
        if u == `Effect4.Codegen.Types.ofNormalized || u == `Effect4.Representation.beq ||
            u == `Effect4.Check.beq || u == `Effect4.Representation.beq._mutual then
          found := found.push n
  for n in found do
    showUses n
    logInfo m!"  isInternal {n.isInternal} isInternalDetail {n.isInternalDetail} user {privateToUserName? n}"
