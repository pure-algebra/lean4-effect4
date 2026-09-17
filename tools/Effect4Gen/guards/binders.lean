/-! ## Acceptance guards for the generated binder table

Appended verbatim by `--append tools/Effect4Gen/guards/binders.lean` into
`src/Effect4/Program/Binders.lean`. The rows are `tools/Effect4Gen/binders.json`'s; these
pin the projection at one constructor of each shape so a regenerated table that dropped a
row fails here before any consumer notices. -/

namespace Effect4.Program.BindersGuards

open Effect4.Program

private def e0 : Eff Unit := .succeed (.lit .unit)

#guard Node.binders (.eff (.bind e0 e0)) 0 = 0
#guard Node.binders (.eff (.bind e0 e0)) 1 = 1
#guard Node.binders (.eff (.matchCause e0 e0 e0)) 2 = 1
#guard Node.binders (.eff (.acquireRelease e0 e0)) 1 = 2
#guard Node.binders (.eff (.whileLoop (.lit .unit) (.lit .unit) (.lit .unit) e0)) 0 = 1
#guard Node.binders (.eff (.suspend e0)) 0 = 0
-- `select` binds by its decision: nothing, the some-value, the payload and the rest
#guard Node.binders (.eff (.select (.lit .unit) .bool e0 e0)) 1 = 0
#guard Node.binders (.eff (.select (.lit .unit) .option e0 e0)) 0 = 0
#guard Node.binders (.eff (.select (.lit .unit) .option e0 e0)) 1 = 1
#guard Node.binders (.eff (.select (.lit .unit) (.tag "A") e0 e0)) 0 = 1
#guard Node.binders (.eff (.select (.lit .unit) (.tag "A") e0 e0)) 1 = 1
#guard Node.binders (.stmts (.cons (.bindYield e0) .nil)) 1 = 1
#guard Node.binders (.stmts (.cons (.yieldDiscard e0) .nil)) 1 = 0
#guard Node.closedChild (.layer (.effectDiscard e0)) 0 = true
#guard Node.closedChild (.eff (.bind e0 e0)) 1 = false
#guard Node.childLevel 3 (.eff (.bind e0 e0)) 1 = 4
#guard Node.childLevel 3 (.layer (.effectDiscard e0)) 0 = 0
#guard Node.childLevel 3 (.eff (.suspend e0)) 0 = 3
#guard readerOnlyHeads.length = 2
#guard machineOnlyHeads.length = 5

end Effect4.Program.BindersGuards
