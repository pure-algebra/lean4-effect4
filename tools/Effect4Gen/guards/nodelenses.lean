/-! ## Acceptance guards for the generated child lenses

Appended verbatim by `--append tools/Effect4Gen/guards/nodelenses.lean` into
`src/Effect4/Program/NodeLenses.lean`. One constructor of each shape: a program child, a
layer child, a spine, a statement, and the refusals (no such child, the wrong sort). -/

namespace Effect4.Program.NodeLensesGuards

open Effect4.Program

private def e0 : Eff Unit := .succeed (.lit .unit)
private def e1 : Eff Unit := .succeed (.lit (.nat 1))

#guard Node.child (.eff (.bind e0 e1)) 0 = some (.eff e0)
#guard Node.child (.eff (.bind e0 e1)) 1 = some (.eff e1)
#guard Node.child (.eff (.bind e0 e1)) 2 = none
#guard Node.child (.eff e0) 0 = none
#guard Node.child (.eff (.provideLayer (.ref [3]) false e0)) 0 = some (.layer (.ref [3]))
#guard Node.child (.eff (.withFiber (.raceAll (.cons e0 .nil)))) 0 = some (.action (.raceAll (.cons e0 .nil)))
#guard Node.child (.effs (.cons e0 (.cons e1 .nil))) 1 = some (.effs (.cons e1 .nil))
#guard Node.child (.stmts (.cons (.bindYield e0) .nil)) 0 = some (.stmt (.bindYield e0))
#guard Node.setChild (.eff (.bind e0 e1)) 0 (.eff e1) = some (.eff (.bind e1 e1))
#guard Node.setChild (.eff (.bind e0 e1)) 0 (.layer (.ref [])) = none
#guard Node.setChild ((.layer (.merge (.ref [0]) (.ref [1]))) : Node Unit) 1 (.layer (.ref [2]))
  = some (.layer (.merge (.ref [0]) (.ref [2])))
#guard Node.setChild (.eff e0) 0 (.eff e1) = none

end Effect4.Program.NodeLensesGuards
