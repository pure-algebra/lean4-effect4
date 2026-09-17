/-! ## Acceptance guards for the generated scope algebra

Appended verbatim by `--append tools/Effect4Gen/guards/scoped.lean` into
`src/Effect4/Program/Scoped.lean`. One row of each binding shape, checked at the level the
table gives it; the universal statements are the per-lift preservation lemmas of
`src/Effect4/Laws/Program/Authoring/Lifts.lean`. -/

namespace Effect4.Program.ScopedGuards

open Effect4.Program

private def v (i : Nat) : Eff Unit := .succeed (.var i)
private def u : Eff Unit := .succeed (.lit .unit)

#guard Eff.scopedAt 0 u = true
#guard Eff.scopedAt 0 (v 0) = false
#guard Eff.scopedAt 1 (v 0) = true
#guard Eff.scopedAt 0 (.bind u (v 0)) = true
#guard Eff.scopedAt 0 (.bind (v 0) u) = false
#guard Eff.scopedAt 0 (.matchCause u (v 0) (v 0)) = true
#guard Eff.scopedAt 0 (.catchIf (.var 0) u (v 0)) = true
-- `select`: the arms are one deeper exactly where the decision binds
#guard Eff.scopedAt 0 (.select (.lit .unit) .bool u u) = true
#guard Eff.scopedAt 0 (.select (.lit .unit) .bool u (v 0)) = false
#guard Eff.scopedAt 0 (.select (.lit .unit) .option u (v 0)) = true
#guard Eff.scopedAt 0 (.select (.lit .unit) .option (v 0) u) = false
#guard Eff.scopedAt 0 (.select (.lit .unit) (.tag "A") (v 0) (v 0)) = true
#guard Eff.scopedAt 0 (.select (.var 0) (.tag "A") u u) = false
#guard Eff.scopedAt 0 (.acquireRelease u (v 1)) = true
#guard Eff.scopedAt 0 (.acquireRelease u (v 2)) = false
#guard Eff.scopedAt 0 (.iterate none (.lit .unit) (.var 0) (.var 1) (.var 0) (v 0)) = true
#guard Eff.scopedAt 0 (.iterate none (.var 0) (.lit .unit) (.lit .unit) (.lit .unit) u) = false
#guard Eff.scopedAt 0 (.iterate none (.lit .unit) (.lit .unit) (.lit .unit) (.var 1) u) = false
-- a layer's body is closed: level 5 outside, level 0 inside
#guard Eff.scopedAt 5 (.provideLayer (.effectDiscard (v 0)) false (v 4)) = false
#guard Eff.scopedAt 5 (.provideLayer (.effectDiscard u) false (v 4)) = true
-- the statement after a `bindYield` is one deeper; after a `yieldDiscard` it is not
#guard Eff.scopedAt 0 (.gen (.cons (.bindYield u) (.cons (.ret (.var 0)) .nil))) = true
#guard Eff.scopedAt 0 (.gen (.cons (.yieldDiscard u) (.cons (.ret (.var 0)) .nil))) = false
#guard Eff.scopedAt 0 (.withFiber (.interruptAll (.lit .unit) (some (.var 0))) : Eff Unit) = false
#guard Eff.scopedAt 1 (.withFiber (.raceAll (.cons (v 0) (.cons u .nil)))) = true
#guard Node.scopedAt 0 (.layer (.effectDiscard (v 0))) = false
#guard Node.scopedAt 7 (.layer (.effectDiscard u)) = true

end Effect4.Program.ScopedGuards
