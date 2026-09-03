import Effect4.Concurrency.FiberFamily

/-!
# `Fibers` handler kernel dependency report

Packet M3. The family declares no theorem: it is a signature, a first-order
projection of a two-fiber run, and the traced face that renders it. What this
report is for is the *ceiling*: the projection and its emitter must sit inside
`propext` and `Quot.sound`, so that no golden of `generated/traces/fiber/` is
underwritten by `Classical.choice` — the family lives under `Effect4/` and is
audited by `#effect4_axiom_gate` like any other module there, with no
exemption.

Every declaration listed below is authored in
`Effect4/Concurrency/FiberFamily.lean`; the `effect_signature` and
`effect_program` elaborators that emit the rest are admitted in the gate's
`targetImplementationModules` as `Effect4.Meta.Derive`, and nothing of their
output is admitted with them.
-/

/-! ## The child bodies and the table -/

#print axioms Effect4.FiberFamily.bodyOutcome
#print axioms Effect4.FiberFamily.FiberTable.start
#print axioms Effect4.FiberFamily.FiberTable.drain
#print axioms Effect4.FiberFamily.FiberTable.interruptAt
#print axioms Effect4.FiberFamily.FiberTable.result?
#print axioms Effect4.FiberFamily.FiberTable.blockOn
#print axioms Effect4.FiberFamily.FiberTable.parentExit
#print axioms Effect4.FiberFamily.FiberTable.liveBodies

/-! ## The handler -/

#print axioms Effect4.FiberFamily.forkAt
#print axioms Effect4.FiberFamily.fibersLive

/-! ## The traced face and the goldens -/

#print axioms Effect4.FiberFamily.fibersTraced
#print axioms Effect4.FiberFamily.fiberRun
#print axioms Effect4.FiberFamily.fiberGoldenLog
#print axioms Effect4.FiberFamily.fiberStuck
#print axioms Effect4.FiberFamily.fiberPrograms

/-! ## The generated signature face

Emitted by `effect_signature`, listed here so the report covers everything a
golden's rows are computed from. -/

#print axioms Effect4.FiberFamily.Fibers
#print axioms Effect4.FiberFamily.Fibers.rows
#print axioms Effect4.FiberFamily.Fibers.Name.spelling
#print axioms Effect4.FiberFamily.Fibers.encodeParam
#print axioms Effect4.FiberFamily.Fibers.encodeAnswer
