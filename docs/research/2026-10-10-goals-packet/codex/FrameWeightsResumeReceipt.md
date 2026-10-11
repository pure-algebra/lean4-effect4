# Saved-frame scalar resume receipt

The shared proof bounds actual value and cause resume by the existing saved scalar sum.
The selected-arm premise remains explicit.

Concept: scope-lifetime-finalization, R11.
Consumers: Atomic cleanup writer debit and Workers release writer debit.
Proof role: preservation.
Evidence status: proved.
Scope: actual FrameFiber.resumeValue and FrameFiber.resumeCause with zero failure current and selected-arm bounds.
The theorem claims no finalizer issuance or history closure.

Base: 53cb3f53d.
Changed module: src/Effect4/Laws/Machine/FrameWeights.lean.

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Machine.FrameWeights` passes 174 jobs.
The changed module takes 2.4 seconds.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FrameWeightsResumeAudit.lean` passes.
The audit reports 87 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.

Atomic full numeric cleanup history remains open.
This proof contains no finite execution or host evidence.
