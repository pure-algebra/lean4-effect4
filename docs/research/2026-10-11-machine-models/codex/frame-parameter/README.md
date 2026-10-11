# Frame rules with an explicit state parameter

The existing frame-rule generator now accepts a named state parameter.
It retains later parameters when updating a record field.
The default syntax still selects the final parameter.

Base: `f821dd533`.
Changed source: `src/Effect4/Laws/Auto/Frames.lean` and `Test/Audit/FrameRules.lean`.
Role: proof tooling for the existing guard invariant.
Evidence: checked generated theorems, not machine execution.
Consumer: the R2 guard repair needs an optional active owner after its machine parameter.
The normal guard invariant keeps its default parameter.

## Verification

`LEAN_NUM_THREADS=3 lake build Test.Audit.FrameRules` passes.
The fixture retains a phase parameter and reuses the unaffected clause.
The existing final-parameter fixtures also pass.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-11-machine-models/codex/frame-parameter/Audit.lean` audits the fixture.
It reports 46 declarations within `[propext, Quot.sound]`, with no planned goals or dependencies on goals.

The separate implementation audit reaches `Classical.choice` through Lean metaprogramming.
`ImplementationAudit.log` retains its seven reported declarations.
`Test/Audit/AxiomGate.lean` already admits `Effect4.Laws.Auto.Frames` as audit implementation.
This slice changes no exemption and adds no semantic theorem to that module.
The generated fixture theorems remain within the ordinary ceiling.

Source changes add 27 lines and remove six.
The fixture adds nine lines.
No executable semantics change, so this slice owes no behavior gate.
The R2 runtime and its full law build remain separate, unfinished work.
