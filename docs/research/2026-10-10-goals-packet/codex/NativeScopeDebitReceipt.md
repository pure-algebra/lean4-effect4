# Complete native evaluator accounting

Every actual native evaluator branch now satisfies the local release accounting law; whole-history custody remains open.

## Placement

Concept: scope-lifetime-finalization, R11. Claim: `ReleaseCustody.Execution.history`, consumed by the original Workers release bound.
`NativeScopeDebit.enter` accounts for empty scope creation and the actual source continuation.
`close_unsafe` transfers the closed scope's stored credits into its optional cleanup program.
`exit_pop_bound` uses the existing continuation-removal laws.
`exiting` combines that removal with state-first close, retaining the returned cleanup program's exact credits.
`native` composes these clauses with `NativeParkDebit.primitive` at the actual native evaluator.
Its premises name saved-frame sequencing, source ownership, sequential scopes, unique identifiers, fresh scope keys and absent races.
Workers already supplies the source restrictions; command-history closure must supply the reached-state premises.
No local accounting theorem establishes progress, source-use uniqueness or an outside-host result.

## Landing

Base: `81b142b92`, including the checked primitive, timeout and source-opportunity checkpoints.
New module: `src/Effect4/Laws/Program/ReleaseCustody/NativeScopeDebit.lean`.
`Execution` imports the native aggregate; `Effect4.Laws` reaches the integrated source-opportunity action proof.
`Test/All.lean` reaches the integrated timeout evaluator and settle proof.
The existing scenario statements and runtime definitions stay unchanged.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeScopeDebit Test.Dogfood.Scenario.Workers Effect4.Laws Test.Dogfood.Proofs.HostTimeoutSettle`.
Result: successful, 1363 jobs; `NativeScopeDebitBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/NativeScopeDebitAudit.lean`.
Result: the real `Api.Built` reader compiles; 227 declarations audit within `[propext, Quot.sound]`, with zero planned dependencies.
The audit includes both primitive modules, source-opportunity actions, and the three integrated timeout modules.
The status output retains `Execution.history` as open.
`NativeScopeDebitAudit.out` retains the results.
No runtime definition changes; no behavior gate is newly reached.
The final generated proof graph refresh remains due.

## Next

The added machine-base packet starts after this landing.
Its shared interference and frame classifications will serve subsequent history proofs and the requested guard cleanup.
The original fourteen-goal lane retains its landing order.
