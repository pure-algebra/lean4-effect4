# Captured context completion checkpoint

The getter's saved callback now retains its returned context's service coverage.
It uses a completion case in the existing program and frame arrows.

Base: `3934dd4b2`.
Concept: residual-program-typing, R4 and R9.
Claim: preservation dependency of `typed-state-reachable`.
Reach: actual native getter, captured callback, ordinary completion positions and actual loop-top interruption.
Evidence: checked producer, callback reader and negative control.
The owner approves this completion-dependent input at the existing arrow boundary.
`ExitInputProposal.md` records the approved success and failure guarantees.
This checkpoint proves no full machine history, physical restoration or target behavior.

## Existing completion index

`AmbientPosition.result` retains the original type, success row and failure row.
Its tuple coercion preserves the ordinary spelling and its exit judgment.
`AmbientPosition.capturedContext` records the getter's guaranteed row.
At success, `ambientInput` reads the actual decoded answer's key row.
At failure, it retains the entry guarantee.
`AmbientBounds` additionally retains the guaranteed row for the captured case.
The other case retains its original bound.

`ambient_captureContext_typed` constructs the actual getter through the same `ProgramArrow`.
`ambient_captured_context` reads strong service membership and coverage at its saved callback.
It uses the existing value membership and exact context decoder.
No syntax, world, evaluator or configuration relation is added.
The original shared path still composes saved frames.

`ambient_entry` reads the failure bound from both completion cases.
`AmbientCodeOk.runloopTop` consumes it when the actual machine injects an interruption.
Ordinary iterator, loop and asynchronous-finalizer hooks retain their type-only protocols.
They reject the captured-only position instead of claiming they preserve returned-value ownership.
`ambientProg_widen` applies to ordinary result positions.
Its helper domain now names that restriction because a captured completion needs its own value correlation.
The original `typedProg_widen` statement remains unchanged.

## Controls and checks

`CapturedContextReader.lean` reads a concrete service key from the captured callback coverage.
Its negative control rejects a captured context missing the promised row.
The same context remains possible under the ordinary coarse result judgment.
The control is conditional proof evidence, not an admitted closed source counterexample.
`CapturedContextProbe.lean` retains the earlier experimental instance as historical evidence.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.Typed.Scheduler
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/CapturedContextReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/context-scheduler-audit.lean
```

Result: 489 build jobs pass.
The last Context compilation measures 59 seconds; Scheduler measures 81 seconds.
The reader passes without messages.
The audit covers Contracts, Residual, Seq, Context and Scheduler.
Result: 668 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
`git diff --check` passes.
The three source files add 105 lines and remove 25 lines before this receipt.
No Machine source or behavior gate changes in this slice.

## Integration and remaining consumers

Apply this checkpoint after `3934dd4b2`.
Changed sources: `Typed/Residual.lean`, `Typed/Context.lean` and `Typed/Scheduler.lean`.
`MigrationInventory.md` lists the exact source, runtime and target consumers still requiring migration.
The next consumer is the actual provider's identity, setter and restoring-finalizer protocol.
The original ambient reachable endpoint remains open.
Its provider bracket must instantiate the existing `MaskBracket` and `StackRegionRun` laws.
Captured value ownership and physical restoration remain distinct premises.
