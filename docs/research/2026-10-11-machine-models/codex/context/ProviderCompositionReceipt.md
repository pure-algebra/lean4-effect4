# Shared provider composition checkpoint

The actual restoring finalizer composes through the existing program arrow.
The provider still needs captured-context ownership and its actual region bracket.

Base: `f18531a2b`.
Concept: residual-program-typing, R4 and R9.
Claim: preservation dependency of `typed-state-reachable`.
Reach: actual getter, setter, guarded callback and restoring finalizer programs.
Evidence: checked shared laws and a compiling positive and negative control.
The owner approves separate success and failure guarantees in `ExitInputProposal.md`.
Decisions rows 117 and 349 bound the source and load consumers.
This checkpoint establishes no machine history, physical context restoration or target behavior.

## Shared laws and consumers

`ProgramArrow.outputMap` transports result membership and entry guarantees in the existing carrier.
`typedProg_widen` and `ambientProg_widen` consume it.
`ProgramArrow.guardBind` composes the existing guarded program and its saved callback.
`guardBind_typed` and `ambient_guardBind` consume it.
Their original type-only headers remain unchanged.

`ambient_setContext_guarantees` covers the actual setter at entry and returned cuts.
The failure guarantee must hold before evaluation and after the setter.
`ambient_restore_finalizer` types the actual `finalizerR` that restores the captured context.
`ambient_onExit_restore` composes it with the actual body.
The service membership premise and restoration coverage remain explicit.

The getter input projection reads the actual decoded answer's key row.
This refines proof input without changing the physical context.
`CapturedContextProbe.lean` uses the same `ProgramArrow` with a completion-dependent input.
Its getter producer proves the captured context covers the callback's guarantee.
Its negative control shows an ordinary static completion position does not imply that value correlation.
The control is conditional proof evidence, not an admitted closed-program counterexample.
The next slice adds that completion index to the existing ambient position.
It adds no stored program, world or evaluator.

## Checks

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.Typed.Scheduler Effect4.Laws.Program.Typed.Stack Effect4.Laws.Program.Typed.Adequacy
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/CapturedContextProbe.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/context-scheduler-audit.lean
```

Result: 489 build jobs pass.
The last compilations measure Context 9.7 seconds, Adequacy 12 seconds, Stack 9.6 seconds and Scheduler 7.6 seconds.
The probe passes without messages.
The audit covers Contracts, Residual, Seq, Context and Scheduler.
Result: 631 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
`git diff --check` passes.

The three source files add 187 lines and remove 31 lines before this receipt.
The replaced result and guarded-composition cases now use shared laws.
No Machine source or behavior gate changes in this dependency slice.
The primary consolidation audit's latest section is 2026-10-11 15:40.

## Integration

Apply this checkpoint after `f18531a2b` and the earlier source and shared-entry commits.
Changed sources: `Typed/Residual.lean`, `Typed/Seq.lean` and `Typed/Context.lean`.
The root-owned `Codegen.Types` refusal and borrowed `Contracts/FramePath.lean` are excluded.

The original ambient reachable endpoint remains open.
It needs actual source body coverage and current, saved and queued adapters.
The provider bracket must instantiate the existing `MaskBracket` and `StackRegionRun` laws.
Physical restoration and captured value ownership are separate premises of that instance.
