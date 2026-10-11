# Shared current-code capability checkpoint

The actual loop top retains the ambient typing relation when it injects a pending interruption.
The original reachable typing endpoint still needs its ambient machine and queue adapters.

Base: `2bb83ca31`, after the approved shared entry premise.
Concept: residual-program-typing, R4 and R9.
Claim: preservation dependency of `typed-state-reachable`.
Reach: current reference code, the existing ordered saved stack, actual context coverage and interrupt provenance.
Evidence: checked shared proofs and an actual loop-top consumer.
This proves no progress, whole-machine history, target behavior or reply admission.

## Shared relations

The existing registration, host and saved-position arrows gain complete object and input parameters.
Their original names remain exact unit-input aliases.
The actual race marker, host and token correlation stays in `RegistrationArrowAt`.
`HostStackAt` and `PositionStackAt` use the existing `Contracts.Path`.
No syntax, world, service table or evaluator is added.

`CodeArrow` generalizes the existing current-code and correlated host-path relation.
`CodeOk` retains its original type-only header through the unit-input instance.
`AmbientCodeOk` supplies the ambient instance and coverage from the actual fiber context.
Strong service membership remains the separate existing `ServiceOk` field.

Shared world transport proves both original and ambient instances.
The ambient getter transports declared service carriers through actual service-table equality.
`AmbientCodeOk.failure_covered` reads the guaranteed failure row from the shared entry proof.
`AmbientCodeOk.runloopTop` uses that same bound at the actual pending-interruption cut.
It keeps the actual context and ordered saved stack.
It does not infer current services from a later successful setter.

## Checks

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Scheduler
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/context-scheduler-audit.lean
```

Result: 489 jobs pass.
The final Scheduler compilation measures 26 seconds.
The audit covers Contracts, Residual, Seq, Context and Scheduler.
Result: 622 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
`git diff --check` passes.

Changed sources: `Typed/Context.lean` and `Typed/Scheduler.lean`.
No Machine source changes or behavior gates occur in this proof dependency slice.
The latest primary consolidation audit remains its 2026-10-11 13:45 section.

## Next consumers

Assembly still instantiates live, readable, parked and queued positions through the type-only aliases.
Its ambient adapters must connect actual entry coverage to every runtime continuation cut.
Source denotation must supply the provider body's row before its typed reader runs.
The provider restores its captured context through the existing compiled finalizer region.
Those connections remain open; this checkpoint does not claim the original endpoint is complete.
