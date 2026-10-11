# Open context reader boundary

The admitted open reader returns an empty context in the default native run.
That successful value fits no world at the reader's promised nonempty context row.
No outward M6 statement changes in this checkpoint.

Base: `943985f53` on `codex/symbolic-native-fold`.
Evidence: `OpenReaderBoundary.lean` in this directory.
Command: `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/OpenReaderBoundary.lean`.
Result: exit zero.
The kernel checks the native execution equation using `kernel_rfl`.
Admission and type guards pass at the actual native source readers.
The successful value cannot fit the promised row at any typed world.
This is a finite native execution control with a universal value-boundary proof.
It is not an outside behaviour comparison or a full M6 falsifier theorem.

## Source and execution

The source is `.withFiber (.context keys)` at one declared native nat service key.
The checker returns answer `contextOf keys`, error `never`, and requirements `keys`.
The requirement row is open.
`admitProgram` accepts the source.
`Provision.runNative` uses the existing native compiler, empty stores and empty context.
It returns `.success (Val.context emptyCtx)`.
The promised key is absent from that context.

This reader supplies no context term and invokes no raw setter.
It does not bypass closed-row admission or an actual supplied-environment premise.
No new stable counterexample identifier is allocated here.

## Outward statement affected by extending the source domain

`reachable_typed_admitted` in `src/Effect4/Laws/Program/Typed/AdmittedSource.lean` currently states:

```lean
theorem reachable_typed_admitted {program : NativeEff} {app : SigApp}
    (a : AdmittedProgram program app) (fuel : Nat) (tape : List Api.Decision)
    (admitted : AdmittedTape a.source a.ty fuel tape) :
    ∃ w, MachineTyped a.source a.ty w (replayR program fuel tape).machine
```

Its initial run supplies `loadR`'s empty context.
`AdmittedTape` restricts host answers, not initial ambient service coverage.
`admittedTape_of_noHostAnswer` admits every answer-free tape.
The current statement carries no closed-row or ambient-service premise.
Its extension to the new reader domain therefore needs the owner to settle that initial boundary.
This receipt does not alter the statement or add a replacement goal.

`m7_admitted` already requires `closedRow`.
The open reader does not meet that premise.
No change to M7's scope follows from this control.

## Ruling and shared repair seam

Decisions row 349 ratifies option A.
It names a context reader whose type carries its row and a context provider region.
The source is `docs/research/2026-10-11-machine-from-the-base/context-transformers.md`, sections 4 and 6.
Section 4 preserves the actual context getter and compiles the provider through `updateContextAt`.
Section 6 treats provision as an action on ambient service keys.
The parameter's requirement must be met when its source site starts.

Decisions row 117 and the research note's section 3 already identify the missing per-position presence clause.
`PointTyped` currently records source typing, value environments, completed views and passed-program stacks.
It records no actual current context.
`preds.ServiceOk` currently establishes typed live values for present services.
It establishes no promised-key coverage.
`fiberPre` fixes `.getContext` at the coarse context certificate.
Its postcondition likewise supplies coarse context membership.
No coercion from that certificate to `contextOf keys` is valid.

The minimal repair extends these existing ambient and getter relations.
It must preserve the actual service declarations, fitting values and supplied keys.
The source consumer is the context reader arm of `Typed.Denotation`.
The provider consumer uses supplied coverage within the existing region.
Restoration remains an instance of StackRegion/MaskBracket.
No second evaluator, source carrier or per-provider command census is proposed.

Proof placement: residual-program-typing, R4 and R9.
Role: control for the typed getter and ambient-coverage migration.
Remaining obligation: the owner resolves the outward initial-coverage boundary before its scope changes.
