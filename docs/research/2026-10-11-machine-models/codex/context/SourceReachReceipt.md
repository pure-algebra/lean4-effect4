# Typed context source reach

The open source denotation relation needs actual ambient coverage for typed context readers.
The unit-input arrow laws retain their original statements.
The closed reachable claims retain decisions row 117's closed-row premise.

Base: `9915c36f7`.
Concept: residual-program-typing, R4 and R9.
Claim: preservation dependency of `typed-state-reachable`.
Role: preservation.
Evidence: checked source provider producer and the retained open-reader control.
The provider producer supplies no whole-history or physical restoration theorem.
No target behavior gate result is claimed.

## Existing source reach

`ChildDenotes` in `src/Effect4/Laws/Program/Typed/Denotation.lean` currently states:

```lean
def ChildDenotes (root : ProgramSource) (f : Nat) (c : NativeEff) (path : List Nat) : Prop :=
  ∀ (w : World), w.serviceTy = root.sig.serviceTy → ∀ (q : Point) (ty : EffTy),
    q.fuel = f → q.path = path → PointTyped root w q ty →
    TypedProg root w ty (denoteR root.program c q)
```

`withFiber_arm` in that same file currently concludes:

```lean
(hfuel : p.fuel ≠ 0)
(hat : Node.at_ (.eff root.program) p.path = some (.eff (.withFiber a)))
(hpt : PointTyped root w p ty) :
TypedProg root w ty (denoteR root.program (.withFiber a) p)
```

`PointTyped` supplies checker evidence, typed values, completed views and passed-program stacks.
`EnvTyped` supplies value membership for the lexical environment.
Neither relation supplies the current context or its promised-key coverage.
World service declarations identify carriers but do not install runtime values.
The old coarse getter's postcondition cannot supply strong membership at `contextOf keys`.
The new source reader therefore cannot retain this open-point conclusion from these premises alone.

`OpenReaderBoundary.lean` retains the admitted open reader's actual empty-context native result.
That result fits no world at the reader's nonempty promised row.
This is a finite execution control with a universal value-boundary proof.
It is not a refutation of a closed-row reachable claim.

## Approved ambient reach

The existing `ProgramArrow` carries the approved entry and completion inputs.
The source adapter supplies an available row and requires checked requirements to lie within it.
The runtime adapter relates that row to the actual fiber context through `AmbientCodeOk`.
The result retains distinct success and failure guarantees at actual entry cuts.
No service coverage follows merely from a future successful continuation.

`checked_provideContext_reader` in `src/Effect4/Laws/Program/Typed/Context.lean` consumes:

- the actual provider node and successful source checker result;
- the existing lexical `EnvTyped` relation and the evaluated supplied context;
- equality with the source's declared service table;
- inclusion of the checked provider requirement in the available row;
- the actual positive compilation fuel.

It concludes `AmbientProg` for the actual provider denotation and its context-reader body.
The term theorem establishes strong membership of the supplied context at its checked `contextOf` row.
The supplied keys discharge the body requirements through the existing row difference.
The previous context supplies the remaining required keys.
The actual identity branch retains that previous context.
The merge branch uses the existing setter, body and restoring finalizer.
Fuel exhaustion remains a live frontier.
No operation precondition changes to hide missing ambient coverage.

The general `ChildDenotes` migration must use this same ambient input and its existing source evidence.
Current, saved and queued positions must retain their actual correlated context coverage.
The type-only `TypedProg`, `FrameAccepts` and shared unit-input laws remain unchanged.

## Closed reach and deferred targets

`reachable_typed_admitted` in `Typed/AdmittedSource.lean` carries `closedRow` under row 117.
Its original machine observation remains unchanged.
`m7_admitted` retains its existing closed-row and answer-free premises.
Row 349 approves the source typed reader and provider region.
`ExitInputProposal.md` records the approved success and failure guarantees.
No approval remains pending.

The provider bracket must instantiate existing `MaskBracket` and `StackRegionRun` laws.
Captured context membership and physical all-exit restoration remain distinct obligations.
`MigrationInventory.md` names the remaining source, runtime and generated consumers.
The central context target projection remains signature-aware and deferred.
The type-interface note keeps `Ty` as the hub and distinguishes strong membership from target widening.
This slice does not expand into its numeric or TypeScript findings.

## Checked checkpoint

Changed source: `src/Effect4/Laws/Program/Typed/Context.lean`.
It adds `ambient_updateContext_provide` and `checked_provideContext_reader`.
Both consume the existing program arrow and its checked smaller producers.
`ProviderSourceReader.lean` applies the source theorem to a real lexical slot and context-reader body.
Its `EnvTyped` premise supplies the actual context value's strong membership.
It does not claim that this open lexical source is an admitted closed program.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.Typed.Scheduler
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/ProviderSourceReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/context-scheduler-audit.lean
```

Result: 489 build jobs pass.
Context compilation measures 32 seconds; Scheduler compilation measures 46 seconds.
The direct source reader passes without messages.
The audit covers Contracts, Residual, Seq, Context and Scheduler.
Result: 686 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
The source adds 149 lines and removes zero lines.
It adds no evaluator or command case analysis.
`git diff --check` passes for the changed source.
Apply this checkpoint after `9915c36f7`.
No Machine source, root import, generator input or target projection changes in this checkpoint.

## General provider arm checkpoint

Base: `bad99e8e2`.
`checked_provideContext_arm` handles any checked provider body through the same ambient arrow.
Its smaller premises type the actual child and the actual immediate exit.
The child premise consumes the body's checker result and its required-row inclusion.
It retains the outer available row as both completion guarantees.
The immediate premise establishes only the shortcut exit's value judgment.
The outer pure constructor additionally retains its actual entry bound.
These premises are inputs from the source induction and `inlineYield_typed`.
They are not new premises of any closed reachable claim.

The actual context-reader consumer now applies this general arm.
It discharges the immediate branch because that reader has no immediate exit.
It constructs its live child using declared carriers and the installed merged row.
The source checker-to-member proof now occurs once.
No duplicate source carrier or private evaluator pass is added.
The broader `inlineYield_typed` proof needs the new provider recursion case.
That value-only helper can retain its original header.
The broader open `ChildDenotes` relation still needs its approved ambient migration.

The same three check commands above pass again.
Result: 489 build jobs pass; Context measures 88 seconds and Scheduler measures 110 seconds.
The source reader passes without messages.
The audit reports 687 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
The source adds 78 lines and removes 48 lines relative to `bad99e8e2`.
`git diff --check` passes for the source.
Apply this checkpoint after `bad99e8e2`.
