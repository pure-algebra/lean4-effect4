# Context continuation input proposal

The existing single completion row cannot cover both sides of a provider's setter.
Keep the physical context and its service membership in the existing machine relation.
Treat row indices as guaranteed capabilities at a phase, never as an exact runtime context.

Base: `e4e1f6814` on `codex/symbolic-native-fold`.
The shared signature change below is proposed, not applied.
Automatic approval review rejects that change pending explicit review of its signature.
The existing typed reader, setter, provider entry and scoped frame consumers compile.
The unchanged stack consumer compiles too.
Their build reports 473 jobs.

## Placement

Concept: residual-program-typing and service-context, R4 and R9.
Question: `typed-state-reachable`, under decisions rows 117 and 349.
Role: preservation dependency.
Evidence: checked producer equations and a proposed shared relation change.
Reach: actual source context readers and merged context provider regions.
Limit: these producers do not yet prove configuration preservation or progress.

Row 117 already ratifies the closed requirement row at the initial load.
Row 349 already ratifies the typed reader and context provider region.
This proposal does not reopen either ruling.
It does not admit the retained raw context setter.

## Checked control

The staged `ambient_setContext_typed` producer has a checked direct consumer.
Its successful completion row is the installed context's key row.
`ExitDemandProbe.lean` checks the runtime branch without the staged typing helpers.
Its concrete Scope requirement is absent from the empty entry row.
A failure before that setter cannot use those absent keys.
The staged consumer proves that failure cannot satisfy the same enlarged completion demand.

The probe also reads the actual `Machine.runloopTop` deferred-interrupt branch.
That branch replaces current code with the pending failure and retains the current context.
The same branch can therefore retain an entry context or a context changed by earlier operations.
No statement says every failure restores the entry context.
This is a local runtime control, not a complete admitted-history counterexample.

## Current shared signatures

`FrameArrow` in `src/Effect4/Laws/Program/Typed/Contracts.lean` uses:

```lean
inputOf : Object → Input
restoreInput : Ctx → Input
run : ∀ w', w.leHost w' → ∀ ex,
  Exits w' (inputOf tin) tin ex → kind.hasExitArm ex = true →
  TypedProg w' (inputOf tin) tout (next ex)
```

`ProgramArrow` in `src/Effect4/Laws/Program/Typed/Residual.lean` uses the same projection.
Its guard body completes at `mid`.
Its saved callback starts at `inputOf mid`, independently of the delivered exit.
The original `TypedProg` and `FrameAccepts` remain unit-input instances of these shared relations.

The current ambient position is `EffTy × Requirement`.
`AmbientExit` requires that position's row to be covered by the entry input.
That row cannot simultaneously describe provision success and interruption before provision.

## Proposed signature

Change only the shared completion-input projection:

```lean
inputOf : Object → ExitV → Input
restoreInput : Ctx → Input
run : ∀ w', w.leHost w' → ∀ ex,
  Exits w' (inputOf tin ex) tin ex → kind.hasExitArm ex = true →
  TypedProg w' (inputOf tin ex) tout (next ex)
```

Use `inputOf mid ex` for the program guard's run and skip clauses.
Keep the scoped callback's actual captured-context restoration through `restoreInput previous`.
The unit-input instance uses `fun _ _ => ()`.
It preserves the original type-only theorem statements and constructor meanings.
The existing world transport and closing proofs stay shared-law instances.

The row instance uses `EffTy × Requirement × Requirement`.
The first row bounds success capabilities.
The second row bounds failure capabilities at that phase.
Neither row names the exact physical context.

For the provider setter, success guarantees the merged context's keys.
Failure before that setter guarantees only the already available row.
For its installed body, both exits retain the body's guaranteed available row until restoration.
After restoration, both exits guarantee the captured context's required row.
A failure after earlier writes may retain more services than its guarantee records.

## Existing consumers and construction order

Construct the entry context membership and coverage first.
Read the typed supplied context at its declared carriers.
Prove merged service membership and the body's required coverage.
Construct the body typing only after the actual setter answer provides that coverage.
Construct the restored tail from the captured context and the existing restoration callback.

`Typed.Context.checked_context_arm` consumes the checker rule and the source's service table.
`Typed.Context.native_context_answer` consumes actual context membership and coverage.
`Typed.Context.provider_entry` consumes strong membership for supplied keys and the remaining requirements.
`Typed.Context.ambient_scoped_frame` consumes the actual captured-context restoration hook.

Migrate existing `Scheduler.CodeOk`, `Assembly.LiveCode` and `Assembly.ReadCode` to the row instance.
Keep actual context membership in the existing `preds.ServiceOk` field.
Tie each current entry row to that fiber's actual context coverage.
Keep saved frames ordered through the existing shared `Contracts.Path`.
Keep queued and parked continuations correlated with their existing owners and tokens.

Interruption needs a further explicit bound at the current code position.
Its failure guarantee must be covered by the capabilities actually available at that cut.
The generalized program relation alone does not establish that bound for arbitrary synthetic programs.
Do not infer it from a setter's future success row.
Discharge it from actual source producers and the existing region/restoration structure.
No parallel world, service table or interpreter is proposed.

## Alternatives

An exact `Ctx` completion index distinguishes more values than membership needs.
It also cannot choose one context for a failure occurring at several execution phases.

A relational completion input can quantify over actual available rows at delivery.
This avoids a total projection but changes the shared callback interface more broadly.
Use it if exit-sensitive lower bounds cannot support the actual source producers.

Restricting all failures to the entry row is rejected.
It contradicts the actual loop-top branch after earlier context changes.
Adding assumed runtime coverage to original scenario statements is rejected.
The existing typed preservation proof must establish coverage from the checked source.

## Region and boundaries

The compiler already uses `updateContextAt` and the stored `restoreCtx` callback.
The context bracket remains an instance of existing StackRegion and MaskBracket laws.
Do not add a separate provider command census or a second region law.

`Val.hasTy(contextOf keys)` remains presence-only.
Strong `Fits(contextOf keys)` retains actual declared carriers and fitting service values.
The new reader must use that strong premise.
The target projection remains separately refused until its signature-aware implementation lands.
