# g309: existing inference boundary exposed by complete annotation

Source-only review at HEAD ad447a54aeaab0a83b14f59dcfcac355a1162b63 plus the active service-identity patch. No compiler, generator, runtime execution or repository edits. The existing corpus reports are evidence produced by the parent, not independently rerun here.

## Finding

This is a preexisting loss of the fiber's answer/error precision, newly exposed as a shipped-module diagnostic by retaining the complete annotation. The retained base row already refused A because the actual type contains unknown. Its emitted module used to be compiler-clean because a nonempty requirement row caused declarationType to omit the entire annotation (base Print.lean70–81). Current full annotation checks the expected fiber payload and raises TS2375. Do not describe that diagnostic as preexisting, but do describe its underlying inferred unknown payload as preexisting.

Current corpus-check/types.json records actual A=Fiber<unknown,unknown>, expected A=Fiber<number|Context<unknown>,number>; E=never and R=Scope.Scope both compare exactly. Both actual and expected A contain unknown, so the existing oracle still refuses that axis. g309's expression contains no ordinary service-key construction; the new literal-key identity mechanism is not what loses these payload types. Runtime and synchronous observations remain the same missingService failure on both faces.

## Exact source route

- Both generated/inferred/g309.ts line5 contain the same initializer. It forks a suspended match over Effect.fail("hi"): onFailure returns Effect.context(), while onSuccess calls Deferred.await(a0). An outer onExit also returns Effect.context(). Only generated/g309.ts adds the expected three-slot annotation.
- Effect.fail has answer never (vendor Effect.ts2123). matchCauseEffect passes its input answer A to onSuccess and unions branch answers/errors (Effect.ts10996–11002; installed dist/Effect.d.ts10147–10151). Thus the success binder for this input is bottom/never.
- Deferred.await is generic <A,E>(self: Deferred<A,E>) => Effect<A,E> (vendor Deferred.ts173; installed dist/Deferred.d.ts147). A bottom argument supplies no informative Deferred payload. The source-based inference explanation is that this uninstantiated call contributes unknown answer/error, propagated by suspend (Effect.ts1564–1566) and forkScoped's conditional extraction (Effect.ts17128–17143). The parent’s actual inference report corroborates the outer result, but this review did not separately compile each inner expression.
- Lean deliberately checks both branches. Checker.lean163–168 gives the success branch the body's .never answer, joins both branch results, then forkScoped wraps that known result in .fiberOf (335–338). Ty.sub .never any=true (Ty.lean714). The native deferredAwait row nevertheless fixes the request to Deferred<number,number>, answer nat, error nat, and currently supplies no target type arguments (Native.lean205–207). getContext returns the fixed Ty.context with no requirement (Checker.lean381); its rendered Context<unknown> remains a separate intentional oracle boundary.

## Smallest candidate repair, and scope

Before a general type-directed emission redesign, test one existing mechanism: use NativeOp.deferredTypeArgs=["number","number"] (Native.lean97) in deferredAwait's row.typeArgs, as deferredMake already does (190–192). PrintLeaf.lean219–225 already renders those arguments, and the reader consumes the row's declared arguments. That would transmit the native row's already-fixed payloads even when the input is never. It changes no runtime instruction and needs no cast or omitted annotation.

This is a candidate, not a checked repair: compile the same inferred g309 expression and an ordinary Deferred<number,number> control to establish whether it is sufficient through context/match/fork inference. It is a native-row target-instantiation change, beyond the service-identity files, and reaches profile generation, corpus output and row-call reader controls (the existing E4-CHECK-CE-013 explicit-argument mechanism). Keep it separate unless the coordinator deliberately includes that scope. If it does not suffice, a separate type-directed call/continuation instantiation change is needed; retain the complete annotation and named diagnostic in this slice. Do not weaken unknown-value rejection or report the newly visible TS2375 as agreement.

## Retained rows

Base ad447a54:

    g309	no	yes	decl	clean	agree	agree	die [{"die":"missingService"}]	die [{"die":"missingService"}]	started 0,exited 0 die	started 0,exited 0 die	refused	same failure reasons and payloads; types refused: unresolved-unknown/A: actual A contains unknown

Current report:

    g309	no	yes	decl	errors	agree	agree	die [{"die":"missingService"}]	die [{"die":"missingService"}]	started 0,exited 0 die	started 0,exited 0 die	refused	same failure reasons and payloads; tsc: error TS2375: Type 'Effect<Fiber<unknown, unknown>, never, Scope>' is not assignable to type 'Effect<Fiber<number | Context<unknown>, number>, never, Scope>' with 'exactOptionalPropertyTypes: true'. Consider adding 'undefined' to the types of the target's properties.; types refused: unresolved-unknown/A: actual A contains unknown

## Read-source hashes

- `harness/truth/corpus-check/inferred/g309.ts`: `08fa65c31d14a32395d77ec5b8cc9f572d36a967c78f1256513ad93ef7af2948`
- `harness/truth/corpus-check/generated/g309.ts`: `6202fd22b44601fce6c49ac9fdd9af74850c1d1de24fe9aca7f49cf9377debdf`
- `src/Effect4/Program/Checker.lean`: `dccbb27dd2526566ad7625f127b72b2de943ea6200715fca61f02c60d5f2aa02`
- `src/Effect4/Program/Native.lean`: `5e4ee526c563318a5cd7ebdf1f6dd6f18ef0c5fa6625c3680967611f08b4a857`
- `src/Effect4/Codegen/Print.lean`: `f80b4a7119af62904dafc4ad701bcbea0cc89d833a2a0e2411839a118b972596`
- `vendor/effect-4.0.0-rc.112/src/Deferred.ts`: `78b5d3cd2ad37f9e4f8ebaf465c9375bb982a00bd22a9f3d50ed02e0cb65f0e9`
- `vendor/effect-4.0.0-rc.112/src/Effect.ts`: `92372a76d06a1c66a47319cd67e1f25c8aa0bc81970ea7cfe7fea2253134e718`
- `ts/eff/node_modules/effect/dist/Deferred.d.ts`: `d12e03fe6a9d0b096b162ac7a0d67ea7674d5983754bc1273b191050f995f734`
- `ts/eff/node_modules/effect/dist/Effect.d.ts`: `3d090d110d4563a1d297de7bd0a2ae8039dd075319798d7623c6a88b5eba78ec`

## Subsequent compiler probe: candidate is insufficient

The parent ran pinned tsgo 7.0.0-dev.20260629.1 on the original emitted declaration and an isolated copy with only `Deferred.await<number, number>(a0)`. Both reject with TS2375. The latter recovers number payloads but reveals `Context<never>` versus the declared `Context<unknown>` in the fiber answer. Thus the suggested one-row change is **not** a complete repair. No production row or context representation was changed. This supports a separate context/type-instantiation slice under DI-76(c); do not present the candidate as ready to land. Commands and diagnostics: `g309-probe-results.json`.
