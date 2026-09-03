# Contract: the region runner (P-T7, runner half)

Light ceremony by operator ruling D2. Effects pin: v0.5.0 (`c28833b`, regions).

## Frozen surface (`Effect4/Flow/Region.lean`)

| Name | Shape |
| --- | --- |
| `RegionService alphabet M` | `handle : Op → Val → M (Except Val Val)`, `pure : Op → Bool` (the aborting reading) |
| `tableRegionService` | a table service whose family operations may fail |
| `Frame alphabet` | an open region and its releases, latest first |
| `closeFrame`, `unwind`, `fail` | close one region with an exit; close every open region with a failure; end the run failed |
| `regionLoop`, `runRegions`, `runRegionsDefault` | the fuelled loop over a `CheckedRegionFlow` |
| `RunResult.failed` (`Runs.lean`) | a run that ended in a failure after closing every open region |

## Semantics pinned (each row checked on the host under every mask)

- `enter r` logs `enter r` and pushes a frame; `acquire` performs, logs its
  `op`/`answer`, and registers its release on the innermost frame.
- `leave v` logs `leave r (success v)`, runs the releases latest-first, each
  logging `finalizer r (success v)` before its own rows, and continues at the
  region's `continue_` block with `v`; a release failure becomes the exit of
  everything enclosing and the run ends `failed` with the first release failure.
- A failing operation logs `failed`, closes every open region innermost-first
  with `failure e` (`leave`, then `finalizer` per release with `failure e`),
  and the run ends `failed e`; a release failing during that close does not
  replace `e` (`Exit.mergeFinalizer`: the body's cause comes first).
- The reified Scope agrees: `Scope.closeOrder` is registration order reversed
  and `Scope.closeExits` hands every release the same closing exit
  (`Effect4Test/Flow/RegionRunnerContract.lean`).

Host evidence: `generated/traces/flow/regionNested.empty`, `regionTwoFail.empty`,
`regionBothSucceed.empty` agree under every mask at both yield settings. A
fallible release runs in Lean but has no lowering (`E4-TARGET-CE-012`), so
`regionReleaseFails` is a Lean-only receipt. Rows `E4-FLOW-CE-019`, `E4-FLOW-CE-020`.

Refusals (not modelled): a parallel finalizer strategy, a region closed twice,
a finalizer that opens a region (a release is one operation by construction), a
fallible release on the host.

Lifted 2026-09-03 by packet M2: an interrupt cause is modelled, but not by this
runner. `regionLoop` still has no interrupted arm and `RunResult` is unchanged;
`Effect4/Flow/Interrupt.lean` carries a second runner (`runInterrupts`, result
type `InterruptResult`) that answers an interrupt tape at every interruptible
point, defers under a mask, and closes every open region with
`Outcome.interrupted` through this module's own `closeFrame`. So `closeFrame`
and `unwind` are the shared subject — `closeFrame_interrupted_log` is
`closeFrame_log` at the new outcome — and the refusal that remains here is
narrower: *this* runner never produces an interrupt cause, and no release of
either runner reads the interruptor identity (the wire drops it). Rows
`E4-FLOW-CE-022`, `E4-FLOW-CE-023`; contract receipts in
`Effect4Test/Flow/InterruptContract.lean`.

## Acceptance

```text
lake env lean Effect4Test/Flow/RegionRunnerContract.lean
./scripts/check-trace-goldens.sh
./scripts/check-trace-host.sh
```

## M2 boundary amendment, 2026-09-03: request delivery and mask restoration

Independent breaker packet for `E4-FLOW-CE-024` and `E4-FLOW-CE-025`.
This appendix supersedes the earlier M2 claim that delivery at the first
outside point models rc.112 restoration. It does not change the region runner
contract above, and does not itself implement the interrupt repair. The
original interrupt battery and counterexamples are retained unchanged when
this packet is frozen. Their historical extra `decide 1000009 false` row and
identification of masked pending state with `_deferredInterrupt` must be
corrected through this explicit amendment before a later M2 acceptance.

### Ownership and assurance

`RegionFlow`, `CheckedRegionFlow`, `Frame`, `IState`, `InterruptResult`, and
`RegionProgram` retain their existing native owners. The existing interrupt
runner and TypeScript lowering are derived interpretations of those carriers;
this packet adds only private fixture data and finite executable expectations,
with no replacement program, scope, decision, or runtime carrier. The existing
`docs/TRACE-DAG.md` interrupt-denotation and structured-agreement routes own the
semantic and generated-target obligations. A finite pass here closes neither
route, the separate scope-machine simulation, nor runtime coverage. Upstream
TypeScript syntax remains owned by the pinned `Typescript` package, not a
second renderer or raw-source injection inside Effect4.

### Pinned evidence and the challenged behavior

The host reproducer is `harness/trace/interrupt-mask-boundary.mjs`. It reads the
actual generated `flow-fixture.ts`, host `interrupt-tail.ts`, `tracer.ts`,
`atoms.ts`, interrupt golden, and observation masks at historical repository
commit `5b29edb4b33ebf7e7afb28f110dc7119e0ed1fef` using read-only `git show`.
It records all six input digests and writes its experimental variants only to
an operating-system temporary directory. This historical evidence remains
reproducible after production and generated files are repaired; it is not the
future current-tree conformance gate.

The exercised host is Effect `4.0.0-rc.112`, upstream commit
`2600f62f4532026928454dcea8d1c48557b3f942`. The reproducer checks the installed
and vendored `src/internal/effect.ts` SHA-256
`0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`
and executed `dist/internal/effect.js` SHA-256
`269e711472b84dcd04862f11e842acc1095cc5d22948af36cda76e9a9185828e`.
The recorded run used Node `v22.23.2` on macOS arm64. Each of five variants runs
with `maxOpsBeforeYield = 1000000` and `3`, budget `100000`, input `5`, service
state `41`, and interrupt tape `[1000005:true]`. The low-threshold run must
actually yield, the tracer must report no defect, and every observed event
must agree between the two thresholds. These are ten finite host runs, not a
scheduler-quantified statement or a patched-runtime coverage receipt.

At that commit, `harness/trace/interrupt-tail.ts:85-97` withholds the actual
`fiber.interruptUnsafe()` call until its own `masked()` predicate is false.
The emitted `interruptMasked` body at `harness/trace/flow-fixture.ts:627-693`
contains `Effect.scoped`, but no `Effect.uninterruptible`. Thus the old golden
can pass every observation mask even though no runtime request is delivered
under a real mask. The real request occurs at the later outside point.

The pinned runtime provides a different boundary:

- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:574-596`,
  `interruptUnsafe`, stores `_interruptedCause` even while uninterruptible.
  `_deferredInterrupt` is a separate injection latch for a request made while
  the fiber is running and interruptible. In the masked probe that latch stays
  false while the pending cause becomes present.
- The same file at `:4302-4320`, `uninterruptible` and `SetInterruptible`,
  pushes restoration and substitutes `failCause(_interruptedCause)` as soon as
  the flag is restored to true. The pending request is delivered before an
  outside continuation, without a fresh request, tape read, or decision row.
  The restoration continuation applies to both success and failure exits.
- `Effect4/Flow/Interrupt.lean:277-294` instead closes successfully and
  recurses into the outside continuation with pending state. A direct return
  there ignores the pending request. The resource-bearing `maskedReturn`
  witness is admitted, but the historical model returns `done (nat 5)`.

The executable host controls retain the entire observed trace:

| Variant | Actual request and mask | Observed result |
| --- | --- | --- |
| Historical baseline | request withheld inside; fiber remains interruptible | all historical masks pass; 13 rows include the outside decision |
| Direct request, missing mask | request sent while interruptible | body `put` does not run; leave and finalizer see interruption; historical m1 and m2 fail |
| Direct request, real outer mask | request sent while uninterruptible; pending cause retained | body `put` and successful cleanup run; 12 rows omit the outside decision; outcome and m1 pass, historical m2 fails |
| Historical baseline, direct return | request withheld and no outside point exists | successful cleanup followed by successful result: the request is lost |
| Direct request, real mask, direct return | request retained by the runtime | the same successful cleanup followed by interruption |

### Frozen repair obligations

1. Carry `RegionProgram.masked` through both dispatch and structured lowering
   into a first-order scoped skeleton/TypeScript form. The marked region must
   execute as `Effect.uninterruptible(Effect.scoped(Effect.onExit(Effect.gen(body), leave)))`:
   the mask surrounds the scope and its cleanup. Masking only the generator
   restores too early. The pinned `TypeScript.Stmt.scopedGen` cannot currently
   express the outer wrapper; any upstream syntax/renderer extension and pin
   change must follow its own ownership and breaker process. The exact
   mask-capable public syntax is not invented or frozen by this appendix.
2. The host interrupt service must read/log each encountered point and call
   `interruptUnsafe()` whenever that point is answered true, regardless of the
   model mask. Runtime state owns deferral. Withholding the request, weakening
   m2, rewriting observed rows, or asserting only final outcomes is not repair.
   The gate must establish that the answered request was made while
   `fiber.interruptible` was false and that `_interruptedCause` became present.
3. After successful cleanup, if the remaining stack restores interruptibility
   and a request is pending, the interrupt runner must deliver it before
   advancing to the outside block. It must consume/log no extra decision.
   The closing scope and its releases retain the successful exit; enclosing
   unmasked scopes then unwind with interruption. If an outer mask remains,
   pending state stays deferred until that mask is left. An immediate outside
   return must produce interruption, not success.
4. The new `Effect4Test/Counterexamples/Flow/InterruptMaskBoundary.lean` reuses
   `InterruptContract.masked` and freezes the complete corrected trace, the
   direct-return result, and independence from a later true outside tape
   answer. Its five positive controls pass at the historical baseline; its
   final three corrected expectations are deliberately red there. It does
   not freeze the historical wrong answer as a required production behavior.
   The original masked golden and two old battery expectations must be amended
   under breaker review solely to remove the obsolete outside delivery row.
5. The later general claim must also account for nested masks, body failure,
   failed cleanup, retained service state, ordinary decision mismatch and live
   frontiers. This packet directly exercises successful cleanup and unmasked
   interrupted cleanup; it does not determine every combined-cause observation
   on failing masked exits. Those observations and the corresponding general
   proof remain open and must not be silently reduced to success-only meaning.
   The source restoration rule above applies on both exit arms.

### Commands and acceptance boundary

Freeze-time narrow checks (no package build in the breaker process):

```text
lake env lean Effect4Test/Counterexamples/Flow/InterruptMaskBoundary.lean
lake env lean Effect4Test/Flow/InterruptContract.lean
lake env lean Effect4Test/Counterexamples/Flow/Interrupt.lean
node harness/trace/interrupt-mask-boundary.mjs /absolute/path/to/node_modules/effect
```

At freeze, the new Lean file must fail exactly its final three guards; an
isolated copy omitting those three guards must pass. Changing its uninterrupted
return control to expect interruption must fail that control, and restoring
it must pass. The historical host reproducer must pass all ten runs, including
the direct-without-mask negative control. The new Lean file must turn green
after repair, alongside the precisely amended old expectations.

The coordinator's later acceptance also requires the existing generation,
drift, TypeScript and host gates with real runtime delivery at both thresholds:

```text
./scripts/generate-trace-goldens.sh
./scripts/check-trace-goldens.sh
./scripts/check-lowering-types.sh
./scripts/test-lowering-mutations.sh
./scripts/check-trace-host.sh
```

An isolated current-tail run is available through the existing driver without
writing a receipt (set `EFFECT4_PROGRAM=interruptMasked`; repeat with
`EFFECT4_MAX_OPS=3 EFFECT4_EXPECT_YIELDS=1`):

```text
node ../effect4-tools/packages/harness/trace.mjs harness/trace --golden generated/traces/flow/interrupt/interruptMasked.tsv --masks generated/traces/masks.tsv --tail interrupt-tail.ts
```

`scripts/check-trace-patched.sh` currently does not iterate the interrupt-golden
subdirectory or assert masked pending delivery. Its existing frame observations
cannot discharge this amendment. If used for that purpose later, its exercised
inputs and assertions must explicitly include this request/restoration path.

### Acceptance, 2026-09-03 (coordinator)

The runner repair landed in `Effect4/Flow/Interrupt.lean`: a `leave` that
restores interruptibility (the rest of the stack is unmasked) delivers a
pending interrupt immediately, before the continuation, with no fresh point and
no tape read; a `ret` with a pending interrupt is delivered the same way. The
three guards of `Effect4Test/Counterexamples/Flow/InterruptMaskBoundary.lean`
are green and the module leaves the declared red set. The historical masked
expectations (`InterruptContract` golden 2 and the `guarded` counterexample)
are amended as this appendix requires: the `decide 1000009 false` row is gone,
and the identification of the masked pending state with `_deferredInterrupt` is
withdrawn — it is rc.112's `_interruptedCause` under an active mask. A failing
close under a pending interrupt keeps the failure (`E4-RUN-CE-025`).

