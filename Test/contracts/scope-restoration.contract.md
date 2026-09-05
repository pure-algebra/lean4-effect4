# Scope-close restoration through the existing frame runtime

This packet freezes a local adapter from completed ScopeMachine cleanup to
the real FrameFiber.step. The independent breaker owns this contract, its
battery, axiom report, counterexample file and finite host reproducer. The
separate builder owns `src/Effect4/Machine/ScopeRestoration.lean`.

No carrier is added. ScopeMachine, Scope, Runtime, Prim, PrimInterp, FrameFiber,
FrameStep, FrameEvent, Exit and Cause remain their existing owners. No old
definition or assertion changes. This packet contributes to the existing
Scope/Frame/D4 assurance routes; it closes no general D4 or M2 relation.

## Source policy and admitted observation

The source is `effect@4.0.0-rc.112`, upstream commit
`2600f62f4532026928454dcea8d1c48557b3f942`. The critical pinned anchors are:

- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3779-3828`: close state
  first, fixed original exit for all releases, and the zero/one/many fold.
- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4302-4320`: a nested mask
  adds no restoration frame when already masked; restoring true can return
  the pending failure replacement.
- `vendor/effect-4.0.0-rc.112/src/internal/core.ts:529-548`: the failure
  evaluator skips an answering continuation while interrupted and
  interruptible, including that restoration replacement.
- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:574-596`: the recorded
  pending cause and the separate deferred run-loop latch.
- `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4002-4028`: cleanup
  masking and existing original/cleanup cause combination.

Consequently, successful cleanup can resume into pending interruption
immediately at restoration, before touching an arbitrary outer continuation.
An already failing restored exit follows the failure evaluator instead: the
restoration hook runs, its replacement is skipped, and the original failure
enters the remaining frame step. Arbitrary remaining handlers or cleanup
masks may then act. Do not strengthen this into an unchanged terminal-cause
claim for arbitrary continuations.

The complete event list is observed. A `substituted pending` event records
what the hook returned even when the failure evaluator subsequently skips
that replacement. The success equation returns a running failure primitive,
not a final outcome before all outer cleanup.

## Exact owned surface

The namespace is `Effect4.ScopeRestoration`. Its only new executable
declaration is `resumeClosedScope`. Imports are exactly
`Effect4.Runtime.ScopeMachine` and `Effect4.Runtime.Runtime`.
All implementation helpers are private.

For `κ φ ν τ ε δ ι α σ : Type u` and independently `β : Type v`:

```lean
resumeClosedScope
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (interp : PrimInterp ν τ β ε δ ι α)
  (machine : ScopeMachine.State κ φ β ε δ ι α)
  (fiber : FrameFiber ν τ β ε δ ι α) :
  Option (FrameStep ν τ β ε δ ι α × List (FrameEvent ν τ β ε δ ι α))
```

Its definition is exactly the derived composition:

```lean
(ScopeMachine.restore? machine).map fun exit =>
  FrameFiber.step interp { fiber with current := Prim.ofExit exit }
```

Only current is replaced. Existing continuation stack, mask, pending cause
and deferred latch enter the real step unchanged. No Boolean delivery
oracle, source decoder, alternate runtime evaluator, whole-run receipt or
replayed scope runner is permitted. An unfinished close returns none. Its
caller retains the same residual ScopeMachine and service state; no callback
is fabricated and no interruption is delivered through this adapter.

The explicit service state σ belongs to ScopeMachine.runState and is
distinct from Runtime's thunk alphabet τ. PrimInterp stays an external
argument. The general completion theorem carries the whole FrameStep/event
observation and final service state; it does not add effects to PrimInterp
or claim an interpretation of arbitrary host callback objects.

## Frozen universal obligations

Exact parameter order, universes, hypotheses and conclusions are ascribed
in `Test/Machine/Runtime/ScopeRestorationContract.lean`. Nine public
theorems are required:

| Theorem | Exact obligation |
| --- | --- |
| `resumeClosedScope_unfinished` | Any machine whose phase differs from complete returns none, for every interpreter and fiber. This includes waiting and empty-pending ready states. |
| `resumeClosedScope_complete` | Running the actual stateful close to its existing bound and adapting it gives the same FrameStep/events and final service state as existing closeExitsM, the exact zero/one/many fold, existing restoreAfterFinalizer, and the real frame step. |
| `resumeClosedScope_success_pending` | A successful restored exit under a top SetInterruptible true frame, masked flag, pending full cause and false deferred latch becomes that failure primitive immediately. The arbitrary tail, pending cause, true restored flag and exact popped/ranContAll/substituted events are retained. |
| `resumeClosedScope_failure_pending` | The same boundary with an already failing restored exit equals the actual remaining-tail step on that original failure, with the same three prefix events. No substitute delivery decision or terminal-cause restriction is introduced. |
| `resumeClosedScope_success_no_pending` | With no pending cause, restoration continues the successful exit through the actual tail step and adds only popped/ranContAll events. |
| `resumeClosedScope_already_masked` | Applying existing uninterruptible to an already masked input changes no adapter result. This is a derived composition law, not a replacement owner of masking. |
| `resumeClosedScope_masked_continuation` | A successful close with an onSuccess frame under an outer mask takes the actual interp.contA continuation, retaining the mask, full optional pending cause and arbitrary tail. |
| `resumeClosedScope_failure_cleanup` | A failed original exit and actual failed cleanup result enter the real frame step with existing Cause.combine applied to both causes. |
| `resumeClosedScope_success_cleanup_failure` | A successful original exit followed by actual cleanup failure follows the failure-pending tail-step equation; pending interruption cannot overwrite the cleanup failure at that restoration frame. |

The two concrete restoration-arm equations explicitly require a false
deferred latch and the stated top frame. These are the emitted-scope
profile, not an assertion about all runtime checkpoints. The general adapter
and completion theorem quantify over arbitrary fibers, including a true
deferred latch. The battery separately checks that latch's existing meaning.

There is no successful-release, nonempty-cause, positive-budget, pure-service
or infallible-service restriction on the general close-completion equation.
Full causes include failures, defects, interrupts, annotations, duplicates
and empty causes. The original ScopeMachine prefix/completion proofs remain
the owners of actual registration order, captured replies and service state
before failure. The adapter never reconstructs captures from a final cause.

## Independent attacks and finite host evidence

`Test/Counterexamples/Machine/Runtime/ScopeRestorationBoundary.lean` imports
only existing ScopeMachine and Runtime. It remains executable when the new
adapter is absent. Stable new rows are:

- `E4-RUN-CE-025`: `pending_does_not_replace_cleanup_failure` and
  `overwrite_failure_is_observably_wrong` retain cleanup failure at the
  restoration boundary rather than replacing it with pending interruption.
- `E4-RUN-CE-026`: `outer_cleanup_retains_delivered_interrupt`,
  `dropping_outer_cleanup_is_observably_wrong` and
  `outer_cleanup_receives_actual_outgoing_exit` retain the actual outgoing
  inner exit, both outer responses and their final service state.

The IDs 022–024 remain reserved for the earlier live-stack packet.
Existing FLOW-024/025 and RUN-009/011/012/014 remain unchanged references
for actual requests, immediate restoration, exact singleton policy, handler
skipping and masks. Named candidate controls reject delayed restoration,
premature completion of a paused close, overwriting failure, dropping outer
cleanup, escaping an outer mask and treating singleton empty failure as a
multiple-exit fold.

The two-scope witnesses obtain the outer input from the actual inner
FrameStep's exit view and carry the inner close's actual service state.
They do not substitute a predicted inner outcome. Captured duplicate reasons
remain visible even when existing Cause.combine deduplicates the restored
cause. A singleton empty failure takes the failure arm; multiple empty
failures can fold to void and therefore take successful restoration.

`harness/trace/scope-restoration.mjs` accepts an explicit installed package
directory, checks the package version and all four source/runtime digests
before importing executable Effect code, and checks both vendored sources.
It makes real interruptUnsafe requests while the fiber is masked, observes
the pending cause and deferred latch, and uses the terminal fiber observer.
No request is withheld, trace row rewritten, or expected cause substituted.

The 20 configurations run at thresholds 1000000 and 3: 40 finite runs, with
16 successful-release, 16 JavaScript-only fallible-release and eight legal
release-defect runs. Two runs also have body defects outside the current
RegionService result type. Fallible release callbacks remain outside public
acquireRelease's never-error signature and current target admission; legal
release defects are identified separately. Neither class proves a target
admission or general host bridge. Complete reason order, each scope's fixed
closing exit, callback order, actual state, between-scope continuation and
terminal outcome are checked.

## Verification and trust

```text
lake env lean Test/Counterexamples/Machine/Runtime/ScopeRestorationBoundary.lean
lake env lean Test/Machine/Runtime/ScopeRestorationContract.lean
lake env lean Test/Machine/Runtime/ScopeRestorationAxiomReport.lean
node harness/trace/scope-restoration.mjs /path/to/node_modules/effect
```

Allowed transitive axioms for all new public and private declarations,
including every battery helper, are only propext and Quot.sound. No sorry,
new axiom, Classical.choice, native_decide or unsafe escape is admitted.
The builder preserves this packet. Root owns imports, graph/status wiring,
generated refreshes, package gates, final review and production integration.

The existing atomic PrimInterp.finalizerExit boundary remains explicit.
This adapter does not implement arbitrary finalizer programs, registration
or region compilation, source fuel/tape embedding, asynchronous scheduling,
parallel scope execution, general frame simulation or M2 host equivalence.

### Freeze receipt, 2026-09-03

The coordinator approved the exact interp-first adapter and all nine
polymorphic theorem statements before packet writing. The inspected
repository base during final validation was
`1ca39de8bd69e6cb0a18a5e817dc0756703934b7`, Lean v4.33.1.

| Existing owner | SHA-256 |
| --- | --- |
| src/Effect4/Machine/Frames.lean | f51ad546ce01022624f1d871dd63bb31b99ba87d2e076293b78429a94c887e33 |
| src/Effect4/Machine/ScopeMachine.lean | 1189173bca2b6b76e114bc178d1945463e0e862e0faca3d0ed91cf04ddb95979 |
| src/Effect4/Machine/Scope.lean | b54b62b214b3f3e2f764000305c3f2dacdc8d6ce5771444d6c7400d3d982a9d5 |
| src/Effect4/Machine/Exit.lean | a4a4c024ad54a8ab6e52acc1493183349bb532e668af0ed7c2512fa134161383 |
| src/Effect4/Machine/Cause.lean | fc7d008f2955a5ea812717a77e2f3e3d187980c924fc0cb25d5014644c7f7196 |

Source/runtime digests, relative to the installed package:

| File | SHA-256 |
| --- | --- |
| src/internal/effect.ts | 0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0 |
| dist/internal/effect.js | 269e711472b84dcd04862f11e842acc1095cc5d22948af36cda76e9a9185828e |
| src/internal/core.ts | 233b7a1fb3a53b9f49f63c01f810052cb174cc13742f52ea2e8bd482f302fd11 |
| dist/internal/core.js | 00a904f9f06154abb87daa77956475567de0f154e78fbb27f67f7cf8458123cf |

Scratch preparation and logs are in
`/private/tmp/effect4-scope-restoration-breaker`. Its prepare.py uses the
saved packet and coordinator-approved signature proposal to derive controls,
six single-candidate mutants, exact missing-declaration checks and the
signature shell. Observed results:

- The saved boundary passes all 27 guards and five named witnesses. The
  scratch ownership audit accepts all 41 declarations in that source.
- ExistingMeaning checks all 29 future behavior assertions through the
  existing-owner reference composition, and accepts all 45 helper/witness
  declarations. No new production theorem is used by those controls.
- All six mutants exit 1 at exactly their intended candidate assertion.
  The restored controls pass again.
- DeclarationRed fails on exactly the ten absent public names; AxiomsRed
  fails on exactly the nine absent theorem constants. The real packet's
  missing production import is recorded separately.
- SignatureShell elaborates every approved type and future behavior
  expression. Its scratch assumptions are not proofs or repository inputs.
- The independent full saved battery also passes against the coordinator's
  immutable scratch candidate, SHA-256
  `e10e40f2059a43bcd2688c0e5cd4715219bb614e94d2168333792583cf957caa`.
  CandidateFullAudit executes all 56 guards, checks every exact ascription,
  and accepts all 167 current-module declarations, including private helpers
  and anonymous ascriptions, with only propext/Quot.sound. This is scratch
  candidate evidence, not a production implementation or package build.
- The durable host probe passes all 40 runs. Removing the two added
  classification fields gives exactly the earlier 40 observations.
  A changed package version and each of the four independently
  changed source/runtime files are rejected before loading; the restored
  replay matches exactly. The new report SHA-256 is
  `5fdf1c4f8e6d055e191632933018894fef00277032bf6889481e32393e28192d`.

No production, old packet, generated artifact, runtime coverage or shared
import was changed by this breaker packet. No package build or full host gate
ran. The coordinator performs the later implementation and required gates.
