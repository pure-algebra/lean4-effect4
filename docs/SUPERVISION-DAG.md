# Fork and supervision proof DAG

Status: breaker-frozen, RED, 2026-09-02.

This document owns the public type dispositions, exact shape expectations,
and assurance routes for the
[frozen contract](../test/contracts/fiber-supervision.contract.md).
The exact declaration names, types, and theorem statements are owned by
[`FiberSupervisionContract.lean`](../Effect4Test/Concurrency/FiberSupervisionContract.lean).
The 136 law names are also the input to
[`FiberSupervisionAxiomReport.lean`](../Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean).
No production proof receipt is asserted at breaker freeze.

## Source profile and ownership

Source: `effect@4.0.0-rc.112`, upstream
`2600f62f4532026928454dcea8d1c48557b3f942`,
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, SHA-256
`0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`.
The runtime census remains the authority for its row spans and digests.
This packet resumes the old direct-child claim; it introduces no second
supervision design and changes no binary `Race.lean` contract.

The production owner of every name in the next tables is
`Effect4/Concurrency/Supervision.lean`, namespace `Effect4.Supervision`.
These are Effect4-native declarations, not moved Foldlab declarations.
Canonical FiberId, FiberState, FiberStatus, CleanupState, InterruptMask, Cause,
Reason, ReasonAnnotations, Exit, and Scope remain at their existing owners.
Standard ULift embeds the passive scope key and finalizer alphabets. No
canonical carrier is copied or shadowed. The root integration mirrors these
native dispositions into `PORT-MANIFEST.md` under its existing claim.

## One graph and necessary leaves

```text
SUP-L-MASK    SUP-L-OBSERVER    SUP-L-SCOPE
      \             |              /
       \            v             /
        SUPERVISION-PG-RC112
        canonical views and observed-world admission
                   |
        fork / observation / scope boundaries
                   |
        WaitStep + WaitRuns / RaceStep + RaceRuns
                   |
        publication and fixed-tape laws
                   |
        counterexamples + trust + declaration census
                   |
        required-open host/continuation interpretation
```

The three finite leaves close with exact shapes and their `cases_receipt`
laws; MaskMode additionally requires its three selection equations. They
link into the single graph rather than receiving independent semantic graphs.
The graph covers controllers over supplied runtime observations. It does not
close host execution, the concurrency category, or a full cutover.

## Complete type and judgment disposition

There are 19 concrete public types and eight public Prop judgments. No public
alias is introduced. Constructors, fields, and compiler-generated recursors
inherit their parent type's owner and route; hand-authored operations and
laws use the API-group and clause rows below. Test witness theorems are owned
by their register rows; their helper data is private test evidence.

| Public type or judgment | Disposition | Relationship and duplicate prevention | Assurance route |
| --- | --- | --- | --- |
| `MaskMode` | native finite leaf | Selects existing InterruptMask; not a second mask carrier | `SUP-L-MASK` |
| `ForkOptions` | native options data | Immediate/daemon/mask inputs to fork boundary; not host closure storage | `SUPERVISION-PG-RC112` |
| `Globals` | native global view | Allocated canonical FiberIds and one shared middleware flag; not per-parent middleware | `SUPERVISION-PG-RC112` |
| `ObserverMode` | native finite leaf | Distinct await-value versus join-effect observations | `SUP-L-OBSERVER` |
| `Subscription` | native observer handle | Named cancellation key and ObserverMode; no callback payload | `SUPERVISION-PG-RC112` |
| `Fiber` | native related view | Contains canonical FiberState Exit; exact toFiberState projection, adds boundary metadata | `SUPERVISION-PG-RC112` |
| `Observation` | native result observation | Canonical Exit returned as value or resumed effect; waiting is a keyed frontier | `SUPERVISION-PG-RC112` |
| `StartObservation` | native external decision data | Deferred or full observed Globals/parent/child after immediate execution | `SUPERVISION-PG-RC112` |
| `ForkEvent` | native boundary trace | Scheduled/evaluated/registered order; not Scheduler.Event replacement | `SUPERVISION-PG-RC112` |
| `ForkResult` | native result data | Initial and observed child kept separately with post-world and exact parent link | `SUPERVISION-PG-RC112` |
| `InterruptAction` | native call-plan alphabet | Request versus explicit await; no completion or source execution claim | `SUPERVISION-PG-RC112` |
| `Refusal` | native controller refusal | Invalid views/decisions only; never effect Cause or finite-tape exhaustion | `SUPERVISION-PG-RC112` |
| `WaitState` | native shared controller | Targets, actual publications, stored continuation datum; result field is not return | `SUPERVISION-PG-RC112` |
| `ReplayResult` | native controller outcome | Distinct done/frontier/refused over observed state; not Scheduler.ReplayResult alias | `SUPERVISION-PG-RC112` |
| `ScopeMode` | native finite leaf | Source forkIn versus fiberRunIn policies over the canonical Scope owner | `SUP-L-SCOPE` |
| `ScopeFinalizer` | native first-order instruction | Child identity plus self guard; canonical Scope stores lifted data, never a function | `SUPERVISION-PG-RC112` |
| `ScopeBinding` | native related result | Canonical Scope with standard ULift keys/instructions, exact observer key and interruptor | `SUPERVISION-PG-RC112` |
| `RaceAllState` | native controller state | First-success rc.112 bookkeeping; distinct from bounded binary first-completion RaceState | `SUPERVISION-PG-RC112` |
| `RaceAllDecision` | native decision alphabet | Split launch, callback, cleanup selection, request; no hidden callback choice | `SUPERVISION-PG-RC112` |
| `Globals.Valid` | native Prop judgment | Allocation uniqueness only; exact valid_iff | `SUPERVISION-PG-RC112` |
| `Globals.Extends` | native Prop judgment | Allocation prefix, monotone global middleware, unique post IDs | `SUPERVISION-PG-RC112` |
| `Globals.OwnsChildren` | native Prop judgment | Observed fiber and each direct child allocated in the observed global view | `SUPERVISION-PG-RC112` |
| `Fiber.Valid` | native Prop judgment | Local lifecycle and key/child uniqueness; does not assert Machine.WellFormed | `SUPERVISION-PG-RC112` |
| `WaitStep` | native Prop judgment | Exactly successful WaitState.observe for an actual publication decision | `SUPERVISION-PG-RC112` |
| `WaitRuns` | native Prop judgment | Exactly total finite waitReplay on a fixed publication tape | `SUPERVISION-PG-RC112` |
| `RaceStep` | native Prop judgment | Exactly successful raceStep on the explicit decision | `SUPERVISION-PG-RC112` |
| `RaceRuns` | native Prop judgment | Exactly total finite raceReplay on a fixed race decision tape | `SUPERVISION-PG-RC112` |

`Fiber.toFiberState_eq` proves exactly that the core projection is the existing
FiberState; it does not identify this wrapper with an admitted Scheduler.Machine.
`Fiber.Valid` is deliberately weaker than that machine invariant and does not
claim a complete graph of all waiting targets. `Globals.OwnsChildren` is
checked for both immediate post-start views. A valid child whose child list
contains an unallocated ID is rejected, as CE-026 requires.

## Exact shape expectations

The following is authored input for the existing FiberAssurance metadata
checker. Prefix every constructor with `Effect4.Supervision.`. Structure
fields appear in exact declared order; a dash means an inductive, not a
structure. Extra constructors or fields must fail the shape check. Exact
constructor argument types and projection types are in the battery.

| Type | Constructors, in order | Structure fields, in order |
| --- | --- | --- |
| `MaskMode` | `MaskMode.interruptible`, `MaskMode.uninterruptible`, `MaskMode.inherit` | — |
| `ForkOptions` | `ForkOptions.mk` | `startImmediately`, `daemon`, `maskMode` |
| `Globals` | `Globals.mk` | `allocated`, `middlewareInstalled` |
| `ObserverMode` | `ObserverMode.awaitValue`, `ObserverMode.joinEffect` | — |
| `Subscription` | `Subscription.mk` | `key`, `mode` |
| `Fiber` | `Fiber.mk` | `core`, `context`, `children`, `subscriptions`, `interrupted` |
| `Observation` | `Observation.waiting`, `Observation.value`, `Observation.effect` | — |
| `StartObservation` | `StartObservation.deferred`, `StartObservation.immediate` | — |
| `ForkEvent` | `ForkEvent.scheduled`, `ForkEvent.evaluated`, `ForkEvent.registered` | — |
| `ForkResult` | `ForkResult.mk` | `globals`, `parent`, `initial`, `child`, `events`, `removeFromParent` |
| `InterruptAction` | `InterruptAction.request`, `InterruptAction.awaitAll` | — |
| `Refusal` | `Refusal.invalidFiber`, `Refusal.duplicateFiber`, `Refusal.wrongStartMode`, `Refusal.wrongChildIdentity`, `Refusal.wrongParentIdentity`, `Refusal.invalidStartGlobals`, `Refusal.invalidParentOwnership`, `Refusal.invalidChildOwnership`, `Refusal.duplicateSubscription`, `Refusal.unknownPublication`, `Refusal.duplicateScopeKey`, `Refusal.duplicateEntrant`, `Refusal.noEntrant`, `Refusal.wrongRacePhase`, `Refusal.unknownEntrant` | — |
| `WaitState` | `WaitState.mk` | `targets`, `published`, `result` |
| `ReplayResult` | `ReplayResult.done`, `ReplayResult.frontier`, `ReplayResult.refused` | — |
| `ScopeMode` | `ScopeMode.forkIn`, `ScopeMode.fiberRunIn` | — |
| `ScopeFinalizer` | `ScopeFinalizer.mk` | `child`, `skipSelf` |
| `ScopeBinding` | `ScopeBinding.mk` | `scope`, `observerKey`, `interruptor` |
| `RaceAllState` | `RaceAllState.mk` | `unstarted`, `starting`, `live`, `remaining`, `failures`, `winner`, `accepted`, `cleanupNeeded`, `requests`, `cleanup`, `cleanupRequested` |
| `RaceAllDecision` | `RaceAllDecision.beginLaunch`, `RaceAllDecision.finishLaunch`, `RaceAllDecision.complete`, `RaceAllDecision.beginCleanup`, `RaceAllDecision.requestNext` | — |

No local metadata checker is compiled in the contract battery. That would
introduce an unnecessary trust-bearing metaprogram beside proof tests. The
existing exempted FiberAssurance driver owns shape and public-census checking;
this packet adds no trust exemption.

## Public operation groups

These groups are one ownership record for each hand-authored non-theorem
operation. Each remains tied to its exact ascription in the battery. The
136 theorem names all carry explicit source-row tags there and use this graph
or the named finite leaf. Private implementation helpers create no additional
public semantic API.

| Group | Exact public operation names | Route |
| --- | --- | --- |
| Initialization and admission | `MaskMode.select`, `Globals.install`, `Globals.Valid`, `Globals.allocate`, `Globals.Extends`, `Globals.extends?`, `Globals.OwnsChildren`, `Globals.ownsChildren?`, `Fiber.Valid`, `Fiber.valid?` | `SUPERVISION-PG-RC112` |
| Canonical observation and interruption | `Fiber.toFiberState`, `Fiber.published?`, `Fiber.addChild`, `Fiber.removeChild`, `observation`, `Fiber.observe`, `Fiber.cancel`, `Fiber.publish`, `interruptCause`, `Fiber.recordInterrupt` | `SUPERVISION-PG-RC112` |
| Fork boundary | `initialFiber`, `commitFork`, `forkUnsafe`, `forkChild`, `forkDetach` | `SUPERVISION-PG-RC112` |
| Shared waiting | `WaitState.begin`, `WaitState.pending`, `WaitState.ready?`, `WaitState.observe`, `ReplayResult.state`, `WaitStep`, `waitReplay`, `WaitRuns` | `SUPERVISION-PG-RC112` |
| Parent and bulk coordination | `beginParentExit`, `parentExitView`, `newChildren`, `awaitAllChildren`, `interruptAllRequests`, `interruptAllWait` | `SUPERVISION-PG-RC112` |
| Scope boundary | `bindScope`, `forkScopedBinding`, `scopeFinalizerInterruptor`, `scopeObserver` | `SUPERVISION-PG-RC112` |
| First-success race | `raceForkOptions`, `raceCleanupMask`, `RaceAllState.initial`, `raceAllAdmit`, `RaceAllState.result?`, `raceComplete`, `raceStep`, `RaceStep`, `raceReplay`, `RaceRuns` | `SUPERVISION-PG-RC112` |

## Runtime clause ledger

These rows specify controller receipts and the remaining source obligations;
they are not a coverage report and assign no row a green status. The census
and generated coverage join decide status only after proof and gate checks.
The theorem tags in the battery identify all permitted reuse, including
common wait laws. `fork.race-all` follows the corrected source wording: an
observed success stops future launch, and empty/nonempty cleanup is chosen
before the currently starting entrant is inserted.

| Census row | Quantified theorem obligations | Required-open source clause |
| --- | --- | --- |
| `fork.unsafe` | `initialFiber_eq`, `forkUnsafe_deferred`, all immediate admission/refusal equations, `forkUnsafe_immediate`, freshness and validity laws, `commitFork_eq` | Actual body evaluation, shared-world observation, scheduler dispatch, inherited host context/flags |
| `fork.child` | `forkChild_eq`, `Globals.install_eq`, `commitFork_done_untracked`, child uniqueness/removal | Installing the real global middleware; child completion invoking its parent observer |
| `fork.detach` | `forkDetach_eq`, `commitFork_daemon_untracked` | Actual daemon execution and independent lifetime |
| `fork.await` | `observation_await`, `Fiber.observe_*`, `Fiber.cancel_*`, `Fiber.publish_eq`, `Fiber.published_iff` | Host callback registration, cancellation, and successful Exit-as-value resumption |
| `fork.join` | `observation_join`, `observation_value_ne_effect`, shared observation/publication laws | Exit resumed as an Effect through the continuation interpreter |
| `fork.interrupt` | `interruptCause_eq`, `Fiber.recordInterrupt_*`, bulk request/wait equations | Request delivery, synchronous execution, and interruption followed by actual await |
| `fork.interrupt-all` | `interruptAllRequests_eq`, `interruptAllWait_eq`, `WaitState.*`, `waitReplay_*`, `wait_fixedTape_deterministic` | Executing request calls in order before explicit await; observations may arrive during calls |
| `fork.in` | `bindScope_*`, `scopeFinalizerInterruptor_eq`, `scopeFinalizer_self_guard`, `scopeObserver_*` | Supplied post-start scope denotes the same mutable host scope; finalizer execution |
| `fork.scoped` | `forkScopedBinding_eq` | Ambient Scope service resolution and composition with fork startup |
| `fork.fiber-run-in` | `bindScope_*`, self-guard contrast, keyed scope removal | Existing-fiber scope attachment, closed-scope request execution and child observer delivery |
| `fork.await-all-children` | `newChildren_eq`, `newChildren_membership`, `awaitAllChildren_eq` | Before/after snapshots obtained from the same parent during actual body evaluation |
| `fork.race-all` | Exact race initial/admission/result/completion/decision/replay equations; `race_first_accepted_stable`, startup/publication safety, positive success/failure and empty-frontier laws | Actual first accepted callback resumption, request delivery, dynamic shared-set interpretation, uninterruptible continuation execution |
| `interrupt.accumulate` | `interruptCause_eq`, `Fiber.recordInterrupt_live`, `Fiber.recordInterrupt_done`, `Fiber.recordInterrupt_core` | Actual FiberId/annotation interpretation and integration of the recording facet with delivery |
| `rule.only-fork-child-tracks` | `commitFork_eq`, `commitFork_daemon_untracked`, `forkDetach_eq`, child-set laws, `raceForkOptions_eq` | Correspondence of all source fork call sites/options to the observed controller inputs |
| `rule.children-interrupted-after-exit` | `beginParentExit_eq`, `parentExitView_waiting`, `parentExitView_ready`, publication-requires-children law, common wait laws | Parent continuation after a successful child wait; intervening interruption can replace the local body Exit |

## Semantic boundaries that cannot be erased by the join

- `Fiber.publish` constructs the supplied terminal view and notifications. It
  is unconditional and may overwrite an already-done view; it is not an
  admitted one-shot transition or proof that cleanup ran once.
- Immediate fork observations include post-globals and post-parent as well as
  post-child. A child can remove an existing sibling or install global
  middleware during startup. Registration uses the observed parent, and both
  observed fibers must own only allocated direct-child IDs.
- Parent body Exit retention holds inside the successful-wait controller.
  External parent interruption is outside that controller and may replace
  its result. CE-025 forbids the stronger stability claim.
- `bindScope` receives the post-start scope. Copying its pre-start state across
  immediate execution would miss scope closure performed by the child.
- The race's starting entrant is separate from the callback-visible live set.
  An empty winner-time set selects the direct Exit and can leave a late child
  live. A nonempty set selects deferred cleanup over the shared set; its
  targets are read at beginCleanup. CE-024 forbids both an all-launched cleanup
  theorem and a fixed winner-time target snapshot.
- Race accepted-result stability allows later callbacks. The host's decision
  to accept one resume and ignore later resumes remains an explicit bridge.
- Bulk interruption plans freeze explicit call order only. Synchronous child
  execution and publication may occur during a request. Actual publications
  remain separate data, never inferred from a request list or a masked wait.
- Full first-order or host-compatibility claims require admission and an
  interpretation of the abstract context/error/annotation/result alphabets.
  The external `FiberId -> ι` argument is not stored and has no assumed
  injectivity. Scope's standard ULift is a carrier embedding, not a host
  finalizer-execution theorem.

## Graph-edge ledger

| Edge | Breaker state | Required closure evidence |
| --- | --- | --- |
| identity | `required-open` | Exact declaration census, all type dispositions, owner modules, and the 19 shape checks |
| construction | `required-open` | Constructor/field checks, local finite-leaf cases, exact initialization, admission and refusal equations |
| semantics | `required-open` | Computational wait/race steps, exact graph relations and replay clauses, all branch equations and inhabited runs |
| laws | `required-open` | Publication safety, identity/set/key laws, fixed-tape determinism, accepted-result stability with their precise profiles |
| representation | `not-applicable` | No serialization, generated target program, normal form, or round-trip claim in this packet |
| counterexamples | `required-open` | CE-012 through CE-026 remain green and the implementation meets their frozen repair obligations |
| bridges | `required-open` | Source body/context/annotation/dispatcher/continuation, publication justification, scope and shared-set interpretations as listed above |
| targets | `required-open` | Finite pinned-host harness plus later interpretation proof; a finite host pass alone cannot close equivalence |
| trust | `required-open` | Actual axiom output for all 136 laws at the allowed `propext`/`Quot.sound` ceiling and the existing trust gate |
| coverage | `required-open` | Every public declaration joined to the independent assurance route; only justified runtime clauses joined to row witnesses |

A controller implementation can close its local semantic and proof obligations
while retaining required-open bridges and honest partial runtime rows. It
cannot close this graph's full host route or claim category cutover while
those edges remain open. Root-owned assurance integration must retain that
separation rather than relabeling external obligations as not-applicable.

## Verification route

The exact red measurements and their elaboration-only feasibility check are
recorded in the contract. The 15 independently green finite witnesses live
in [`FiberSupervision.lean`](../Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean),
with stable claims and repair links in
[`REGISTER.md`](../test/counterexamples/REGISTER.md) and
[`concurrency/ATTACKS.md`](../test/counterexamples/concurrency/ATTACKS.md).
CE-024/025 additionally link the independent host witness in
`harness/fiber-supervision/runtime-check.ts`.

After the independent implementation, run the exact contract and axiom report
without the default error cap; build the package; run fiber assurance and its
reaction gate, the trust gate, the pinned supervision host gate, and the
runtime census gate; obtain independent model/proof/compatibility review;
then perform the root-owned runtime witness join. Generated files come from
their existing drivers, never from this prose. Runtime coverage may be stated
only by the repository's prescribed report after its census gate passes.
