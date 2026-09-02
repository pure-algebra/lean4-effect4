# Fork and supervision contract

Status: breaker-frozen, RED, 2026-09-02.

Owner: `Effect4/Concurrency/Supervision.lean`, namespace
`Effect4.Supervision`. This resumes the existing direct-child reservation.
The binary opaque-terminal `Race.lean` and its frozen packet are unchanged.
The exact declaration and statement authority is
[`FiberSupervisionContract.lean`](../../Effect4Test/Concurrency/FiberSupervisionContract.lean).
[`SUPERVISION-DAG.md`](../../docs/SUPERVISION-DAG.md) owns dispositions,
shape expectations, assurance routes, and the open source bridges.

## Source and admitted boundary

The behavioral source is `effect@4.0.0-rc.112`, upstream
`2600f62f4532026928454dcea8d1c48557b3f942`, vendored
[`src/internal/effect.ts`](../../vendor/effect-4.0.0-rc.112/src/internal/effect.ts),
SHA-256 `0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`.
The census owns source row spans and digests. Relevant regions are FiberImpl
construction/publication/interrupt recording at 499–660, middleware and fiber
observation at 738–921, callback registration at 1102–1144, raceAll at
1477–1532, and fork/scope operations at 5227–5461. The global middleware is
`interruptChildrenPatch` at 6656.

This packet defines controllers at observed runtime boundaries. It does not
implement the Effect continuation interpreter. Body execution enters as data:
post-start global, parent, and child views; a local body Exit; and actual child
publications. An interrupt request is distinct from execution, cleanup, and
publication. A finite tape with unanswered publications remains a frontier.
The packet claims fixed-tape behavior only, not scheduler fairness, eventual
termination, a codec, or a host equivalence theorem.

`Fiber.publish` is an unconditional constructor for the terminal view and its
ordered notifications **given an externally justified actual publication**.
It is not an admitted one-shot runtime transition: its equation can overwrite
an already-done view. Its cleanup count of one records the supplied boundary;
it does not prove that cleanup ran once. The existing Fiber representative
continues to own operational cleanup safety. Likewise `Fiber.recordInterrupt`
models only cause recording; its core-state frame law deliberately makes no
claim about actual delivery or the synchronous execution performed by
`interruptUnsafe`.

The parent wait controller models the **successful wait continuation with no
intervening parent evaluation**. A new parent interruption can replace the
stored local body Exit; `E4-CONC-CE-025` and the host harness exhibit this.
The local controller's result retention must not be presented as an
unconditional rc.112 parent-result stability theorem.

## Public data and canonical relationships

All names in this synopsis are under `Effect4.Supervision`; the Lean battery
is authoritative for their exact types. `χ`, `ε`, `δ`, `ι`, and `α` range over
`Type u`; `β` ranges independently over `Type v`. The cause and exit carriers
are canonical `Effect4.Cause ε δ ι α` and `Effect4.Exit β ε δ ι α`.
An operation argument `FiberId -> ι` interprets interruptors. It is never
stored, and no injectivity or host interpretation is assumed. Standard
`ULift.{u}` embeds passive scope keys and finalizer records without narrowing
the existing cause universe.

```lean
inductive MaskMode | interruptible | uninterruptible | inherit
structure ForkOptions where
  startImmediately : Bool
  daemon : Bool
  maskMode : MaskMode
structure Globals where
  allocated : List Effect4.FiberId
  middlewareInstalled : Bool
inductive ObserverMode | awaitValue | joinEffect
structure Subscription where
  key : Nat
  mode : ObserverMode
structure Fiber (χ : Type u) (β : Type v) (ε δ ι α : Type u) where
  core : Effect4.FiberState (Effect4.Exit β ε δ ι α)
  context : χ
  children : List Effect4.FiberId
  subscriptions : List Subscription
  interrupted : Option (Effect4.Cause ε δ ι α)
inductive Observation (β : Type v) (ε δ ι α : Type u)
  | waiting (key : Nat)
  | value (exit : Effect4.Exit β ε δ ι α)
  | effect (exit : Effect4.Exit β ε δ ι α)
inductive StartObservation (χ : Type u) (β : Type v) (ε δ ι α : Type u)
  | deferred
  | immediate (globals : Globals) (parent fiber : Fiber χ β ε δ ι α)
inductive ForkEvent
  | scheduled (child : Effect4.FiberId) (priority : Nat)
  | evaluated (child : Effect4.FiberId)
  | registered (parent child : Effect4.FiberId)
structure ForkResult (χ : Type u) (β : Type v) (ε δ ι α : Type u) where
  globals : Globals
  parent : Fiber χ β ε δ ι α
  initial : Fiber χ β ε δ ι α
  child : Fiber χ β ε δ ι α
  events : List ForkEvent
  removeFromParent : Option Effect4.FiberId
inductive InterruptAction
  | request (target : Effect4.FiberId)
  | awaitAll (targets : List Effect4.FiberId)
inductive Refusal
  | invalidFiber (id : Effect4.FiberId)
  | duplicateFiber (id : Effect4.FiberId)
  | wrongStartMode
  | wrongChildIdentity
  | wrongParentIdentity
  | invalidStartGlobals
  | invalidParentOwnership
  | invalidChildOwnership
  | duplicateSubscription (key : Nat)
  | unknownPublication (id : Effect4.FiberId)
  | duplicateScopeKey (key : Nat)
  | duplicateEntrant
  | noEntrant
  | wrongRacePhase
  | unknownEntrant (id : Effect4.FiberId)
structure WaitState (τ : Type u) where
  targets : List Effect4.FiberId
  published : List Effect4.FiberId
  result : τ
inductive ReplayResult (σ : Type u) (τ : Type v)
  | done (state : σ) (result : τ)
  | frontier (state : σ)
  | refused (state : σ) (reason : Refusal)
inductive ScopeMode | forkIn | fiberRunIn
structure ScopeFinalizer where
  child : Effect4.FiberId
  skipSelf : Bool
structure ScopeBinding (β : Type v) (ε δ ι α : Type u) where
  scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} ScopeFinalizer) β ε δ ι α
  observerKey : Option Nat
  interruptor : Option Effect4.FiberId
structure RaceAllState (β : Type v) (ε δ ι α : Type u) where
  unstarted : List Effect4.FiberId
  starting : Option Effect4.FiberId
  live : List Effect4.FiberId
  remaining : Nat
  failures : List (Effect4.Reason ε δ ι α)
  winner : Option (Effect4.FiberId × β)
  accepted : Option (Effect4.Exit β ε δ ι α)
  cleanupNeeded : Bool
  requests : List Effect4.FiberId
  cleanup : Option (WaitState (Effect4.Exit β ε δ ι α))
  cleanupRequested : Bool
inductive RaceAllDecision (β : Type v) (ε δ ι α : Type u)
  | beginLaunch
  | finishLaunch (immediateExit : Option (Effect4.Exit β ε δ ι α))
  | complete (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α)
  | beginCleanup
  | requestNext
```

`Fiber.toFiberState` is exactly the `core` projection. The wrapper adds the
minimum boundary information absent from the bounded representative: opaque
context, direct-child order, keyed subscriptions, and accumulated Cause. It
contains no scheduler machine, hidden host callback, Promise, continuation,
or duplicate FiberId/Exit/Scope definition. First-order claims remain relative
to admitted alphabets: choosing a function type for `χ` does not become a
reification theorem merely because Lean accepts it.

## Admission and operational obligations

Every obligation below has a quantified named theorem in the exact battery.
The comment preceding each theorem lists the census row IDs required in the
production theorem's docstring. Those tags identify the claim; they do not
close a source bridge by themselves.

1. **Identity and lifecycle.** `Globals.Valid` requires unique allocated IDs.
   `Globals.Extends before after` requires the previous allocation list as an
   exact prefix, monotonic middleware installation, and unique post IDs.
   `Globals.OwnsChildren g fiber` requires the fiber itself and each direct
   child to occur in `g.allocated`. `Fiber.Valid` requires unique children and
   subscription keys, plus the active/finalizing/done terminal and cleanup
   conditions specified by `Fiber.valid_iff`. It is a local view predicate,
   not an alias for `Machine.WellFormed`; waiting-target closure and a complete
   global graph invariant remain outside this boundary.
2. **Fork initial and observed state.** `initialFiber` is runnable with no
   terminal, pending interrupt, children, subscriptions, or accumulated cause;
   its context and selected mask come from the pre-start parent. `forkUnsafe`
   rejects an already allocated child ID before any start-mode check. Deferred
   start requires `startImmediately = false`, allocates the ID, and records a
   priority-zero scheduling event. This local branch assumes an admitted
   pre-world for its global invariant theorems; it is not a global admission
   checker for arbitrary inputs.
3. **Immediate admission.** Immediate start requires the true start flag,
   stable child and parent identities, valid post-child and post-parent views,
   post-globals extending the allocation **before** startup, and post-global
   ownership of **both** post-parent and post-child direct children. These
   guards occur in that order; every failure has an exact refusal equation.
   `commitFork` consumes the observed globals and observed parent unchanged
   apart from possible child registration. This preserves sibling removal,
   nested allocations, global middleware installation, and changed parent
   state caused by immediate execution. Initial inheritance is distinct from
   the child's post-execution mask and context.
4. **Direct-child registration.** After startup, only an unpublished
   non-daemon is added to the observed parent's ordered child set. A completed
   immediate child and a daemon receive no parent link. Addition avoids
   duplicates; completion removes exactly its identity and leaves unrelated
   children in order. `forkChild` installs the global middleware and forces
   non-daemon; `forkDetach` forces daemon only. A daemon body can itself install
   middleware, so there is no final-global-state preservation claim for it.
5. **Await, join, and subscriptions.** `Fiber.published?` requires the canonical
   `.done` status and returns its terminal. Invalid views are refused. A
   published child returns immediately without adding a subscription; await
   yields `Observation.value exit`, join `Observation.effect exit`. A live
   child registers a fresh key and returns waiting. Cancellation removes
   exactly that key. At externally supplied publication, `Fiber.publish`
   returns notifications in subscription order and a terminal view with no
   remaining subscriptions or children. No repeated publication law is claimed.
6. **Interruption record.** A published view is unchanged by recordInterrupt.
   An unpublished view records the explicit interpreted and annotated
   interrupt Cause, combining it with an earlier Cause through canonical
   `Cause.combine`. Core state remains unchanged at this recording boundary.
   Actual annotation capture, interrupt delivery, and execution are open.
7. **Waiting and parent publication.** `WaitState.pending` filters the target
   list against actual publications. An accepted publication appends the
   pending identity; unknown or repeated publications refuse. `ready?` returns
   continuation data only when every target has published. Replay is tied to
   `WaitStep`/`WaitRuns` by exact ready/nil/cons equations, with explicit done,
   refused, and frontier outcomes and fixed-tape determinism. The publication
   frame law and a positive two-publication run prevent an empty-relation
   implementation. `beginParentExit` selects the current child list only when
   the **global** middleware is installed. Within the successful-wait profile,
   `parentExitView` is finalizing before readiness and published only afterward.
   Reading its stored local terminal as an observable Exit is forbidden.
8. **New-child wait and bulk interruption.** `awaitAllChildren` waits for the
   children still present after the body that were absent from the initial
   snapshot, in current order. `interruptAllRequests` describes all explicit
   request calls followed by the explicit await phase. It is a call plan, not
   a completion transition. A child may execute, clean up, or publish inside
   an earlier request call. `interruptAllWait` is initialized from the supplied
   post-request views, preserving those early publications; subsequent waits
   require actual publication observations.
9. **Scope composition.** `bindScope` consumes the supplied **post-start** view
   of the same scope, because immediate execution may close or mutate it. A
   published child is skipped. A closed forkIn scope chooses the parent as
   interruptor; fiberRunIn chooses the child. An open binding refuses a reused
   key, calls canonical `Scope.addUnsafe`, and records that exact key for the
   child observer. forkIn's finalizer skips self-interruption; fiberRunIn's
   does not. `scopeObserver` removes the same lifted key through canonical
   `Scope.removeUnsafe`. `forkScopedBinding` assumes the ambient scope has
   already been resolved. Scope interpretation, finalizer execution, and
   ambient service resolution remain open bridges.
10. **First-success racing with reentrant startup.** `raceAllAdmit` rejects
    duplicate entrant IDs; allocation and body execution remain outside it.
    Entrants use immediate interruptible daemon options. `beginLaunch`
    reserves a separate `starting` ID; `finishLaunch` inserts it and supplies
    its immediate terminal observation if any. A callback from an already
    registered entrant may occur between those decisions. Success prevents
    subsequent beginLaunch, but must not erase the currently starting child.
    Failure reasons append in callback arrival order, with duplicates; even
    all-empty causes produce a failed Exit after the last failure.
11. **Race branch capture and waiting.** The first accepted success captures
    the winner and the **empty/nonempty branch** of the live set after removing
    that winner. Empty selects a direct Exit; a late inserted child can remain
    live outside cleanup. Nonempty selects deferred uninterruptible cleanup;
    `beginCleanup` reads the then-current live list, so it can include the
    late entrant. Requests are explicit `requestNext` decisions, separate
    from actual completion callbacks. The accepted result cannot be returned
    until startup finishes, and the cleanup branch also requires requests
    complete and every target published. `raceComplete_after_accepted` allows
    later callbacks to update bookkeeping while retaining the accepted result.
    This is accepted-result stability, not a claim that callbacks stop or
    that every call to host resume is accepted. Empty race and incomplete
    cleanup tapes remain frontiers; no liveness follows from the mask setting.

## Assurance and red receipt

The frozen surface contains 294 exact ascriptions: 105 type, constructor, and
projection checks; 53 operation checks (including eight Prop judgments); and
136 theorem checks. There are 19 concrete public shapes and eight additional
public Prop judgments. The DAG records all of them, including finite leaves.
The existing `FiberAssurance` integration must check the exact constructor and
field tables there. No new metaprogram or trust exemption is introduced into
this battery.

The separate breaker ran, before production implementation:

```text
lake env lean -DmaxErrors=10000 Effect4Test/Concurrency/FiberSupervisionContract.lean
  exit 1; 1,090 diagnostics; zero warnings
  997 unknown-reference diagnostics naming exactly the 294 intended declarations
  93 consequent unknown-type, dotted-identifier, record, or field diagnostics
lake env lean -DmaxErrors=10000 Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean
  exit 1; exactly 136 unknown theorem constants; zero warnings
lake env lean -DmaxErrors=10000 Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean
  exit 0; zero errors and warnings; 15 kernel-checked finite witnesses
```

The full red output was inspected beyond the default 100-error limit. No
missing name belongs outside `Effect4.Supervision`. A disposable signature
feasibility module, containing the exact shapes and assumed statement names,
elaborated all 294 ascriptions with zero errors or warnings; it checks only
statement formation, not consistency or proof. It is not part of the repository
and contributes no proof receipts. The 15 actual counterexample receipts are
11 with no axioms and four (`post_start_child_ownership_required`,
`only_new_children_awaited`,
`race_empty_and_cleanup_frontiers`, `race_reentrant_launch_branch`) using only
`propext` and `Quot.sound`.

All 136 production law receipts remain red until the independent builder
proves them. Their permitted ceiling is `propext` and `Quot.sound`. The builder
must not edit this packet to repair a proof failure. Any statement amendment
requires breaker review and an explicit recorded reason. Full build, public
surface/shape verification, trust gate, host checks, and independent review
follow implementation; this red packet claims none of those have passed.
The finite host cases in `harness/fiber-supervision/runtime-check.ts` supplement
CE-024/025 and never substitute for the required-open source interpretation.
