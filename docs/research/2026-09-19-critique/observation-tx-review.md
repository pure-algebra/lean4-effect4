# Observation, transaction, and composition audit

Reviewed tree: `/Users/pooks/Dev/lean4-effect4`, coordinator base `6d2385cd`. Read-only review. No repository edits or Lake invocation. Candidate Lean controls are in `/private/tmp/effect4-critique-observation-tx-probes.lean`; the coordinator must execute them before calling them verified. This is architectural clarification, not a proposal for more gates.

**First thing to know:** the critique identifies useful obligations, but upgrades six open proposals to “Concretely Approved Architecture”, invents a total ordering between observations, and assumes a resumable public run boundary that does not currently retain its residual command stack. These are correctable contract issues; no STM implementation exists to accuse of violating serializability.

## 1. What the critique gets right, and what it overstates

- Correct: current `Machine.Obs` includes all fiber exits and concrete Stores. Replacement by a physically different store needs a relation or logical projection, not reflexive equality of raw representations.
- Correct: typing does not establish module concurrency semantics. `HasTy` is not linearizability, fairness, progress, or cancellation cleanup.
- Correct: disabling the yield injection is not enough to establish a transaction exclusion invariant. `injectYield` only gates the injection at `Machine/Fibers.lean:1012`; `driveStep` can evaluate/resume other fibers, and external decisions can execute between separately issued commands.
- Correct: source `Effect.ts:24343-24354` schedules all registered callbacks of every journal entry, including unmodified entries, on the committing fiber's dispatcher at priority 0; clears each cell's pending map afterwards. This is not Latch's coalesced broadcast.
- Incorrect status: decisions 78–83 are all open; only the typed-world rows 44–45 are approved. The critique's table is a recommendation, not a ratification.
- Overbroad scope: DI-11 explicitly rules Queue/Mailbox/PubSub composition and Stream kernel; it does not itself ratify Semaphore/Cache/STM/Latch. Their proposed composition can be retained without claiming the ruling already covers them.
- Overclaim: being first-order is not by itself complete serializability/replayability, storage migration, or memory safety. Code resolution, codecs, identities, effects, and invariants remain necessary. Current public machine projection additionally drops command-loop residue (below).

## 2. Observations are a family of views, not a strict hierarchy

The critique states `Obs_semantic ⊏ Obs_holder ⊏ Obs_diagnostic`. There is no defined information order, no proof of strictness, and no reason a diagnostics-only event stream determines public resource state or host reply receipt. Neither the current code nor the synthesis proposed that chain.

Actual owners:

- `src/Effect4/Laws/Machine/Behaviour.lean:29-50`: `Obs = {exits : List (FiberId × Option ExitV), stores : Stores}`. No trace, no frontier reason, no code/control projection.
- `src/Effect4/Run.lean:220-253`: holder `Run.Observation` contains host-protocol state, outcome, root exit, outstanding calls, pending/retired keys, applied count, frontier reasons, and fiber statuses. **It does not contain the command journal.** `Run` separately stores that journal at lines 57–59.
- `src/Effect4/Api/Supervision.lean:229-246`: status reads exit, parent children, scope observer, and finally fork history to distinguish daemon from root. Thus some current trace data is holder-semantic, not erasable diagnostics.

A precise small definition is an information preorder by factorization:

```lean
-- Conceptual signature; reuse a suitable existing projection API if one exists.
def FactorsThrough {S A B : Type} (low : S → A) (high : S → B) : Prop :=
  ∃ forget : B → A, ∀ s, low s = forget (high s)
```

Use it only when a factorization exists. A joint observation can be a product `(semantic s, holder s, diagnostic s)` with obvious forgetful projections. Diagnostics alone is not that product. Strictness needs a distinguishing pair and is usually irrelevant. Existing `Machine.Obs` and `Run.Observation` must stay intact; introduce named projections/relations and explicit connectors.

Concrete countermodel candidate in the Lean control: two raw machines have the same fibers/stores but differ by a `.forked` event. Frozen `obs` is equal; `Api.fiberStatuses` changes root to daemon. It is explicitly a counterexample over arbitrary machine states, not evidence that deleting history preserves reachability. Its purpose is to refute an unconditional factorization from frozen Obs to holder supervision.

## 3. Hiding identities needs an interface world

“Existentialize helpers” is insufficient unless that existential remains coherent under future operations. A public result may contain a nested handle later supplied in `Command.apply`, interrupt, join, or another module operation. Concrete handle IDs also occur in serialized values and replay keys.

Use a world-indexed relation `Rel W model concrete` where W records, per identity sort:

1. the admitted public identities and an injective correspondence to concrete identities;
2. concrete private identities and who may refer to them;
3. typing/lifetime compatibility for the referenced cells/fibers;
4. extension when a previously private identity is deliberately exported;
5. closure of related outputs, public state, requests, causes, and commands under the same correspondence.

A bijection onto **all** concrete identities would wrongly forbid private helpers. An injection from public/reference identities plus a private complement is sufficient for many refinements. The relation may extend monotonically on allocation. No recycling without an epoch/generation or lifetime argument. “Private” is relative to a chosen client interface: an API that enumerates all fibers exposes helpers unless that API's profile changes and its projection is named. Internal allocation may also change later public numeric names, so simply filtering helper entries from a list is not enough.

Current reusable pieces: `Store.Val.handles`, machine value handle tags, `Laws/Machine/Handles.lean` key/world projections, `Book.ListRel` and replay-lifting pattern. These are starting points, not an existing renaming/hiding theorem.

## 4. Fuel frontier is not an implemented public resume protocol

`driveState` (`Machine/Fibers.lean:1945-1954`) returns `(machine, remaining Cmd list)`. `driveState_add` really proves resumption with that remainder. Above it:

- `drive` returns only the machine (`:1958-1960`).
- `fireStep` returns machine plus settled Bool and loses the task's remaining commands (`:1973-1979`). `fireState` drains the dispatcher snapshot before folding; once a task exhausts its budget, later snapshot tasks are not run and are not retained in the result (`:1983-1990`).
- `stepDecisionState` returns machine and Bool, with the command list projected away (`:2058-2088`).
- `replayEval` stops on fuel shortage and returns a frontier machine, with neither the pending command list nor remaining tape in the constructor (`:2123-2147`).
- `HostSession.advance` stores that machine even when phase is `.frontier`, then accepts later independently supplied controls (`Api/HostSession.lean:239-250`). No pending-command or exclusive-owner field exists in Session (`:84-93`). Its protocol admits scheduling from idle/awaiting/parked; it does not recognize a suspended atomic owner.
- `HostSession.applyReply` similarly calls `steppedBy` and counts the reply once the guard disappears. It does not preserve a command continuation (`:204-224`).

The current guarantee is **rerun from the same initial state/tape with sufficient fuel** and command-loop resumption if the caller explicitly retains `driveState`'s pair. It is not automatic refueling of an arbitrary public frontier machine. No `runCommand` declaration exists at this base; relevant paths are `Run.step → Runner.step/result → HostSession.advance/applyReply → stepDecisionState`.

Actual-machine candidate control: evaluate `succeed 42` with fuel 1. Root is running, command residue `[loop root false, drainDue]` remains. A new `evaluate root` at fuel 400 skips the running root, drains dues, and reports settled while root exit remains absent. Passing the saved `driveState` residue finishes. An interrupt decision can still change the intermediate frontier. This is not an STM counterexample; it proves the boundary that a future persistent owner must cover is larger than `TxOpen.owner`.

Minimal architectural alternatives:

A. **Evaluation evidence only:** keep the current replay API and state that low-fuel results are approximants rerun from the original state; do not expose them as resumable execution snapshots or allow version erasure to rely on that claim.

B. **Resumable running state:** retain the residual command stack **and** outer continuation (rest of captured dispatcher snapshot, flush/clock phase, remaining selected command). A first-order continuation carrier can reuse existing Cmd/Task data. Persist owner across this whole carrier; next budget advances this same continuation. Fresh external input is classified as inspect, record-only receipt, owner-compatible update, deferred work, or execution that must wait until owner closure. This is a control representation requirement, not a transaction-specific duplicate evaluator.

Neither alternative changes fuel into a typed program failure. Receipt-only host reply collection can continue if proved noninterfering; executing a reply is a different action.

## 5. Exact transaction version-erasure proposition

The critique's “only under strictly pure/TxRef” is too strong as a necessary condition. That fragment is a useful sufficient starting profile. Some additional synchronous operations might commute with the active transaction or affect only private disjoint state. The actual condition is stability of every journaled cell's committed version/value between first read and commit, plus matching attempt/retry behavior.

Candidate invariant, not current code:

`AttemptRel(W, refAttempt, implAttempt)` relates owner, residual execution, ordered accessed cells, per-cell saved values, current buffered own writes, and retry intent. While attempt is open, every accepted transition either advances that owner or is an admitted noninterfering/environment receipt action. Buffered own writes do not mutate committed cells. For each accessed cell, committed version at commit equals the first-read version. Then the source version-validation predicate is true and removing its stored version numbers does not change this attempt's result/commit behavior. Prove ordered emitted callback actions separately.

This is an **attempt theorem**, not yet equivalence of whole concurrent transactions. Whole-module proof also needs flat nesting, failure/retry cleanup, admission through called/stored programs, resource state retained after failure, and command/fairness profiles. Retry releases owner after atomically registering the attempt identity over its dynamic access list; wake/cancel cleanup occurs before guarded resumption. It must handle empty access lists explicitly. Because one waiter registers on multiple cells, commit may schedule its callback more than once; replacing that with a single task needs an observation/scheduling argument, not just eventual resume equality.

Source points: `Effect.ts:24274-24311` wraps `restore(effect)` and retries inconsistent attempts; `:24313-24320` checks versions; `:24322-24341` registers one key across accessed cells and clears all on wake/cancel; `:24343-24354` commits/wakes. `TxRef.ts:222-245` lazily inserts first access and mutates buffered value; `get` is `modify(identity)` at `:368`, so reads also enter the journal. `TxRef` exposes mutable runtime fields (`:61-66`); a host profile must prohibit foreign mutation rather than assume property privacy.

Do not claim general rc.112 equality: a restricted atomic implementation removes interleavings. A source attempt can read a stale state and diverge before its validation point. Finite fuel probes of nontermination do not prove divergence. Treat that as an explicit candidate until modeled, and first establish behavior inclusion under matched profiles. The existing scout and synthesis already acknowledge this distinction.

## 6. Simulation direction, divergence, and frontier clauses

For a target-restricting profile, the desired safety direction is `Beh_impl ⊆ Beh_spec` under related inputs/handles and named observations. A direct proof maps each concrete visible transition to an allowed abstract path. Equality needs the converse behavior inclusion; naming a forward simulation without saying what arrows run where is insufficient.

If concrete administrative steps may correspond to zero abstract steps, local relation preservation alone allows a concrete implementation to spin forever while the specification has terminated. The supplied small Unit model exhibits the logical omission (toy model, not a machine bug). A useful simulation package separately states:

- initialization and world correspondence;
- visible-step/finite-trace matching, with consistent world extension;
- terminal result correspondence and no new stuck state;
- live frontiers related at compatible continuation boundaries, independent of equal raw fuel;
- well-founded decrease for infinite runs made solely of unmatched administrative steps, or an explicit divergence-sensitive weak simulation;
- fairness/receptiveness assumptions, if any, and their transport.

A settled tape can still leave live fibers: existing `Behaviour.lean` and `E4-BEH-CE-002` already refute sufficiency = termination. `Scheduling.flush_fair` is finite queue service under `FlushReady`, valid owners, and enough rounds; it proves neither arbitrary-tape fairness nor progress of a new composite module. Reuse that bounded theorem only for its stated queue claim.

## 7. Composite modules: a history contract, not mandatory fixed linearization points

The critique's “arbitrary steps preserving I do not invalidate progress or safety” is too strong for progress and too weakly specified for safety. A step can preserve I while withholding the scheduler forever; I alone says nothing about which transitions another thread may perform. Conversely, legitimate module operations can change the abstract state while preserving I.

Small reusable module contract:

- public operations with requests/answers and invocation identities;
- abstract state and labeled operation/return relation (including pending operations);
- representation invariant tying shared cells **and operation-local/ghost state** to the abstract state;
- ownership/encapsulation and a rely relation of permitted environment steps;
- concrete operation steps satisfy a guarantee relation; client composition checks each guarantee is permitted by others' rely;
- history refinement preserving real-time order of nonoverlapping calls, results, cancellation and cleanup according to the chosen spec;
- progress as a separate conditional theorem, only if wanted, with scheduler/admission/availability assumptions.

A fixed atomic `refModify` can supply a linearization point for a suitable operation, but it is neither sufficient by itself (registration/wake/cancel may matter) nor universally required. Operations spanning pending work may need a logical transition at another fiber's step or history-based simulation. Do not force every future Stream/Channel/Pool/Queue contract into a false single-instruction story.

A count-only semaphore invariant illustrates the danger: both callers can read “available” then each store unavailable, preserving `0 ≤ count ≤ 1` while both proceed. The correct state relation accounts for held permits and atomic acquisition. Even then invariant-preserving endless environment steps can starve one acquire, so fairness/progress is separate. This is a toy contract countermodel, not an allegation about any existing Eff semaphore.

The strongest immediate abstraction work is to state one module contract and instantiate it for the first selected derived program using the existing machine, store relations, and Protocol typing. No new universal concurrency logic or per-module gate is needed merely to record these interfaces.

## 8. Proposed continuation signature and transaction boundary preconditions

One shape to investigate, as a contract rather than runtime code now:

```text
SuspendedDriver κ φ η St =
  { machine : existing RunMachine … κ φ η St
  , commands : List (existing Cmd … κ)
  , outer : List (DriverFrame … κ) }

DriverFrame = the existing driver's remaining work, represented as data:
  dispatcher task suffix with its owner
  | remaining flush/root-flush phase
  | an in-progress logical-clock advance
  | remaining replay decisions / completion of the selected top-level command

advanceBudget : Nat → SuspendedDriver →
  SuspendedDriver ⊎ SettledDriverResult
```

This names the missing outer-driver sort; it does not invent new program syntax or a second evaluator. `DriverFrame` would be owned next to the existing machine driver and use existing Task/RunDecision/clock data. The exact clock cursor follows the current staged timer state, including which deadline has fired and whether owed work was delivered; replay cursors belong in the replay/holder layer rather than being smuggled into the program's Stores. Existing stores remain the semantic owner of service state. Fuel is an input to `advanceBudget`, not a stored lexical capture. A zero budget returns the same suspension. A positive advance either progresses this existing cursor, returns a new suspension, or finishes the selected driver operation. The alternative is explicitly to retain no such public value and rerun from the original state/tape with more fuel.

Do **not** add a second authoritative owner field to every continuation and store. If the active attempt carries `owner`, the suspension's proof-only predicate reads it there:

```text
OwnerContinues(owner, suspension) :=
  the machine's active attempt has owner
  ∧ its pending and outer work is consistent with that attempt
  ∧ every admitted next execution step is owner-local or proved noninterfering
```

The engine/holder control contract then needs the following exact cases:

- **Entry:** world/state invariant; a settled driver boundary or a defined nested flat-transaction entry; no other open outer attempt; transitively admitted body; ownership of all effectful capabilities the body may invoke. Beginning the outer attempt installs the owner before any body operation runs. A nested entry reuses the same owner/journal.
- **Continuation:** `OwnerContinues owner suspended` implies that budget exhaustion yields `OwnerContinues owner suspended'`; neither command/driver residue nor owner is dropped. Resumption consumes the stored residual work before accepting unrelated executable work.
- **Incoming host command:** read-only inspect and independently checked receipt-only submit may be admitted if they do not modify owner-protected state. Applying a reply, firing another dispatcher, clock-driven wakes, and interrupts each require a named policy: defer until close, prove noninterference, or initiate an explicit abort path that retains cleanup ownership. It is not enough to classify all of them as “control”.
- **Close:** success publishes buffered writes and ordered delivery actions while still owned; failure discards only specified transactional writes; retry installs/removes registrations according to the protocol. Ownership is released at that specified boundary, never because a budget ran out. Allocation/ordinary-cell visibility follows the selected profile, not whole-store rollback.

No exact theorem about the version-erased implementation should be pinned until this control contract is selected. It can nevertheless be stated now parametrically over an implementation satisfying these premises, so later backends reuse the same semantic obligation.

## Verification receipt

The coordinator executed `lake env lean /private/tmp/effect4-critique-observation-tx-probes.lean` and reported exit 0. Thus the finite actual-machine controls, raw-state observation countermodel, and toy logical countermodel in that file are checked. No source changes or STM implementation were tested. The proposed signatures and transaction/module contracts above are design statements, not implemented declarations or completed correctness proofs.
