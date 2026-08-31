# Fiber/scheduler/interruption representative contract

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence:
`Effect4/Concurrency/{Fiber,Scheduler,Interrupt}.lean`

Lean battery:
`Effect4Test/Concurrency/FiberRepresentativeContract.lean`

Counterexamples: `E4-CONC-CE-001` through `E4-CONC-CE-007` in
`test/counterexamples/REGISTER.md`

Red verifier: `scripts/check-fiber-representative-red.sh`

## Claim boundary

This packet freezes one bounded concurrency representative: first-order fiber
identity and lifecycle data, explicit finite scheduling decisions, a relational
one-decision semantics, finite taped runs, and the observations required for
join, interruption masks, and cleanup.

It does not implement the representative. It does not model effect syntax,
fork-tree ownership, supervision, scopes, race combinators, priority, time,
work stealing, host tasks, result payloads, fairness, starvation freedom, or
eventual completion. It makes no Effect TypeScript compatibility or code
generation claim.

## CATEGORIES

- `inductive-data` — identifiers, statuses, decisions, refusals, and events are
  first-order data, parameterized by an externally owned terminal observation;
- `operational-semantics` — `Step` and `Runs` state the meaning of a supplied
  scheduler tape;
- `algebraic-laws` — fixed-tape uniqueness, join agreement, interruption/mask
  behavior, and cleanup safety;
- `counterexamples` — seven finite proved witnesses force the representation;
- `claim-scope` — safety is separated from fairness and finite frontier from
  every terminal or refusal arm.

## REQUIRES

1. Lean core and Std at the repository's pinned toolchain.
2. Every fiber and scheduler decision is polynomial data relative to an
   externally admitted terminal alphabet `τ`. The concurrency layer adds no
   host function, continuation, Promise, task, or callback; full reification
   later requires the terminal alphabet's separate codec/admission witness.
3. Raw initial machines cross `Machine.WellFormed` before any replay theorem is
   available. Admission requires unique fiber IDs, cleanup counts at most one,
   and the lifecycle coherence used by the cleanup and join laws.
4. State and observable trace are retained outside terminal observations and
   scheduler refusals so cleanup information is not erased.
5. Every scheduler choice relevant to the representative, including
   interrupt-versus-complete order, is present in `DecisionTape`.
6. A finite depleted tape produces `ReplayResult.frontier machine`; it never
   produces a synthetic terminal observation or scheduler refusal.
7. Concurrency does not own the failure/defect/interruption result alphabet.
   Every state and decision is parameterized by a terminal type `τ`; a small
   `InterruptBoundary τ` supplies only the distinguished interruption value.
   A later `Semantics.Exit` instantiation must prove result-arm separation.

## Public declarations

Binder names may differ. Public names, constructor order and fields, argument
roles, result types, and theorem propositions are frozen by the Lean battery.

### Existing-type and duplicate-prevention rows

All rows are native to this contract and inherit the `separateCalculus`
disposition recorded for concurrency in `PORT-MANIFEST.md`. None is a renamed
copy of an Effect TypeScript or Foldlab runtime carrier. `FIBER-PG` abbreviates
the `FIBER-PG-REPRESENTATIVE` graph in `docs/FIBER-DAG.md`.

| Stable public type | Owner | Relationship | Assurance route |
| --- | --- | --- | --- |
| `Effect4.FiberId` | `Concurrency/Fiber.lean` | canonical nominal identity for this calculus | leaf receipt linked to `FIBER-PG.identity` |
| `Effect4.FiberStatus` | `Concurrency/Fiber.lean` | canonical representative lifecycle alphabet | leaf receipt linked to `FIBER-PG.construction` |
| `Effect4.FiberState τ` | `Concurrency/Fiber.lean` | canonical passive state record; terminal observations are supplied by the owning semantics | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.InterruptMask` | `Concurrency/Interrupt.lean` | canonical mask alphabet for this calculus | leaf receipt linked to `FIBER-PG.construction` |
| `Effect4.CleanupState` | `Concurrency/Interrupt.lean` | canonical cleanup alphabet for this calculus | leaf receipt linked to `FIBER-PG.construction` |
| `Effect4.InterruptBoundary τ` | `Concurrency/Interrupt.lean` | boundary record naming the interruption observation in external `τ`; not a copied exit carrier | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.SchedulerDecision τ` | `Concurrency/Scheduler.lean` | canonical explicit decision alphabet | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.DecisionTape τ` | `Concurrency/Scheduler.lean` | derived alias of `List (SchedulerDecision τ)`, not a second decision carrier | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.Event τ` | `Concurrency/Scheduler.lean` | canonical observable-event alphabet | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.Trace τ` | `Concurrency/Scheduler.lean` | derived alias of `List (Event τ)`, not a second trace carrier | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.Machine τ` | `Concurrency/Scheduler.lean` | canonical passive state collection and trace record | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.Machine.WellFormed` | `Concurrency/Scheduler.lean` | canonical admission predicate; no duplicate checked-machine carrier | `FIBER-PG.construction` and `FIBER-PG.semantics` |
| `Effect4.Machine.Finished` | `Concurrency/Scheduler.lean` | canonical finished-state predicate used by nil-tape classification | `FIBER-PG.semantics` |
| `Effect4.SchedulerRefusal` | `Concurrency/Scheduler.lean` | passive labels; refusal behavior is owned by `Step`/`Runs` | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.StepResult τ` | `Concurrency/Scheduler.lean` | derived one-decision result envelope for `Step` | leaf receipt linked to `FIBER-PG.semantics` |
| `Effect4.ReplayResult τ` | `Concurrency/Scheduler.lean` | canonical finite-run observation envelope; its `frontier` arm carries only the stopped machine | leaf receipt linked to `FIBER-PG.semantics` |

The operational relations, public projections, and theorem spine inherit the
same unique owner and contribute to `FIBER-PG`; they do not mint more carriers
or graphs.

### D0 — passive first-order leaves

```lean
structure FiberId where
  value : Nat

inductive FiberStatus
  | runnable
  | running
  | waiting (target : FiberId)
  | finalizing
  | done

inductive InterruptMask
  | unmasked
  | masked

inductive CleanupState
  | notStarted
  | pending
  | done
```

Each D0 carrier has `DecidableEq` and `Repr`. The future terminal type remains
owned by `Semantics.Exit`; this packet does not duplicate its typed failure,
defect, or interruption constructors.

```lean
inductive SchedulerRefusal
  | unknownFiber (id : FiberId)
  | invalidLifecycle (id : FiberId)
```

Scheduler refusal is nominally distinct from both terminal observations and
finite tape exhaustion. Exhaustion is represented only by the
`ReplayResult.frontier` arm, so Scheduler does not mint a duplicate Frontier
carrier. Constructor census and exhaustive-case theorems are sufficient local
receipts for these passive finite alphabets; no separate proof graph is made.

### D1 — fiber and machine state

```lean
structure InterruptBoundary (τ : Type u) where
  interrupted : τ

structure FiberState (τ : Type u) where
  id : FiberId
  status : FiberStatus
  terminal : Option τ
  mask : InterruptMask
  interruptPending : Bool
  cleanup : CleanupState
  cleanupCount : Nat

structure Machine (τ : Type u) where
  fibers : List (FiberState τ)
  trace : Trace τ
```

The public projections are:

```lean
Machine.fiber : Machine τ -> FiberId -> Option (FiberState τ)
Machine.terminal : Machine τ -> FiberId -> Option τ
Machine.mask : Machine τ -> FiberId -> Option InterruptMask
Machine.interruptPending : Machine τ -> FiberId -> Option Bool
Machine.cleanupState : Machine τ -> FiberId -> Option CleanupState
Machine.cleanupCount : Machine τ -> FiberId -> Nat
Event.cleanupId? : Event τ -> Option FiberId
Machine.cleanupEventIds : Machine τ -> List FiberId
```

The Lean battery freezes the projection equations: `fiber` is the first list
entry with the requested ID; `terminal` reads the fiber's explicit optional
terminal observation;
mask, pending interruption, and cleanup state map the resolved fiber; and a
missing cleanup count is zero. `Event.cleanupId?` recognizes exactly
`cleanupFinished`, and `Machine.cleanupEventIds` is exactly the trace's
filtered cleanup identities. These equations prevent the operational laws
from being satisfied by unrelated fixture projections. It also freezes the
machine projection of every `StepResult` and `ReplayResult` constructor.

`Machine.cleanupCount` is observational bookkeeping used to state at-most-once
cleanup. Raw `Machine` remains first-order data; this predicate is its only
admission boundary and does not mint a second machine carrier:

```lean
structure Machine.WellFormed (machine : Machine τ) : Prop where
  idsUnique : (machine.fibers.map FiberState.id).Nodup
  cleanupBounded : forall fiber, fiber ∈ machine.fibers ->
    fiber.cleanupCount <= 1
  cleanupEventsUnique : machine.cleanupEventIds.Nodup
  cleanupEventsClosed : forall id, id ∈ machine.cleanupEventIds ->
    exists fiber, fiber ∈ machine.fibers /\ fiber.id = id
  cleanupEventAgreement : forall fiber, fiber ∈ machine.fibers ->
    (fiber.id ∈ machine.cleanupEventIds <-> fiber.cleanupCount = 1)
  activeCleanup : forall fiber, fiber ∈ machine.fibers ->
    fiber.status.Active -> fiber.terminal = none /\
      fiber.cleanup = .notStarted /\ fiber.cleanupCount = 0
  finalizingCleanup : forall fiber, fiber ∈ machine.fibers ->
    fiber.status = .finalizing ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = .pending /\ fiber.cleanupCount = 0
  doneCleanup : forall fiber, fiber ∈ machine.fibers ->
    fiber.status = .done ->
    (exists result, fiber.terminal = some result) /\
      fiber.cleanup = .done /\ fiber.cleanupCount = 1
  pendingActive : forall fiber, fiber ∈ machine.fibers ->
    fiber.interruptPending = true ->
    fiber.mask = .masked /\ fiber.status.Active
  waitingClosed : forall fiber target, fiber ∈ machine.fibers ->
    fiber.status = .waiting target ->
    exists targetFiber, targetFiber ∈ machine.fibers /\
      targetFiber.id = target

Machine.wellFormedDecidable :
  forall [DecidableEq τ] (machine : Machine τ), Decidable machine.WellFormed

def Machine.Finished (machine : Machine τ) : Prop :=
  forall fiber, fiber ∈ machine.fibers ->
    fiber.status = .done
```

The exact `Machine.finished_iff` theorem in the Lean battery freezes that
definition. Admission rules out a raw initial cleanup count above one,
duplicate or orphan cleanup events, and disagreement between retained cleanup
history and the per-fiber count. It prevents a done fiber from being reset
into an active cleanup lifecycle, makes waiting targets closed, and states
only the coherence used here. It imposes no fairness or scheduler policy.

### D2 — decisions and observable trace

```lean
inductive SchedulerDecision (τ : Type u)
  | schedule (id : FiberId)
  | join (waiter target : FiberId)
  | requestInterrupt (requester target : FiberId)
  | enterMask (id : FiberId)
  | exitMask (id : FiberId)
  | complete (id : FiberId) (result : τ)
  | cleanup (id : FiberId)

abbrev DecisionTape (τ : Type u) := List (SchedulerDecision τ)

inductive Event (τ : Type u)
  | scheduled (id : FiberId)
  | joinWaiting (waiter target : FiberId)
  | joinObserved (waiter target : FiberId) (result : τ)
  | interruptRequested (requester target : FiberId)
  | interruptDeferred (target : FiberId)
  | interruptDelivered (target : FiberId)
  | maskEntered (id : FiberId)
  | maskExited (id : FiberId)
  | completed (id : FiberId) (result : τ)
  | cleanupFinished (id : FiberId)

abbrev Trace (τ : Type u) := List (Event τ)
```

`complete` is a first-order supplied observation of a representative body
result, not a body evaluator. `schedule` is the explicit nondeterministic
choice. Interrupt/completion ordering is therefore part of the tape.

### D3 — operational results and relations

```lean
inductive StepResult (τ : Type u)
  | advanced (machine : Machine τ)
  | refused (reason : SchedulerRefusal) (machine : Machine τ)

inductive ReplayResult (τ : Type u)
  | finished (machine : Machine τ)
  | refused (reason : SchedulerRefusal) (machine : Machine τ)
  | frontier (machine : Machine τ)

StepResult.machine : StepResult τ -> Machine τ
ReplayResult.machine : ReplayResult τ -> Machine τ
stepEval : InterruptBoundary τ -> Machine τ -> SchedulerDecision τ -> StepResult τ
Step : InterruptBoundary τ -> Machine τ -> SchedulerDecision τ -> StepResult τ -> Prop
Runs : InterruptBoundary τ -> Machine τ -> DecisionTape τ -> ReplayResult τ -> Prop
```

The relation over all possible decisions may branch; a fixed machine and fixed
decision has at most one result. `Runs` consumes the supplied finite tape. A
run is `finished` only when every admitted fiber is done. An invalid taped
decision is a refusal. Tape depletion before finish is a frontier, not a
refusal. The existence laws below make both relations nonempty where the
contract requires behavior.

`Runs` is mechanically tied to `Step`, not an unrelated relation. The exact
Lean `runs_nil_iff` and `runs_cons_iff` laws freeze this recursion:

- on an admitted empty tape, return `.finished initial` exactly when
  `initial.Finished`, otherwise `.frontier initial`;
- on `decision :: rest`, either an advanced `Step` continues with `Runs` on
  the remaining tape, or a refused `Step` stops with the same refusal and
  machine.

## ENSURES — public theorem spine

### Passive leaf receipts

The battery freezes exhaustive case receipts for `FiberStatus`,
`InterruptMask`, `CleanupState`, `SchedulerRefusal`, `SchedulerDecision τ`,
and `Event τ`. These receipts make no operational claim. Terminal cases and a
shared frontier alphabet belong to Semantics, not this packet.

### Operational determinism

```lean
step_deterministic :
  Step boundary before decision left ->
  Step boundary before decision right -> left = right

fixedTape_deterministic :
  Runs boundary initial tape left -> Runs boundary initial tape right ->
    left = right

step_preserves_wellFormed :
  before.WellFormed -> Step boundary before decision result ->
    result.machine.WellFormed

runs_preserves_wellFormed :
  initial.WellFormed -> Runs boundary initial tape result ->
    result.machine.WellFormed

finite_replay_total :
  initial.WellFormed -> exists result, Runs boundary initial tape result

step_total :
  before.WellFormed -> exists result, Step boundary before decision result

step_iff
runs_nil_iff
runs_cons_iff
```

This is the only determinism claim. It is conditional on the exact same finite
tape. Totality is only for admitted machines. There is no untaped determinism
or fairness theorem. `Step` is extensionally fixed by `stepEval`, and `Runs`
is fixed by the nil/cons equations, so neither relation may be an unrelated
total oracle.

The `stepEval_*` theorem family is exhaustive over every decision constructor
and lifecycle branch. Each advanced clause fixes the exact replacement state
and chronological trace suffix through `Machine.transition`; each refusal
clause fixes the refusal and unchanged machine. Scheduling covers missing,
runnable, and invalid fibers. Join covers missing/self/invalid inputs,
blocking a running waiter on any target not yet `.done`, including a target in
finalization, and observing only a `.done` target after cleanup. A malformed
raw `.done` target with no stored terminal observation has its own exact
`.invalidLifecycle` refusal equation; admission makes that branch unreachable
for a well-formed machine.
Interrupt requests cover missing, every active status including waiting, both
mask states, and inactive refusal. Mask entry/exit, completion, and atomic
pending-to-done cleanup have similarly exhaustive equations. Completion is
admitted only from a running, unmasked fiber with no pending interruption.
A masked fiber must first execute `exitMask`; when an interruption is pending,
that step delivers interruption instead of allowing completion to erase it.

### Required positive operational cases

The implication laws are not allowed to hold vacuously. The Lean battery
freezes existence and observation theorems for every representative clause:

```lean
done_join_exists
waiting_join_exists
masked_request_exists
unmasked_request_exists
enter_mask_exists
pending_unmask_exists
unmask_without_pending_exists
completion_exists
cleanup_exists
unknown_schedule_refuses
invalid_completion_refuses
runs_nil_finished
runs_nil_frontier
representative_inputs_exist
exists_representative_finished_run
```

Respectively, these cover every decision constructor in admitted valid states.
The exact schedule equation covers scheduling; the inhabited cases cover
blocking join, done join, masked and unmasked interrupt requests,
mask entry, unmask with and without a pending request, unmasked completion with
no pending interruption, and atomic cleanup. They also require exact
`.unknownFiber` and `.invalidLifecycle`
refusals, so every refusal constructor has an operational call site. The
requester and target must exist, and every interrupt or mask transition names
an active lifecycle. Inhabited admitted preconditions make those clauses
non-vacuous.
The remaining obligations freeze exact nil-tape finished/frontier
classification and at least one admitted nonempty finite run that finishes.
Their full propositions are frozen in the Lean battery.

Together with `finite_replay_total`, these reject empty `Step`/`Runs`, a
constant-refusal interpreter, and a constant-frontier interpreter. They do not
add fairness or infinite execution.

### Join agreement

```lean
join_agreement :
  before.WellFormed ->
  before.fiber target = some targetState ->
  targetState.status = .done ->
  Step boundary before (.join waiter target) (.advanced after) ->
  before.terminal target = some result ->
  after.terminal target = some result /\
  after.cleanupState target = before.cleanupState target /\
  after.trace = before.trace ++ [.joinObserved waiter target result]

double_join_agreement :
  before.WellFormed ->
  before.fiber target = some targetState ->
  targetState.status = .done ->
  before.terminal target = some result ->
  waiter₁ ≠ target -> waiter₂ ≠ target ->
  Step boundary before (.join waiter₁ target) (.advanced middle) ->
  Step boundary middle (.join waiter₂ target) (.advanced after) ->
  middle.terminal target = some result /\
  after.terminal target = some result /\
  after.cleanupCount target = before.cleanupCount target
```

Join-before-done is an advanced blocking transition: a running waiter becomes
`.waiting target` and appends exactly `.joinWaiting waiter target`. This also
applies while the target is finalizing. Only after the atomic cleanup step has
moved the target to `.done` may a later taped join resume the waiter and append
`joinObserved` with the stored result. Join neither consumes the result nor
runs cleanup.

### Interruption and masks

```lean
unmasked_interrupt_delivers :
  before.WellFormed ->
  before.fiber requester = some requesterState ->
  before.fiber target = some targetState -> targetState.status.Active ->
  targetState.mask = .unmasked ->
  Step boundary before (.requestInterrupt requester target) (.advanced after) ->
  after.terminal target = some boundary.interrupted /\
  (after.fiber target).map FiberState.status = some .finalizing /\
  after.cleanupState target = some .pending

masked_interrupt_defers :
  before.WellFormed ->
  before.fiber requester = some requesterState ->
  before.fiber target = some targetState -> targetState.status.Active ->
  targetState.mask = .masked ->
  Step boundary before (.requestInterrupt requester target) (.advanced after) ->
  after.interruptPending target = some true /\
    after.terminal target = before.terminal target

unmask_delivers_pending :
  before.WellFormed ->
  before.fiber target = some fiber -> fiber.status.Active ->
  fiber.mask = .masked -> fiber.interruptPending = true ->
  Step boundary before (.exitMask target) (.advanced after) ->
  after.interruptPending target = some false /\
  after.mask target = some .unmasked /\
  after.terminal target = some boundary.interrupted /\
  (after.fiber target).map FiberState.status = some .finalizing
```

Delivery on unmask happens before another body action can be scheduled for the
target. Waiting is active and interruptible. Completed and finalizing fibers
refuse new interrupt/mask transitions. These restrictions prevent resetting a
completed cleanup lifecycle. Ordering is fixed by exact trace deltas.

### Cleanup safety

```lean
cleanup_at_most_once :
  initial.WellFormed -> Runs boundary initial tape result ->
    result.machine.cleanupCount id <= 1

cleanup_events_at_most_once :
  initial.WellFormed -> Runs boundary initial tape result ->
    result.machine.cleanupEventIds.Nodup

cleanup_events_agree :
  initial.WellFormed -> Runs boundary initial tape result ->
  forall fiber, fiber ∈ result.machine.fibers ->
    (fiber.id ∈ result.machine.cleanupEventIds <->
      fiber.cleanupCount = 1)

cleanup_count_monotone :
  before.WellFormed -> Step boundary before decision result ->
    before.cleanupCount id <= result.machine.cleanupCount id

cleanup_preserves_terminal :
  before.WellFormed ->
  before.fiber id = some fiber ->
  fiber.status = .finalizing -> fiber.terminal = some terminal ->
  fiber.cleanup = .pending ->
  Step boundary before (.cleanup id) (.advanced after) ->
  after.terminal id = some terminal /\
  (after.fiber id).map FiberState.status = some .done /\
  after.cleanupState id = some .done /\ after.cleanupCount id = 1 /\
  after.trace = before.trace ++ [.cleanupFinished id]

cleanup_safe_on_finish :
  initial.WellFormed ->
  Runs boundary initial tape (.finished final) ->
  final.terminal id = some terminal ->
  final.cleanupState id = some .done /\
    final.cleanupCount id = 1
```

Cleanup is one atomic `pending -> done` transition and appends exactly one
`cleanupFinished` event. The structural `transition_cleanupEventIds` equation
ties appended events to retained history. Stepwise count monotonicity plus
admission prevents a `1 -> 0 -> 1` reset from satisfying only the final bound;
event uniqueness and count agreement rule out duplicate cleanup observations.
The final law is a safety statement about runs already classified as finished,
not eventual cleanup or fairness.

`interrupt_complete_order_distinct` supplies one admitted ground machine and
the two exact nonempty tapes. Under the frozen policy, the first decision moves
the target to finalizing; the second is then refused without altering that
machine. The two replay results therefore preserve different terminal or
trace observations and are unequal. The theorem requires no inequality in
`τ`; for a singleton terminal alphabet, the trace still distinguishes order.

## Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `E4-CONC-CE-001` | untaped race admits two different next traces | put scheduler choice in the tape; claim determinism only for a fixed tape |
| `E4-CONC-CE-002` | interrupt-before-complete and complete-before-interrupt leave different traces before the second action refuses; terminal values may coincide for a singleton `τ` | tape and trace the order; prove unequal replay results with `interrupt_complete_order_distinct` on admitted runs |
| `E4-CONC-CE-003` | masked interruption cannot be reported immediately as terminal interruption | retain pending request; deliver at unmask before another body action |
| `E4-CONC-CE-004` | projecting only the terminal outcome erases whether cleanup ran | retain machine state and trace outside terminal/error arms |
| `E4-CONC-CE-005` | a second join must not rerun cleanup or consume the terminal result | make join a repeatable read-only observation |
| `E4-CONC-CE-006` | empty `Step` and `Runs` satisfy every implication-only old law | require admission, total `Step`, exhaustive `stepEval` equations and trace deltas, total finite replay, exact `Runs` recursion through `Step`, projection equations, positive clause coverage, exact nil classification, and a finite finished witness |
| `E4-CONC-CE-007` | a count bounded by one admits a trace that records the same cleanup twice | extract cleanup event identities and admit only unique, closed histories that agree with per-fiber counts |

The seven witnesses are finite self-contained breaker models. They prove the attacks,
not the eventual production laws.

## Trust and acceptance

The checker is Lean's kernel at the pinned toolchain. `decide` is allowed for
finite propositions. `native_decide`, `sorry`, `admit`, `Classical.choice`, and
new axioms are not allowed in the packet or implementation.

The breaker phase is accepted when:

```sh
lake env lean Effect4Test/Counterexamples/Concurrency/FiberRepresentative.lean
scripts/check-fiber-representative-red.sh
```

both exit zero, while this direct implementation contract exits nonzero:

```sh
lake env lean Effect4Test/Concurrency/FiberRepresentativeContract.lean
```

The red verifier must recognize the frozen missing declaration/law sentinels;
an unrelated parse, import, toolchain, or counterexample failure is not a clean
red result.

The later builder phase requires the direct contract and complete project test
suite to exit zero, plus `#print axioms` receipts for every public theorem. It
still does not authorize Effect host cutover. Direct runtime/type fixtures and
an auxiliary language-service diagnostic gate belong to a later host evidence
node.
