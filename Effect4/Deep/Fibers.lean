import Effect4.Runtime.Runtime
import Effect4.Concurrency.Supervision

/-!
# Deep spike: the program-carrying fiber machine

Status: design spike, 2026-09-03, third pass. Module `Deep.Fibers` of the non-default `Deep`
library (`lakefile.toml`, `srcDir = "workshop"`); built with `lake build Deep.Fibers`.
Contract: `docs/research/2026-09-03-fiber-machine-pass-a.md`. Plan:
`docs/research/2026-09-03-deep-plan.md`. This pass folds in every finding of the three
spikes (`2026-09-03-spike-s1-prim-parking.md`, `-s2-stores-witnesses.md`,
`-s3-fork-flow.md`): the three park primitives are `Prim` constructors now (S1), the
`AsyncFinalizer` frame is pushed where rc.112 pushes it, a stuck machine is observable rather
than a silent spin (S3 §5.1), the interp can refuse a thunk (S3 §5.2), a stateful `sync`
drains the resumes it owes on the spot (S2 M1), a program can mask its own fiber (M2), a
cancel name knows the waiter it splices out (M3), scope linking knows its mode (M4), an
interrupt carries the caller's annotations (M5), a countdown collects the exits it awaited
(M6), the scope hooks can say "unknown" (M7), a settled race interrupts its unlaunched
entrants instead of deleting them (M8), and M9 (the old alphabet's missing suspended phase)
is moot since the projections were retired.

One source of truth. A `RunFiber` holds the frame machine's five fields
(`Effect4/Runtime/Runtime.lean`, reused unchanged), the parking state, the exit, the
supervision fields, and the per-fiber dispatcher. The scheduler and supervision calculi this
machine replaced were retired on 2026-09-04
(`docs/research/2026-09-04-retire-old-machines.md`); only their vocabulary
(`Effect4/Concurrency/Supervision.lean`) remains.

Every arm names the rc.112 line it transcribes (`vendor/effect-4.0.0-rc.112/src/`,
`internal/effect.ts` unless another file is named). Where rc.112 leaves a choice to the
host, the machine takes a `RunDecision` from a tape. Tape exhaustion and fuel exhaustion
are live frontiers (DB-04); so is a stuck machine, which is what a state rc.112 cannot reach
(a join on a handle the machine does not hold, an unknown scope key) becomes here, observably.
The error channel is `Cause ε δ ι α` and `Exit` everywhere.
-/

namespace Effect4.Deep

universe u v

open Effect4

-- Core derives no decidable equality for Except; the machine's parkOf answers one, so
-- witnesses compare them.
deriving instance DecidableEq for Except

/-! ## Parking, tasks, observers, dispatcher -/

/-- The one park the frame alphabet does not spell: `fiberJoin`/`fiberAwait` (`:5291`,
`:5304`), an observer on the target answered at once when the target has exited
(`:561-562`). `yieldNowWith` and `Async` are `Prim` constructors (S1). -/
inductive ParkKind
  | join (target : FiberId) (mode : Supervision.ObserverMode)
deriving DecidableEq

/-- rc.112 `_yielded`: absent, or the resume guard `resumed = true` (`:990-992`, `:1128-1130`),
which a token names exactly. -/
inductive Parked
  | notParked
  | withGuard (token : Nat)
deriving DecidableEq, Repr

/-- What a countdown park continues with when its last observer fires. -/
inductive Resume (ν : Type u)
  /-- The awaited exits as a value (`fiberAwaitAll`, `:779`). -/
  | exitsValue
  /-- `exitVoid` (`awaitAllChildren`, `interruptAll`). -/
  | void
  /-- A named continuation applied to the exits value; the exit path uses `restoreName`. -/
  | continueWith (name : ν)
deriving DecidableEq

/-- One outstanding park. An `Async` registration (`:1117-1140`) carries whether it pushed an
`AsyncFinalizer` frame; a countdown park (`fiberAwaitAll`, `awaitAllChildren`, the exit
path's child interruption, race cleanup) carries how many observers must still fire, the
exits collected so far (M6), and what resumes it. -/
structure Pending (ν : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  token : Nat
  waitingOn : Option FiberId
  remaining : Nat
  collected : List (Exit β ε δ ι α)
  resumeWith : Resume ν
  /-- `Effect.all`/`forEach` with concurrency: the first failing exit interrupts the
  outstanding targets (S5 §7.4, `Layer.ts:1597-1598`); the countdown still waits for them. -/
  failFast : Bool
  /-- The targets still outstanding, for a fail-fast interruption. -/
  outstanding : List FiberId
deriving DecidableEq

/-- Every `addObserver` shape (`:565`): join and await (`:561-562`), the child's untrack
observer (`:5281`), `forkIn`'s key-dropping observer (`:5370-5372`), a countdown for an
await-all, a race entrant's callback, and a runtime entry's callback (`runCallback`,
`runPromise`). -/
inductive Observer
  | resumeAwait (waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode)
  | untrackChild (parent : FiberId)
  | dropScopeFinalizer (scope : Nat) (key : Nat)
  | countdown (waiter : FiberId) (token : Nat)
  | raceCallback (race : Nat)
  | callback (key : Nat)
deriving DecidableEq

/-- The two task shapes ever enqueued: a deferred child start (`:5277`) and a yield resume
(`:986`). Everything else resumes synchronously through `resume(effect)` (`:1121`). -/
inductive Task (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  | start (child : FiberId)
  | resume (target : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
deriving DecidableEq

/-- `Scheduler.ts:105-131`: buckets in ascending priority, FIFO within a bucket. -/
structure Bucket (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  priority : Nat
  tasks : List (Task ν σ β ε δ ι α)
deriving DecidableEq

/-- One `MixedSchedulerDispatcher` (`Scheduler.ts:188-233`); every fiber lazily owns one
(`:552-555`). `armed` is "the host callback is scheduled" (`Scheduler.ts:207-212`). -/
structure Dispatcher (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  buckets : List (Bucket ν σ β ε δ ι α)
  armed : Bool
deriving DecidableEq

namespace Dispatcher

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

def empty : Dispatcher ν σ β ε δ ι α := ⟨[], false⟩

def insert (priority : Nat) (task : Task ν σ β ε δ ι α) :
    List (Bucket ν σ β ε δ ι α) → List (Bucket ν σ β ε δ ι α)
  | [] => [⟨priority, [task]⟩]
  | bucket :: rest =>
    if bucket.priority = priority then ⟨bucket.priority, bucket.tasks ++ [task]⟩ :: rest
    else if priority < bucket.priority then ⟨priority, [task]⟩ :: bucket :: rest
    else bucket :: insert priority task rest

/-- `Scheduler.ts:105-131` plus arming on the first task (`:207-212`). -/
def enqueue (d : Dispatcher ν σ β ε δ ι α) (priority : Nat) (task : Task ν σ β ε δ ι α) :
    Dispatcher ν σ β ε δ ι α :=
  ⟨insert priority task d.buckets, true⟩

/-- `runTasks` drains the snapshot once (`Scheduler.ts:225-233`): a task enqueued during
the drain waits for the next host task. -/
def drain (d : Dispatcher ν σ β ε δ ι α) :
    List (Task ν σ β ε δ ι α) × Dispatcher ν σ β ε δ ι α :=
  ((d.buckets.map Bucket.tasks).flatten, ⟨[], false⟩)

end Dispatcher

/-! ## The fiber -/

/-- rc.112 `FiberImpl` (`:505-555`), seventeen fields read through one record. `frame` is
the five-field machine of `Runtime.lean`; `running` (`:537`), `parked` (`:536`), `pending`,
`finalizing` (the exit held while the children are interrupted, `:613-617`), `exit`
(`:533`), the op counter and the two `Context`-cached budget fields (`:530`, `:549-550`),
`yieldOverride` (the tape's `shouldYield`, `Scheduler.ts:78-81`), `observers` (`:532`),
`children` (`:534`), `dispatcher` (`:552`) and `context` (`:541`) are the rest. -/
structure RunFiber (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) : Type (max u v) where
  id : FiberId
  frame : FrameFiber ν σ β ε δ ι α
  running : Bool
  parked : Parked
  pending : List (Pending ν β ε δ ι α)
  finalizing : Option (Exit β ε δ ι α)
  exit : Option (Exit β ε δ ι α)
  currentOpCount : Nat
  maxOpsBeforeYield : Nat
  preventYield : Bool
  yieldOverride : Option Bool
  observers : List Observer
  children : List FiberId
  dispatcher : Dispatcher ν σ β ε δ ι α
  context : χ
deriving DecidableEq

namespace RunFiber

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}

def interruptPending (f : RunFiber ν σ β ε δ ι α χ) : Bool :=
  f.frame.deferredInterrupt || f.frame.interruptedCause.isSome

/-- `new FiberImpl(context, interruptible)` (`:512-514`) with the modelled fields; the
budget fields are read off the context as `setContext` does (`:726-727`). -/
def make (id : FiberId) (current : Prim ν σ β ε δ ι α) (interruptible : Bool)
    (budget : Nat × Bool) (context : χ) : RunFiber ν σ β ε δ ι α χ where
  id := id
  frame := { FrameFiber.start current with interruptible := interruptible }
  running := false
  parked := Parked.notParked
  pending := []
  finalizing := none
  exit := none
  currentOpCount := 0
  maxOpsBeforeYield := budget.1
  preventYield := budget.2
  yieldOverride := none
  observers := []
  children := []
  dispatcher := Dispatcher.empty
  context := context

/-- Park on `p.token`, remembering what resumes it. -/
def park (f : RunFiber ν σ β ε δ ι α χ) (p : Pending ν β ε δ ι α) : RunFiber ν σ β ε δ ι α χ :=
  { f with parked := Parked.withGuard p.token, pending := f.pending ++ [p] }

end RunFiber

/-! ## What a `withFiber` thunk can do

rc.112 reaches the raw fiber only through `withFiber` (`:1147`); every fiber-level
operation is one of these shapes. A parameter of the interp names which one a thunk is. -/
inductive WithFiberAction (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) : Type (max u v)
  /-- `forkUnsafe` (`:5264-5284`): `forkChild`, `forkDetach`, `forkDaemon` by options. -/
  | fork (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions)
  /-- `forkIn` (`:5364-5378`): a daemon linked to a scope by a keyed, self-guarded finalizer. -/
  | forkIn (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
      (key : Nat)
  /-- `forkScoped` (`:5400-5406`): `forkIn` on the ambient `Scope` service. -/
  | forkScoped (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (key : Nat)
  /-- `fiberRunIn` (`:5447-5461`): bind an existing fiber to a scope by an unguarded finalizer. -/
  | runIn (target : FiberId) (scope : Nat) (key : Nat)
  /-- `fiberInterrupt` (`:859`): record with the running fiber's id, then await the target. -/
  | interrupt (target : FiberId)
  /-- A scope's fiber finalizer (`:5369-5371`): interrupt unless the interruptor is the
  fiber itself, then await. -/
  | interruptScoped (target : FiberId)
  /-- `fiberInterruptAll` / `fiberInterruptAllAs` (`:895`, `:913`): record on every target
  first, then await them all. `none` means the running fiber's own id. -/
  | interruptAll (targets : List FiberId) (interruptor : Option FiberId)
  /-- `fiberAwaitAll` (`:779`, `:5318-5322`): a countdown over the targets' exits, answered
  as the list of exits. -/
  | awaitAll (targets : List FiberId)
  /-- `Effect.all`/`forEach` with concurrency (`Layer.ts:1597-1598`): await all, but the
  first failing exit interrupts the outstanding targets with the awaiter's id. -/
  | awaitAllFailFast (targets : List FiberId)
  /-- `awaitAllChildren`'s snapshot before the body runs (`:5318`). -/
  | snapshotChildren
  /-- `awaitAllChildren`'s exit half: await the children added since the snapshot. -/
  | awaitNewChildren (snapshot : List FiberId)
  /-- `raceAll`: immediate daemons in order until an observed success, failures in order,
  the empty race pending until interrupted (`Supervision.RaceAllState`). -/
  | raceAll (entrants : List (Prim ν σ β ε δ ι α))
  /-- `uninterruptible`/`interruptible` bodies (`:4302-4310`, `:4331-4352`): set the flag,
  push the restoring frame, and fail now if a cause is pending (M2). -/
  | setInterruptible (body : Prim ν σ β ε δ ι α) (flag : Bool)
  /-- `setContext` (`:709-727`): the context and its two cached budget fields. -/
  | setContext (context : χ)
  /-- `fiber.context` as a value (`getContext`, `:2153`). -/
  | getContext
  /-- `withFiberId`. -/
  | getId
  /-- `scopeClose` from the fiber (`Scope.ts` via `:3826`): the store builds the close
  program for the scope's strategy; the closing fiber's mask is inherited by a parallel
  strategy's daemons. -/
  | closeScope (scope : Nat) (exit : Exit β ε δ ι α)
  /-- The interp refuses this thunk: the fiber fails with `cause`, visibly (S3 §5.2). -/
  | refuse (cause : Cause ε δ ι α)
deriving DecidableEq

/-! ## Events, races, the machine, the decisions, the interp -/

inductive RunEvent (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) : Type (max u v)
  | forked (parent child : FiberId) (daemon : Bool)
  | started (fiber : FiberId)
  | scheduledTask (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α)
  | ranTask (owner : FiberId) (task : Task ν σ β ε δ ι α)
  | yieldInjected (fiber : FiberId) (atOp : Nat)
  | parkedOn (fiber : FiberId) (token : Nat)
  | resumedWith (fiber : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
  | interruptRecorded (interruptor : Option FiberId) (target : FiberId)
  | interruptDeferred (target : FiberId)
  | childrenInterrupted (parent : FiberId) (children : List FiberId)
  | observerFired (fiber : FiberId) (observer : Observer)
  | frame (fiber : FiberId) (event : FrameEvent ν σ β ε δ ι α)
  | finalizerProgram (fiber : FiberId) (finalizer : ν) (exit : Exit β ε δ ι α)
  | scopeLinked (mode : Supervision.ScopeMode) (scope : Nat) (key : Nat) (fiber : FiberId)
  | scopeClosedOnLink (scope : Nat) (fiber : FiberId)
  | raceStarted (race : Nat) (host : FiberId) (entrants : List FiberId)
  | raceLaunched (race : Nat) (entrant : FiberId)
  | raceSkipped (race : Nat) (entrant : FiberId)
  | raceSettled (race : Nat) (exit : Exit β ε δ ι α)
  | contextSet (fiber : FiberId) (context : χ)
  | callback (key : Nat) (exit : Exit β ε δ ι α)
  | exited (fiber : FiberId) (exit : Exit β ε δ ι α)
deriving DecidableEq

/-- Why the machine stopped: a state rc.112 cannot reach, made observable (DB-04 forbids a
silent spin; a frontier must be a frontier). -/
inductive Stuck
  | unknownFiber (id : FiberId)
  | unknownScope (scope : Nat)
deriving DecidableEq, Repr

/-- One `raceAll` in flight: its host, the host's park token, and the frozen bookkeeping of
`Supervision.RaceAllState`, reused as is. -/
structure Race (β : Type v) (ε δ ι α : Type u) : Type (max u v) where
  id : Nat
  host : FiberId
  token : Nat
  state : Supervision.RaceAllState β ε δ ι α
  settled : Bool

/-- The process: every live fiber, the races, the id and token counters, the global
middleware latch (`:6656-6658`), the service state the stores live in, the trace, and the
stuck marker. -/
structure RunMachine (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) :
    Type (max u v) where
  fibers : List (RunFiber ν σ β ε δ ι α χ)
  races : List (Race β ε δ ι α)
  nextId : Nat
  nextToken : Nat
  nextRace : Nat
  middlewareInstalled : Bool
  state : St
  trace : List (RunEvent ν σ β ε δ ι α χ)
  stuck : Option Stuck

/-- The decisions rc.112 leaves to the host or the caller (Pass A §1). -/
inductive RunDecision (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- (a) the host fires this fiber's dispatcher: drain once, run the tasks in order. -/
  | fire (owner : FiberId)
  /-- the sync scheduler's `flush` (`Scheduler.ts`): every armed dispatcher, in fiber order,
  until none is armed. -/
  | flush
  /-- a fiber evaluated now: the root's synchronous start (`runFork`, `:5423`). -/
  | evaluate (fiber : FiberId)
  /-- (b) an override of `shouldYield` for the fiber's next injection check. -/
  | yieldVerdict (fiber : FiberId) (verdict : Bool)
  /-- (c) an external `resume(effect)` (`:1121`) for a parked async. -/
  | answerAsync (fiber : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
  /-- (d) `interruptUnsafe(fiberId, annotations)` (`:574`): the interruptor the wire drops
  and the caller's annotations (M5); `none` is `runFork`'s abort signal (`:5427-5429`). -/
  | interruptFrom (interruptor : Option FiberId) (annotations : ReasonAnnotations α)
      (target : FiberId)
  /-- (e) the `interruptChildren` middleware latch (`:6656-6658`). -/
  | installMiddleware
deriving DecidableEq

/-- What gives names meaning at the machine level. Extends the frame machine's pure
`PrimInterp` (now with `cancelThenFail`, S1) with the store interface (Pass A Q2), the
classifications the frame machine cannot make, and the values the machine has to mint. A
parameter, never canonical content. -/
structure RunInterp (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v))
    extends PrimInterp ν σ β ε δ ι α where
  /-- Which primitives are a `join`/`await` park (the frame alphabet has no constructor), or
  a refused one: a `join` whose request is not a fiber handle fails with the cause the
  interp gives it rather than falling through to the oracle (S3 §9). -/
  parkOf : Prim ν σ β ε δ ι α → Option (Except (Cause ε δ ι α) ParkKind)
  /-- What a `withFiber` thunk does. -/
  withFiberOf : σ → Option (WithFiberAction ν σ β ε δ ι α χ)
  /-- A `sync` thunk that reads or writes the service state; `none` falls back to the pure
  `syncValue`. Ref, Deferred and Scope operations live here. -/
  syncState : σ → St → Option (St × β)
  /-- `register(resume, signal)` (`:1117`): update the store (a waiter added), and either
  resume synchronously with a primitive (`:1120-1126`) or park. -/
  registerAsync : ν → FiberId → Nat → St → St × Option (Prim ν σ β ε δ ι α)
  /-- Resumes the store owes now (a completed Deferred's waiters, in registration order,
  `Deferred.ts:1655-1659`); resumed synchronously, inside the completing `sync` (M1). -/
  dueResumes : St → List (FiberId × Nat × Prim ν σ β ε δ ι α) × St
  /-- Attach the waiter's identity to a cancel name, so the `AsyncFinalizer` frame's
  `contE` can splice the waiter out (`Deferred.ts:181-184`, M3). -/
  cancelName : ν → FiberId → Nat → ν
  /-- The cancel name of an `Async` with a signal but no cancel effect: abort the
  controller (`:1134-1140`). -/
  abortName : ν
  /-- An `OnExit` finalizer that is a *program*, run as one (`:4021`), rather than the pure
  `finalizerExit` shortcut of the frame machine; `none` keeps the shortcut. -/
  finalizerProgram : ν → Exit β ε δ ι α → Option (Prim ν σ β ε δ ι α)
  /-- The continuation names for `flatMap(finalizer(exit), () => exit)` and its failure
  arm (`Exit.restoreAfterFinalizer`, `Exit.mergeFinalizer`): names are data. -/
  restoreName : Exit β ε δ ι α → ν
  mergeName : Exit β ε δ ι α → ν
  /-- The scope store: `none` unknown; `some none` open; `some (some exit)` closed. -/
  scopeStatus : Nat → St → Option (Option (Exit β ε δ ι α))
  /-- Register the keyed fiber finalizer of `forkIn` (self-guarded, `:5370`) or
  `fiberRunIn` (unguarded, `:5458`); `none` when the scope is unknown (M4, M7). -/
  scopeLinkFiber : Supervision.ScopeMode → Nat → Nat → FiberId → St → Option St
  /-- `forkIn`'s key-dropping observer (`:5370-5372`); `none` when the scope is unknown. -/
  dropFinalizer : Nat → Nat → St → Option St
  /-- The close program of a scope for its strategy: sequential awaits each finalizer
  through its exit; parallel forks daemons that inherit the closing fiber's mask and merges
  every exit by `exitAsVoidAll`. Arguments: scope, exit, the closer's `interruptible`, the
  closer's id; `none` when the scope is unknown (M7). -/
  closeScope : Nat → Exit β ε δ ι α → Bool → FiberId → St → Option (St × Prim ν σ β ε δ ι α)
  /-- The ambient `Scope` service of a context (`forkScoped`, `:5400-5406`). -/
  ambientScope : χ → Option Nat
  /-- `MaxOpsBeforeYield` and `PreventSchedulerYield` read off a context (`:726-727`). -/
  budgetOf : χ → Nat × Bool
  /-- `Context.empty()` (`:627`). -/
  emptyContext : χ
  /-- A context as a value (`getContext`). -/
  contextValue : χ → β
  /-- What a resumed awaiter continues with: the exit as a value (`await`, `:5304`) or as
  an effect (`join`, `:5291`). -/
  exitValue : Exit β ε δ ι α → Supervision.ObserverMode → Prim ν σ β ε δ ι α
  /-- The fiber handle a fork answers with. -/
  fiberValue : FiberId → β
  /-- A list of handles as a value (`awaitAllChildren`'s snapshot). -/
  fibersValue : List FiberId → β
  /-- A list of exits as a value (`fiberAwaitAll`, `:779`; M6). -/
  exitsValue : List (Exit β ε δ ι α) → β
  /-- `exitVoid` as a value (`:988`). -/
  voidValue : β
  /-- The interruptor's encoding into the cause's `ι` (`Supervision.interruptCause`). -/
  encodeFiber : FiberId → ι
  /-- What `currentStackFrame` contributes to an interrupt cause (`:579-580`). -/
  stackAnnotations : FiberId → ReasonAnnotations α
  /-- `AsyncFiberError`, the defect of a fiber that survives `runSync`'s flush. -/
  asyncFiberError : δ
  /-- The defect of `forkScoped` with no ambient `Scope` service: rc.112's `Context.get`
  throws `ServiceNotFound` (`:5400-5406`). Named apart from `notImplemented`, which is the
  "unimplemented step" of `defaultEvaluate` (finding S1-1, 2026-09-04). -/
  missingScope : δ

/-! ## Machine operations -/

namespace RunMachine

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

def fiber? (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) :
    Option (RunFiber ν σ β ε δ ι α χ) :=
  m.fibers.find? fun f => f.id = id

def update (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) :
    RunMachine ν σ β ε δ ι α χ St :=
  { m with fibers := m.fibers.map fun g => if g.id = f.id then f else g }

def emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ)) :
    RunMachine ν σ β ε δ ι α χ St :=
  { m with trace := m.trace ++ events }

def modify (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (k : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) :
    RunMachine ν σ β ε δ ι α χ St :=
  match m.fiber? id with
  | none => m
  | some f => m.update (k f)

def halt (m : RunMachine ν σ β ε δ ι α χ St) (why : Stuck) : RunMachine ν σ β ε δ ι α χ St :=
  { m with stuck := some why }

def race? (m : RunMachine ν σ β ε δ ι α χ St) (id : Nat) : Option (Race β ε δ ι α) :=
  m.races.find? fun r => r.id = id

def updateRace (m : RunMachine ν σ β ε δ ι α χ St) (r : Race β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St :=
  { m with races := m.races.map fun s => if s.id = r.id then r else s }

/-- Every fiber has exited. -/
def finished (m : RunMachine ν σ β ε δ ι α χ St) : Bool :=
  m.fibers.all fun f => f.exit.isSome

/-- A fresh machine over a store. -/
def empty (state : St) : RunMachine ν σ β ε δ ι α χ St where
  fibers := []
  races := []
  nextId := 0
  nextToken := 0
  nextRace := 0
  middlewareInstalled := false
  state := state
  trace := []
  stuck := none

end RunMachine

/-! ## The commands the loop runs

Everything that rc.112 runs synchronously on the current stack, nested inside another
fiber's evaluate, is a command: an immediate fork's start (`:5270-5271`), a `resume`
(`:1121`), a Deferred completion's waiters (`Deferred.ts:1655-1659`), a race launch. The loop
runs commands with fuel, and re-reads a fiber from the machine after every nested command,
so a fiber that was interrupted or resumed while another ran is never a stale local. -/
inductive Cmd (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  /-- `evaluate` (`:599-628`) on a fiber that is not running. -/
  | evaluate (fiber : FiberId)
  /-- Continue a running fiber's `runLoop` with the injection latch. -/
  | loop (fiber : FiberId) (yielding : Bool)
  /-- `resume(effect)` (`:1121`): unpark on the token and evaluate. -/
  | resume (fiber : FiberId) (token : Nat) (answer : Prim ν σ β ε δ ι α)
  /-- One race entrant's immediate launch; once the race is settled the entrant is
  interrupted instead (M8). -/
  | launch (race : Nat) (entrant : FiberId)
  /-- Drain the resumes the store owes. -/
  | drainDue

section Machine

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- `interruptUnsafe(fiberId, annotations)` (`:574-595`) on one fiber, without the
apply-now re-entry, which the loop performs as a command. The cause is annotated from the
target's stack frame and from the caller (`:578-584`, M5). Returns the fiber and whether to
evaluate it now. When the fiber was parked on an `Async` that pushed an `AsyncFinalizer`,
applying the interrupt means failing through that frame, whose `contE` runs the cancel
(`:1155-1159`) — the frame machine does that; nothing here has to. -/
def interruptRecord (interp : RunInterp ν σ β ε δ ι α χ St) (interruptor : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    RunFiber ν σ β ε δ ι α χ × Bool :=
  if f.exit.isSome then (f, false)                                     -- :575-577
  else
    let cause : Cause ε δ ι α :=
      Cause.annotate
        (Supervision.interruptCause interp.encodeFiber interruptor (interp.stackAnnotations f.id))
        extra false
    let accumulated : Cause ε δ ι α :=
      match f.frame.interruptedCause with                              -- :585-587
      | none => cause
      | some previous => Cause.combine previous cause
    let f := { f with frame := { f.frame with interruptedCause := some accumulated } }
    if f.frame.interruptible then                                      -- :588
      if f.running then ({ f with frame := { f.frame with deferredInterrupt := true } }, false)
      else                                                             -- :591-594
        ({ f with
            parked := Parked.notParked
            pending := []
            frame := { f.frame with current := Prim.failure accumulated } }, true)
    else (f, false)

/-- Register the observers of a countdown park over `targets` and park `f` on it; a target
that has already exited counts at once, its exit collected (`:561-562`, M6). Returns whether
the fiber actually parked; when nothing was live the continuation is applied at once. -/
def countdownPark (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId) (resumeWith : Resume ν)
    (failFast : Bool := false) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × Bool :=
  let token := m.nextToken
  let m := { m with nextToken := m.nextToken + 1 }
  let exited := targets.filterMap fun t => (m.fiber? t).bind RunFiber.exit
  let live := targets.filter fun t =>
    match m.fiber? t with
    | some g => g.exit.isNone
    | none => false
  if live.isEmpty then
    (m, { f with frame := { f.frame with current := resumePrim interp resumeWith exited } }, false)
  else
    let m := live.foldl (fun m t =>
        m.modify t fun g => { g with observers := g.observers ++ [Observer.countdown f.id token] }) m
    let f := f.park ⟨token, none, live.length, exited, resumeWith, failFast, live⟩
    (m.emit [RunEvent.parkedOn f.id token], f, true)
where
  /-- What a finished countdown continues with. -/
  resumePrim (interp : RunInterp ν σ β ε δ ι α χ St) (resumeWith : Resume ν)
      (exits : List (Exit β ε δ ι α)) : Prim ν σ β ε δ ι α :=
    match resumeWith with
    | Resume.exitsValue => Prim.success (interp.exitsValue exits)
    | Resume.void => Prim.success interp.voidValue
    | Resume.continueWith name => Prim.onSuccess (Prim.success (interp.exitsValue exits)) name

/-- Where one `runLoop` iteration left the fiber. -/
inductive Outcome (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) : Type (max u v)
  | continue_
  | parked
  | finished (exit : Exit β ε δ ι α)
  | stuck (why : Stuck)
deriving DecidableEq

/-- The result of one iteration: the machine, the fiber, the latch, where it left off, and
the commands to run synchronously before continuing. -/
structure Iter (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) :
    Type (max u v) where
  machine : RunMachine ν σ β ε δ ι α χ St
  fiber : RunFiber ν σ β ε δ ι α χ
  yielding : Bool
  outcome : Outcome ν σ β ε δ ι α
  nested : List (Cmd ν σ β ε δ ι α)

/-- Create a child over the parent (`:5264-5284`): mask by the options (`:5272`), the
parent's context (`:5273`), tracked unless daemon (`:5280-5281`). -/
def spawn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × FiberId :=
  let childId : FiberId := ⟨m.nextId⟩
  let childInterruptible :=
    match options.maskMode with
    | Supervision.MaskMode.interruptible => true
    | Supervision.MaskMode.uninterruptible => false
    | Supervision.MaskMode.inherit => parent.frame.interruptible
  let child := RunFiber.make childId program childInterruptible
    (interp.budgetOf parent.context) parent.context
  let child :=
    if options.daemon then child
    else { child with observers := [Observer.untrackChild parent.id] }
  let parent := { parent with
    children := (if options.daemon then parent.children else parent.children ++ [childId]) }
  let m := { m with fibers := m.fibers ++ [child], nextId := m.nextId + 1 }
  (m.emit [RunEvent.forked parent.id childId options.daemon], parent, childId)

/-- Start a spawned child: now, on the caller's stack (`:5270-5271`), or deferred onto the
parent's dispatcher at priority 0 (`:5277`). -/
def start (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) (immediately : Bool) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × List (Cmd ν σ β ε δ ι α) :=
  if immediately then (m, parent, [Cmd.evaluate child])
  else
    let parent := { parent with dispatcher := parent.dispatcher.enqueue 0 (Task.start child) }
    (m.emit [RunEvent.scheduledTask parent.id 0 (Task.start child)], parent, [])

/-- Link a fiber to a scope (`forkIn`, `:5364-5378`; `fiberRunIn`, `:5447-5461`): open, a
keyed finalizer of the mode's shape and the key-dropping observer; closed, an immediate
interrupt with `interruptor` and the interruptor's own stack annotations (`:5374`, M5);
unknown, stuck (M7). -/
def linkScope (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (mode : Supervision.ScopeMode) (scope key : Nat) (target : FiberId)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) :
    RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α) :=
  match interp.scopeStatus scope m.state with
  | none => (m.halt (Stuck.unknownScope scope), [])
  | some (some _) =>                                                   -- closed: :5374, :5454
    match m.fiber? target with
    | none => (m.halt (Stuck.unknownFiber target), [])
    | some t =>
      -- M10: `forkIn` passes the parent's stack annotations (:5374); `fiberRunIn` passes
      -- none (:5454). The caller decides, by mode.
      let (t, applyNow) := interruptRecord interp interruptor extra t
      let m := (m.update t).emit [RunEvent.scopeClosedOnLink scope target,
        RunEvent.interruptRecorded interruptor target]
      (m, if applyNow then [Cmd.evaluate target] else [])
  | some none =>                                                       -- open: :5369-5372
    match m.fiber? target with
    | none => (m.halt (Stuck.unknownFiber target), [])
    -- an exited fiber is not linked (`:5367`, `:5451-5452`, R2-9)
    | some t =>
      if t.exit.isSome then (m, [])
      else
        match interp.scopeLinkFiber mode scope key target m.state with
        | none => (m.halt (Stuck.unknownScope scope), [])
        | some state =>
          let m := { m with state := state }
          let m := m.modify target fun t =>
            { t with observers := t.observers ++ [Observer.dropScopeFinalizer scope key] }
          (m.emit [RunEvent.scopeLinked mode scope key target], [])

/-- The top of a `runLoop` iteration (`:639-642`): a deferred interrupt is cleared and the
current primitive is replaced by the pending cause's failure. -/
def runloopTop (f : RunFiber ν σ β ε δ ι α χ) : RunFiber ν σ β ε δ ι α χ :=
  if f.frame.deferredInterrupt then
    { f with frame :=
        { f.frame with deferredInterrupt := false, current := Prim.failure f.frame.pendingCause } }
  else f

/-- The op counter (`:643`). -/
def countOp (f : RunFiber ν σ β ε δ ι α χ) : RunFiber ν σ β ε δ ι α χ :=
  { f with currentOpCount := f.currentOpCount + 1 }

/-- `shouldYield` (`Scheduler.ts:174-176`): the op count has reached the budget — under the
tape's override (`Scheduler.ts:78-81`), which answers instead when present. -/
def yieldVerdict (f : RunFiber ν σ β ε δ ι α χ) : Bool :=
  f.yieldOverride.getD (decide (f.currentOpCount >= f.maxOpsBeforeYield))

/-- Yield injection (`:644-652`): at most once per entry (the `yielding` latch), never under
`PreventSchedulerYield`, and only on the verdict. The fiber parks behind a resume guard
whose task carries its current primitive at priority 0. -/
def injectYield (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) : Option (Iter ν σ β ε δ ι α χ St) :=
  if !yielding && !f.preventYield && yieldVerdict f then
    let token := m.nextToken
    let m := { m with nextToken := m.nextToken + 1 }
    let f := { f with
      yieldOverride := none
      dispatcher := (f.dispatcher.enqueue 0 (Task.resume f.id token f.frame.current)) }
    let f := f.park ⟨token, none, 0, [], Resume.void, false, []⟩
    some ⟨m.emit [RunEvent.yieldInjected f.id f.currentOpCount, RunEvent.parkedOn f.id token],
      f, true, Outcome.parked, []⟩
  else none

/-- Evaluate the current primitive (`current[evaluate](this)`, `:655`), with the fiber-level
arms rc.112 keeps out of the frame machine: the two parks the alphabet spells (`Yield`,
`Async`), the join park the interp classifies, `withFiber` actions, stateful `sync` thunks,
and exits meeting an `OnExit` frame whose finalizer is a program. Everything else is the
frame machine's step. -/
def evaluatePrim (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) : Iter ν σ β ε δ ι α χ St :=
    match f.frame.current with
    | Prim.yieldNowWith priority =>                                     -- :982-990
      let token := m.nextToken
      let m := { m with nextToken := m.nextToken + 1 }
      let f := { f with
        frame := { f.frame with current := Prim.success interp.voidValue }
        dispatcher :=
          (f.dispatcher.enqueue priority (Task.resume f.id token (Prim.success interp.voidValue))) }
      let f := f.park ⟨token, none, 0, [], Resume.void, false, []⟩
      ⟨m.emit [RunEvent.parkedOn f.id token], f, yielding, Outcome.parked, []⟩
    | Prim.async register withSignal cancel =>                          -- :1109-1143
      let token := m.nextToken
      let (state, immediate) := interp.registerAsync register f.id token m.state
      let m := { m with state := state, nextToken := m.nextToken + 1 }
      match immediate with
      | some next =>                                                   -- :1120-1126
        ⟨m, { f with frame := { f.frame with current := next } }, yielding,
          Outcome.continue_, [Cmd.drainDue]⟩
      | none =>                                                        -- :1128-1141
        -- the finalizer frame is pushed exactly when there is a controller or a cancel
        let f :=
          if withSignal || cancel.isSome then
            let name := interp.cancelName (cancel.getD interp.abortName) f.id token
            { f with frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack } }
          else f
        let f := f.park ⟨token, none, 0, [], Resume.void, false, []⟩
        ⟨m.emit [RunEvent.parkedOn f.id token], f, yielding, Outcome.parked, []⟩
    | _ =>
      match interp.parkOf f.frame.current with
      | some (Except.error cause) =>                                   -- a refused park
        ⟨m, { f with frame := { f.frame with current := Prim.failure cause } }, yielding,
          Outcome.continue_, []⟩
      | some (Except.ok (ParkKind.join target mode)) =>                -- :5291, :5304
        match m.fiber? target with
        | none => ⟨m, f, yielding, Outcome.stuck (Stuck.unknownFiber target), []⟩   -- S3 §5.1
        | some t =>
          match t.exit with
          | some exit =>                                               -- :561-562
            ⟨m, { f with frame := { f.frame with current := interp.exitValue exit mode } },
              yielding, Outcome.continue_, []⟩
          | none =>
            let token := m.nextToken
            let m := { m with nextToken := m.nextToken + 1 }
            let m := m.update
              { t with observers := t.observers ++ [Observer.resumeAwait f.id token mode] }
            let f := f.park ⟨token, some target, 0, [], Resume.void, false, []⟩
            ⟨m.emit [RunEvent.parkedOn f.id token], f, yielding, Outcome.parked, []⟩
      | none =>
        match f.frame.current with
        | Prim.withFiber thunk =>
          match interp.withFiberOf thunk with
          | some action => withFiber interp m f yielding action
          | none => stepFrame interp m f yielding
        | Prim.sync thunk =>
          match interp.syncState thunk m.state with
          | some (state, value) =>                                     -- M1: drain on the spot
            let (next, events) := f.frame.resumeValue interp.toPrimInterp value none
            finishFrame { m with state := state } f yielding next events [Cmd.drainDue]
          | none => stepFrame interp m f yielding
        | Prim.success value =>
          finalizerOr interp m f yielding (Exit.success value)
        | Prim.failure cause =>
          finalizerOr interp m f yielding (Exit.failure cause)
        | _ => stepFrame interp m f yielding
where
  /-- An exit meeting an `OnExit` frame whose finalizer is a program (`:4021`): the frame is
  popped, its `contAll` masks (`ensure`), and the finalizer runs followed by the restoring
  continuation. Otherwise the frame machine's pure shortcut applies. -/
  finalizerOr (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
      (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (exit : Exit β ε δ ι α) :
      Iter ν σ β ε δ ι α χ St :=
    -- S5 §7.1: the exit is delivered to the frame `getCont` answers with, not to the stack
    -- head — frames that do not declare the demanded arm (a restoring `setInterruptible`
    -- an inner `OnExit` pushed) are passed first. Same demand and skip as `resumeValue`
    -- (`Runtime.lean:2300`) and `resumeCause` (`:2334`).
    let demand := match exit with
      | Exit.success _ => Arm.contA
      | Exit.failure _ => Arm.contE
    let skip := match exit with
      | Exit.success _ => false
      | Exit.failure _ => true
    let pop := f.frame.getCont demand skip
    match pop.answer with
    | ContAnswer.frame (Prim.onExit _ fin _) =>
      match interp.finalizerProgram fin exit with
      | some program =>
        -- `pop.fiber` already carries the answering frame's `ensure` (the mask and its
        -- restoring frame) and the stack below it (`Runtime.lean:1463-1465`).
        let fiber := { pop.fiber with
          current := Prim.onSuccessAndFailure program (interp.restoreName exit) (interp.mergeName exit) }
        ⟨m.emit (pop.events.map (RunEvent.frame f.id) ++ [RunEvent.finalizerProgram f.id fin exit]),
          { f with frame := fiber }, yielding, Outcome.continue_, []⟩
      | none => stepFrame interp m f yielding
    | _ => stepFrame interp m f yielding
  /-- Delegate to the frame machine (`current[evaluate](this)`, `:655`). -/
  stepFrame (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
      (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) : Iter ν σ β ε δ ι α χ St :=
    let (next, events) := f.frame.step interp.toPrimInterp
    finishFrame m f yielding next events []
  finishFrame (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
      (yielding : Bool) (next : FrameStep ν σ β ε δ ι α)
      (events : List (FrameEvent ν σ β ε δ ι α)) (nested : List (Cmd ν σ β ε δ ι α)) :
      Iter ν σ β ε δ ι α χ St :=
    let m := m.emit (events.map (RunEvent.frame f.id))
    match next with
    | FrameStep.running frame => ⟨m, { f with frame := frame }, yielding, Outcome.continue_, nested⟩
    | FrameStep.finished exit => ⟨m, f, yielding, Outcome.finished exit, nested⟩
  /-- Every `withFiber` action. -/
  withFiber (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
      (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
      (action : WithFiberAction ν σ β ε δ ι α χ) : Iter ν σ β ε δ ι α χ St :=
    let answer (f : RunFiber ν σ β ε δ ι α χ) (value : β) : RunFiber ν σ β ε δ ι α χ :=
      { f with frame := { f.frame with current := Prim.success value } }
    let outcomeOf (m : RunMachine ν σ β ε δ ι α χ St) (parked : Bool) : Outcome ν σ β ε δ ι α :=
      match m.stuck with
      | some why => Outcome.stuck why
      | none => if parked then Outcome.parked else Outcome.continue_
    match action with
    | WithFiberAction.fork program options =>
      -- `forkChild` installs the interrupt-children middleware for the process
      -- (`interruptChildrenPatch()`, `:5253`, `:6656-6658`); `forkDetach` does not (R2-6)
      let m := if options.daemon then m else { m with middlewareInstalled := true }
      let (m, f, child) := spawn interp m f program options
      let (m, f, nested) := start m f child options.startImmediately
      ⟨m, answer f (interp.fiberValue child), yielding, Outcome.continue_, nested⟩
    | WithFiberAction.forkIn program options scope key =>
      let (m, f, child) := spawn interp m f program { options with daemon := true }
      let (m, nested) := linkScope interp m Supervision.ScopeMode.forkIn scope key child
        (some f.id) (interp.stackAnnotations f.id)
      let (m, f, started) := start m f child options.startImmediately
      ⟨m, answer f (interp.fiberValue child), yielding, outcomeOf m false, nested ++ started⟩
    | WithFiberAction.forkScoped program options key =>
      match interp.ambientScope f.context with
      | some scope =>
        let (m, f, child) := spawn interp m f program { options with daemon := true }
        let (m, nested) := linkScope interp m Supervision.ScopeMode.forkIn scope key child
          (some f.id) (interp.stackAnnotations f.id)
        let (m, f, started) := start m f child options.startImmediately
        ⟨m, answer f (interp.fiberValue child), yielding, outcomeOf m false, nested ++ started⟩
      | none =>
        ⟨m, { f with frame := { f.frame with
            current := Prim.failure (Cause.die interp.missingScope) } },
          yielding, Outcome.continue_, []⟩
    | WithFiberAction.runIn target scope key =>
      let (m, nested) := linkScope interp m Supervision.ScopeMode.fiberRunIn scope key target
        (some target) ReasonAnnotations.empty
      ⟨m, answer f interp.voidValue, yielding, outcomeOf m false, nested⟩
    | WithFiberAction.interrupt target =>
      interruptThenJoin interp m f yielding target (some f.id)
    | WithFiberAction.interruptScoped target =>
      if target = f.id then ⟨m, answer f interp.voidValue, yielding, Outcome.continue_, []⟩
      else interruptThenJoin interp m f yielding target (some f.id)
    | WithFiberAction.interruptAll targets interruptor =>
      let who := interruptor.getD f.id
      let (m, nested) := targets.foldl (fun (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) t =>
          match acc.1.fiber? t with
          | none => acc
          | some g =>
            -- the caller's stack annotations, whoever the interruptor is (`:892-895`, `:910-913`)
            let (g, applyNow) := interruptRecord interp (some who) (interp.stackAnnotations f.id) g
            let m := (acc.1.update g).emit [RunEvent.interruptRecorded (some who) t]
            (m, acc.2 ++ (if applyNow then [Cmd.evaluate t] else []))) (m, [])
      let (m, f, parked) := countdownPark interp m f targets Resume.void
      ⟨m, f, yielding, outcomeOf m parked, nested⟩
    | WithFiberAction.awaitAll targets =>
      let (m, f, parked) := countdownPark interp m f targets Resume.exitsValue
      ⟨m, f, yielding, outcomeOf m parked, []⟩
    | WithFiberAction.awaitAllFailFast targets =>                       -- Layer.ts:1597-1598
      let (m, f, parked) := countdownPark interp m f targets Resume.exitsValue true
      ⟨m, f, yielding, outcomeOf m parked, []⟩
    | WithFiberAction.snapshotChildren =>
      ⟨m, answer f (interp.fibersValue f.children), yielding, Outcome.continue_, []⟩
    | WithFiberAction.awaitNewChildren snapshot =>
      let fresh := f.children.filter fun c => !(snapshot.contains c)
      let (m, f, parked) := countdownPark interp m f fresh Resume.void
      ⟨m, f, yielding, outcomeOf m parked, []⟩
    | WithFiberAction.raceAll entrants =>
      let raceId := m.nextRace
      let token := m.nextToken
      let m := { m with nextRace := m.nextRace + 1, nextToken := m.nextToken + 1 }
      -- entrants exist as fibers before any launch; a launch is a command
      let (m, f, ids) := entrants.foldl
        (fun (acc : RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × List FiberId) program =>
          -- `forkUnsafe(parent, effect, true, true, false)`: immediate, daemon, and
          -- *interruptible* — `uninterruptible = false` (`:1521`, R2-10)
          let (m, f, child) := spawn interp acc.1 acc.2.1 program
            ⟨true, true, Supervision.MaskMode.interruptible⟩
          let m := m.modify child fun c =>
            { c with observers := c.observers ++ [Observer.raceCallback raceId] }
          (m, f, acc.2.2 ++ [child])) (m, f, [])
      let race : Race β ε δ ι α :=
        ⟨raceId, f.id, token, Supervision.RaceAllState.initial ids, false⟩
      let m := { m with races := m.races ++ [race] }
      let m := m.emit [RunEvent.raceStarted raceId f.id ids]
      -- the empty race stays pending until interrupted; a non-empty one launches in order
      let f := f.park ⟨token, none, 0, [], Resume.void, false, []⟩
      ⟨m.emit [RunEvent.parkedOn f.id token], f, yielding, Outcome.parked,
        ids.map (Cmd.launch raceId)⟩
    | WithFiberAction.setInterruptible body false =>                    -- :4302-4310 (M2)
      ⟨m, { f with frame := { f.frame.uninterruptible with current := body } },
        yielding, Outcome.continue_, []⟩
    | WithFiberAction.setInterruptible body true =>                     -- :4331-4352 (M2)
      let (frame, immediate) := f.frame.interruptibleRegion
      ⟨m, { f with frame := { frame with current := immediate.getD body } },
        yielding, Outcome.continue_, []⟩
    | WithFiberAction.setContext context =>
      let (maxOps, prevent) := interp.budgetOf context
      let f := { f with context := context, maxOpsBeforeYield := maxOps, preventYield := prevent }
      ⟨m.emit [RunEvent.contextSet f.id context], answer f interp.voidValue, yielding,
        Outcome.continue_, []⟩
    | WithFiberAction.getContext =>
      ⟨m, answer f (interp.contextValue f.context), yielding, Outcome.continue_, []⟩
    | WithFiberAction.getId =>
      ⟨m, answer f (interp.fiberValue f.id), yielding, Outcome.continue_, []⟩
    | WithFiberAction.closeScope scope exit =>
      match interp.closeScope scope exit f.frame.interruptible f.id m.state with
      | none => ⟨m, f, yielding, Outcome.stuck (Stuck.unknownScope scope), []⟩   -- M7
      | some (state, program) =>
        ⟨{ m with state := state }, { f with frame := { f.frame with current := program } },
          yielding, Outcome.continue_, []⟩
    | WithFiberAction.refuse cause =>                                   -- S3 §5.2
      ⟨m, { f with frame := { f.frame with current := Prim.failure cause } }, yielding,
        Outcome.continue_, []⟩
  /-- `fiberInterrupt` (`:859`): record with `interruptor`, then await the target. -/
  interruptThenJoin (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
      (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (target : FiberId)
      (interruptor : Option FiberId) : Iter ν σ β ε δ ι α χ St :=
    match m.fiber? target with
    | none => ⟨m, f, yielding, Outcome.stuck (Stuck.unknownFiber target), []⟩
    | some t =>
      -- `fiberInterruptAs` passes the caller's stack annotations (`:880-883`, R2-5)
      let (t, applyNow) := interruptRecord interp interruptor (interp.stackAnnotations f.id) t
      let m := (m.update t).emit [RunEvent.interruptRecorded interruptor target]
      let nested := if applyNow then [Cmd.evaluate target] else []
      let (m, f, parked) := countdownPark interp m f [target] Resume.void
      ⟨m, f, yielding, (if parked then Outcome.parked else Outcome.continue_), nested⟩

/-- One `runLoop` iteration (`:638-668`) on fiber `f` in machine `m`; `yielding` is the
per-entry injection latch (`:634`, `:648`): the top of the loop, the op counter, then either
a yield injection or the evaluation of the current primitive. -/
def iteration (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) : Iter ν σ β ε δ ι α χ St :=
  let f := countOp (runloopTop f)
  match injectYield m f yielding with
  | some it => it
  | none => evaluatePrim interp m f yielding

/-- Fire one observer (`:621-623`) of fiber `id`, which has exited with `exit`. Resumes
are synchronous (`:1121`), so they come back as commands. -/
def fireObserver (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) (observer : Observer) :
    RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α) :=
  let m := acc.1.emit [RunEvent.observerFired id observer]
  match observer with
  | Observer.resumeAwait waiter token mode =>                          -- :561-562, :5291, :5304
    (m, acc.2 ++ [Cmd.resume waiter token (interp.exitValue exit mode)])
  | Observer.untrackChild parent =>                                    -- :5281
    (m.modify parent fun p => { p with children := p.children.filter fun c => c ≠ id }, acc.2)
  | Observer.dropScopeFinalizer scope key =>                           -- :5370-5372
    match interp.dropFinalizer scope key m.state with
    | none => (m.halt (Stuck.unknownScope scope), acc.2)
    | some state => ({ m with state := state }, acc.2)
  | Observer.countdown waiter token =>                                 -- M6: collect the exit
    match m.fiber? waiter with
    | none => (m, acc.2)
    | some w =>
      match w.pending.find? fun p => p.token = token with
      | none => (m, acc.2)
      | some p =>
        let collected := p.collected ++ [exit]
        let outstanding := p.outstanding.filter fun t => t ≠ id
        -- fail-fast (`Effect.all` with concurrency): the first failing exit interrupts every
        -- outstanding target with the awaiter's id; the countdown still waits for them
        let firstFailure := p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess
        let (m, nested) :=
          if firstFailure then
            outstanding.foldl (fun (a : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) t =>
                match a.1.fiber? t with
                | none => a
                | some g =>
                  let (g, applyNow) :=
                    interruptRecord interp (some waiter) (interp.stackAnnotations waiter) g
                  let m := (a.1.update g).emit [RunEvent.interruptRecorded (some waiter) t]
                  (m, a.2 ++ (if applyNow then [Cmd.evaluate t] else []))) (m, [])
          else (m, [])
        if p.remaining <= 1 then
          let w := { w with pending := w.pending.map fun q =>
            if q.token = token then { q with remaining := 0, collected := collected, outstanding := [] } else q }
          (m.update w,
            acc.2 ++ nested ++
              [Cmd.resume waiter token (countdownPark.resumePrim interp p.resumeWith collected)])
        else
          let w := { w with pending := w.pending.map fun q =>
            if q.token = token then
              { q with remaining := q.remaining - 1, collected := collected, outstanding := outstanding }
            else q }
          (m.update w, acc.2 ++ nested)
  | Observer.raceCallback raceId =>
    match m.race? raceId with
    | none => (m, acc.2)
    | some race =>
      let state := Supervision.raceComplete race.state id exit                 -- frozen bookkeeping
      let race := { race with state := state }
      let m := m.updateRace race
      match state.accepted, race.settled with
      | some accepted, false =>
        -- settle: interrupt the live entrants with the host's id, then resume the host
        let m := m.updateRace { race with settled := true }
        let m := m.emit [RunEvent.raceSettled raceId accepted]
        let (m, nested) := state.live.foldl
          (fun (a : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) entrant =>
            match a.1.fiber? entrant with
            | none => a
            | some e =>
              let (e, applyNow) :=
                interruptRecord interp (some race.host) (interp.stackAnnotations race.host) e
              let m := (a.1.update e).emit [RunEvent.interruptRecorded (some race.host) entrant]
              (m, a.2 ++ (if applyNow then [Cmd.evaluate entrant] else []))) (m, [])
        -- the host is resumed after the losers have been awaited: a countdown over them
        match m.fiber? race.host with
        | none => (m, acc.2 ++ nested)
        | some host =>
          let host := { host with
            parked := Parked.notParked
            pending := host.pending.filter fun p => p.token ≠ race.token }
          let (m, host, parked) := countdownPark interp m host state.live
            (Resume.continueWith (interp.restoreName accepted))
          if parked then (m.update host, acc.2 ++ nested)
          else (m.update host, acc.2 ++ nested ++ [Cmd.evaluate race.host])
      | _, _ => (m, acc.2)
  | Observer.callback key => (m.emit [RunEvent.callback key exit], acc.2)

/-- The exit path (`:611-627`): with the middleware installed and tracked children, the
children are interrupted with the parent's id and awaited before the exit is stored
(`:613-617`, `awaitAllChildren`); then the exit is stored, every observer fires in index
order, and the fiber is cleared, its context emptied (`:619-627`). -/
def exitFiber (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × Bool × List (Cmd ν σ β ε δ ι α) :=
  if m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty then
    let (m, nested) := f.children.foldl
      (fun (a : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) child =>
        match a.1.fiber? child with
        | none => a
        | some c =>
          -- `fiberInterruptAll(children)` under `withFiber(parent)`: the parent's stack
          -- annotations (`:892-895`, R2-5)
          let (c, applyNow) := interruptRecord interp (some f.id) (interp.stackAnnotations f.id) c
          let m := (a.1.update c).emit [RunEvent.interruptRecorded (some f.id) child]
          (m, a.2 ++ (if applyNow then [Cmd.evaluate child] else []))) (m, [])
    let m := m.emit [RunEvent.childrenInterrupted f.id f.children]
    -- the loop returned an exit: `_deferredInterrupt = false` (`:659`, R2-2)
    let f := { f with finalizing := some exit, frame := { f.frame with deferredInterrupt := false } }
    let (m, f, parked) :=
      countdownPark interp m f f.children (Resume.continueWith (interp.restoreName exit))
    (m, f, parked, nested)
  else
    let f := { f with                                                  -- :619-627
      exit := some exit
      finalizing := none
      frame := { f.frame with stack := [], deferredInterrupt := false }
      children := []
      parked := Parked.notParked
      pending := []
      context := interp.emptyContext }
    let m := (m.update f).emit [RunEvent.exited f.id exit]
    let (m, nested) := f.observers.foldl (fireObserver interp f.id exit) (m, [])
    let f := { f with observers := [] }
    (m.update f, f, false, nested)

/-- The command loop. Each command costs one fuel; exhaustion is a live frontier, and so is
a stuck machine, which stops the loop with its reason recorded. -/
def drive (interp : RunInterp ν σ β ε δ ι α χ St) :
    Nat → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) →
      RunMachine ν σ β ε δ ι α χ St
  | 0, m, _ => m
  | _ + 1, m, [] => m
  | fuel + 1, m, cmd :: rest =>
    if m.stuck.isSome then m else
    match cmd with
    | Cmd.evaluate id =>                                               -- :599-628
      match m.fiber? id with
      | none => drive interp fuel m rest
      | some f =>
        if f.exit.isSome || f.running then drive interp fuel m rest      -- :600-601
        else
          let f := { f with running := true, currentOpCount := 0, parked := Parked.notParked }
          let m := (m.update f).emit [RunEvent.started id]
          drive interp fuel m (Cmd.loop id false :: rest)
    | Cmd.loop id yielding =>
      match m.fiber? id with
      | none => drive interp fuel m rest
      | some f =>
        let it := iteration interp m f yielding
        match it.outcome with
        | Outcome.continue_ =>
          let m := it.machine.update it.fiber
          drive interp fuel m (it.nested ++ [Cmd.loop id it.yielding] ++ rest)
        | Outcome.parked =>                                            -- :667, :608-610
          let m := it.machine.update { it.fiber with running := false }
          drive interp fuel m (it.nested ++ rest)
        | Outcome.finished exit =>
          -- M1: what the last primitive owes synchronously (a completion's waiters) runs
          -- before this fiber's exit path, as it does on rc.112's stack; the fiber is then
          -- re-read, since a nested command may have recorded an interrupt on it.
          let m := drive interp fuel (it.machine.update it.fiber) it.nested
          if m.stuck.isSome then m else
          match m.fiber? id with
          | none => drive interp fuel m rest
          | some f =>
            let (m, f, parked, nested) := exitFiber interp m { f with running := false } exit
            let m := m.update f
            drive interp fuel m (nested ++ (if parked then [] else [Cmd.drainDue]) ++ rest)
        | Outcome.stuck why =>
          (it.machine.update { it.fiber with running := false }).halt why
    | Cmd.resume id token answer =>                                    -- :602-606, :1121
      match m.fiber? id with
      | none => drive interp fuel m rest
      | some t =>
        match t.parked with
        | Parked.withGuard parkedToken =>
          if parkedToken = token then
            let t := { t with
              parked := Parked.notParked
              pending := t.pending.filter fun p => p.token ≠ token
              frame := { t.frame with current := answer } }
            let m := (m.update t).emit [RunEvent.resumedWith id token answer]
            drive interp fuel m (Cmd.evaluate id :: rest)
          else drive interp fuel m rest
        | Parked.notParked => drive interp fuel m rest
    | Cmd.launch raceId entrant =>
      match m.race? raceId with
      | some race =>
        if race.state.accepted.isSome then                             -- M8: interrupt, do not delete
          match m.fiber? entrant with
          | none => drive interp fuel m rest
          | some e =>
            let (e, applyNow) :=
              interruptRecord interp (some race.host) (interp.stackAnnotations race.host) e
            let m := (m.update e).emit [RunEvent.raceSkipped raceId entrant,
              RunEvent.interruptRecorded (some race.host) entrant]
            drive interp fuel m ((if applyNow then [Cmd.evaluate entrant] else []) ++ rest)
        else
          let m := m.updateRace { race with state :=
            { race.state with
              unstarted := race.state.unstarted.filter fun e => e ≠ entrant
              live := race.state.live ++ [entrant] } }
          drive interp fuel (m.emit [RunEvent.raceLaunched raceId entrant])
            (Cmd.evaluate entrant :: rest)
      | none => drive interp fuel m rest
    | Cmd.drainDue =>
      let (due, state) := interp.dueResumes m.state
      let m := { m with state := state }
      drive interp fuel m ((due.map fun d => Cmd.resume d.1 d.2.1 d.2.2) ++ rest)

/-- One tape decision. -/
def stepDecision (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : RunDecision ν σ β ε δ ι α →
      RunMachine ν σ β ε δ ι α χ St
  | RunDecision.fire owner => fire interp fuel m owner
  | RunDecision.flush => flushAll interp fuel fuel m
  | RunDecision.evaluate id => drive interp fuel m [Cmd.evaluate id, Cmd.drainDue]
  | RunDecision.yieldVerdict id verdict =>
    m.modify id fun f => { f with yieldOverride := some verdict }
  | RunDecision.answerAsync id token answer =>
    drive interp fuel m [Cmd.resume id token answer, Cmd.drainDue]
  | RunDecision.interruptFrom interruptor annotations target =>
    match m.fiber? target with
    | none => m
    | some t =>
      let (t, applyNow) := interruptRecord interp interruptor annotations t
      let m := m.emit [RunEvent.interruptRecorded interruptor target]
      let m := if t.frame.deferredInterrupt && t.running then
        m.emit [RunEvent.interruptDeferred target] else m
      let m := m.update t
      if applyNow then drive interp fuel m [Cmd.evaluate target, Cmd.drainDue] else m
  | RunDecision.installMiddleware => { m with middlewareInstalled := true }
where
  /-- `runTasks` (`Scheduler.ts:225-233`): drain once, run in order. -/
  fire (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
      (owner : FiberId) : RunMachine ν σ β ε δ ι α χ St :=
    match m.fiber? owner with
    | none => m
    | some o =>
      let (tasks, dispatcher) := o.dispatcher.drain
      let m := m.update { o with dispatcher := dispatcher }
      tasks.foldl (fun m task =>
          let m := m.emit [RunEvent.ranTask owner task]
          match task with
          | Task.start child => drive interp fuel m [Cmd.evaluate child, Cmd.drainDue]
          | Task.resume target token answer =>
            drive interp fuel m [Cmd.resume target token answer, Cmd.drainDue]) m
  /-- The sync scheduler's `flush`: armed dispatchers in fiber order until none is armed.
  Assumption, recorded: the cross-dispatcher order under a synchronous flush is fiber order. -/
  flushAll (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
      Nat → RunMachine ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St
    | 0, m => m
    | rounds + 1, m =>
      let armed := (m.fibers.filter fun f => f.dispatcher.armed).map RunFiber.id
      if armed.isEmpty || m.stuck.isSome then m
      else flushAll interp fuel rounds (armed.foldl (fire interp fuel) m)

/-! ## Replay and the runtime entries -/

inductive ReplayResult (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u) (St : Type (max u v)) :
    Type (max u v)
  | finished (machine : RunMachine ν σ β ε δ ι α χ St)
  | frontier (machine : RunMachine ν σ β ε δ ι α χ St)
  | stuck (why : Stuck) (machine : RunMachine ν σ β ε δ ι α χ St)

/-- Replay a decision tape (DB-03: the meaning is the relation over tapes; this is its
fuel-bounded simulator, DB-04). -/
def replayEval (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    List (RunDecision ν σ β ε δ ι α) → RunMachine ν σ β ε δ ι α χ St →
      ReplayResult ν σ β ε δ ι α χ St
  | [], m =>
    match m.stuck with
    | some why => ReplayResult.stuck why m
    | none => if m.finished then ReplayResult.finished m else ReplayResult.frontier m
  | decision :: tape, m =>
    match m.stuck with
    | some why => ReplayResult.stuck why m
    | none => replayEval interp fuel tape (stepDecision interp fuel m decision)

/-- The relation the plan calls the meaning: one decision, one step. -/
def Step (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (before : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (after : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  after = stepDecision interp fuel before decision

/-- `runForkWith` (`:5410-5430`): one root fiber over the caller context, evaluated
synchronously on the caller stack; the abort signal is the tape's `interruptFrom none`. -/
def runFork (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ) :
    RunMachine ν σ β ε δ ι α χ St × FiberId :=
  let root : FiberId := ⟨m.nextId⟩
  let fiber := RunFiber.make root program true (interp.budgetOf context) context
  let m := { m with fibers := m.fibers ++ [fiber], nextId := m.nextId + 1 }
  (drive interp fuel m [Cmd.evaluate root, Cmd.drainDue], root)

/-- `runCallbackWith` (`:5470-5490`): `runFork` plus an exit observer under `key`; the
returned interruptor is the tape's `interruptFrom (some caller) _ root`. -/
def runCallback (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ)
    (key : Nat) : RunMachine ν σ β ε δ ι α χ St × FiberId :=
  let root : FiberId := ⟨m.nextId⟩
  let fiber := RunFiber.make root program true (interp.budgetOf context) context
  let fiber := { fiber with observers := [Observer.callback key] }
  let m := { m with fibers := m.fibers ++ [fiber], nextId := m.nextId + 1 }
  (drive interp fuel m [Cmd.evaluate root, Cmd.drainDue], root)

/-- `runSyncExitWith` (`:5500-5530`): `runFork` on the sync scheduler, flush, and the
`AsyncFiberError` defect when the root survives the flush. -/
def runSyncExit (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ) :
    RunMachine ν σ β ε δ ι α χ St × Exit β ε δ ι α :=
  let (m, root) := runFork interp fuel m program context
  let m := stepDecision interp fuel m RunDecision.flush
  match (m.fiber? root).bind RunFiber.exit with
  | some exit => (m, exit)
  | none => (m, Exit.failure (Cause.die interp.asyncFiberError))

/-- `runPromiseWith` rejects with `causeSquash` of the failure cause; `runPromiseExitWith`
resolves with the exit. Both are the callback observer plus a projection. -/
def promiseOutcome (exit : Exit β ε δ ι α) : Except (Squashed ε δ) β :=
  match exit with
  | Exit.success value => Except.ok value
  | Exit.failure cause => Except.error cause.squash

end Machine

/-! ## Separation gates (`docs/FRAMES-DAG.md` separation 4): names stay data. -/

example {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    [DecidableEq ν] [DecidableEq σ] [DecidableEq β] [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] [DecidableEq χ] :
    DecidableEq (RunFiber ν σ β ε δ ι α χ) := inferInstance

example {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    [DecidableEq ν] [DecidableEq σ] [DecidableEq β] [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] :
    DecidableEq (RunDecision ν σ β ε δ ι α) := inferInstance

example {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    [DecidableEq ν] [DecidableEq σ] [DecidableEq β] [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] [DecidableEq χ] :
    DecidableEq (WithFiberAction ν σ β ε δ ι α χ) := inferInstance

end Effect4.Deep
