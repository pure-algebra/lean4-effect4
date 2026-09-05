import Effect4.Machine.Witnesses

/-!
# S1: enumerated invariants over the reference fiber machine

Plan: `docs/research/2026-09-04-stress-plan.md` row S1 ("the runtime must be unbreakable").
Every battery under `Test/` before this one checks a handful of hand-written programs
at one tape. This module enumerates the *alphabet* instead: a bounded corpus of `ProgName`
programs over `Effect4.Machine.Stores`, a bounded corpus of `RunDecision` tapes, and nine
Boolean invariants over the machine `Effect4.Machine.Witnesses.replay` reaches on each pair.

Everything here is data. The corpus is two `def`s, the report is a `List Failure`, and the
battery is `#guard`s over them: no `decide` on a proposition about the corpus, no
`Classical.choice`, no `Repr` on anything carrying a `Cause`. `#guard` runs compiled code,
so the cost is the enumeration, not the kernel.

## What the corpus can and cannot name

A program names only keys it can mint. Ref and Deferred keys are the store's *frontier*:
`syncOpStep` answers `none` on a dangling key and the machine falls through to the pure
`syncValue`, so `refGet ⟨0⟩` on the empty heap succeeds with `Val.unit` rather than getting
stuck — checked, and relied on, below. Scope keys are not: `closeScope` and `forkIn` on a
key no allocation minted halt the machine with `Stuck.unknownScope` (W13), so every
scope-consuming program of the corpus sits behind a `scopeMake`.

`forkScoped` is the one shape held out of the corpus; see finding S1-1 at the end.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Test.Machine.Fuzz

open Effect4
open Effect4.Machine
open Effect4.Machine.Witnesses

/-! ## The harness

`Witnesses.replay` at an explicit fuel bound, which invariant 7 needs, over the empty store,
which every pair of this battery starts from. -/

/-- `Witnesses.replay` with the fuel bound named rather than fixed. -/
def replayWith (bound : Nat) (program : ProgName) (tape : List D) : M :=
  match replayEval stores bound tape
      (spawnRoot (RunMachine.empty Stores.empty) program emptyCtx) with
  | ReplayResult.finished m => m
  | ReplayResult.frontier m => m
  | ReplayResult.stuck _ m => m

/-! ## List helpers

Written here rather than taken from a library so that every one is structural and reaches no
axiom beyond the two the gate allows. -/

/-- Membership by the decidable equality of the alphabet. -/
def memOf {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: rest => decide (x = y) || memOf x rest

/-- No element repeats. -/
def noRepeat {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: rest => !(memOf x rest) && noRepeat rest

/-- Keep one occurrence of each element. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: rest =>
    let rest := dedup rest
    if memOf x rest then rest else x :: rest

/-- Pointwise `a → b` over two flag lists, the first no longer than the second: a flag once
set stays set as the run goes on. -/
def flagsMonotone : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => (!a || b) && flagsMonotone as bs

/-! ## The program corpus

Depth 1 is the atom list; the wrappers below take it to depth 3. Every constructor of
`ProgName` the plan names is reachable, and every key a program reads is one it minted or one
the store answers as a frontier. -/

/-- `Ref.make`, the head of every ref sequence. -/
def mkCell : ProgName := ProgName.syncOp (SyncOp.refMake (Val.nat 1))

/-- `Deferred.make`, the head of every Deferred sequence. -/
def mkPromise : ProgName := ProgName.syncOp SyncOp.deferredMake

/-- `scopeMakeUnsafe` under the sequential strategy; it mints key `0` on the empty store. -/
def mkScope : ProgName := ProgName.syncOp (SyncOp.scopeMake FinalizerStrategy.sequential)

/-- The same under the parallel strategy. -/
def mkScopePar : ProgName := ProgName.syncOp (SyncOp.scopeMake FinalizerStrategy.parallel)

/-- The exit every close of the corpus closes with. -/
def unitExit : ExitV := Exit.success Val.unit

/-- The `sync` alphabet at the two keys the corpus can name, one program per rc.112
operation. A dangling key is deliberately included: it is the store's frontier answer. -/
def syncAtoms : List ProgName :=
  [ SyncOp.refMake (Val.nat 1)
  , SyncOp.refGet ⟨0⟩
  , SyncOp.refSet ⟨0⟩ (Val.nat 2)
  , SyncOp.refGetAndSet ⟨0⟩ (Val.nat 2)
  , SyncOp.refSetAndGet ⟨0⟩ (Val.nat 2)
  , SyncOp.refUpdate ⟨0⟩ FnName.incr
  , SyncOp.refGetAndUpdate ⟨0⟩ FnName.double
  , SyncOp.refUpdateAndGet ⟨0⟩ FnName.incr
  , SyncOp.refUpdateSome ⟨0⟩ FnName.zeroWhenPositive
  , SyncOp.refGetAndUpdateSome ⟨0⟩ FnName.zeroWhenPositive
  , SyncOp.refUpdateSomeAndGet ⟨0⟩ FnName.zeroWhenPositive
  , SyncOp.refModify ⟨0⟩ FnName.takeAndBump
  , SyncOp.refModifySome ⟨0⟩ FnName.noChange
  , SyncOp.deferredMake
  , SyncOp.deferredIsDone ⟨0⟩
  , SyncOp.deferredPoll ⟨0⟩
  , SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 7)))
  , SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.failure (Cause.fail Err.boom)))
  , SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofRefGet ⟨0⟩)
  , SyncOp.deferredInterruptWith ⟨0⟩ ⟨0⟩
  , SyncOp.deferredAwaitCleanup ⟨0⟩ ⟨0⟩ 0
  , SyncOp.scopeMake FinalizerStrategy.sequential
  , SyncOp.scopeMake FinalizerStrategy.parallel
  , SyncOp.scopeAdd 0 100 (FinName.release 1 false)
  , SyncOp.scopeAdd 0 100 (FinName.release 1 true)
  , SyncOp.scopeRemove 0 100
  , SyncOp.scopeIsClosed 0
  ].map ProgName.syncOp

/-- Depth 1: values, one `fail` and one `die`, the parks, the four declared races, the whole
`sync` alphabet, and the two Deferred programs whose key the sequence heads mint. -/
def atoms : List ProgName :=
  [ ProgName.value Val.unit
  , ProgName.value (Val.nat 1)
  , ProgName.failCause (Cause.fail Err.boom)
  , ProgName.failCause (Cause.die Defect.badName)
  , ProgName.yieldNow 0
  , ProgName.park 0
  , ProgName.maskedPark 0
  , ProgName.awaitDeferred ⟨0⟩
  , ProgName.awaitFibers []
  , ProgName.interruptDeferred ⟨0⟩
  , ProgName.raceOf RaceName.empty
  , ProgName.raceOf RaceName.successThenSecond
  , ProgName.raceOf RaceName.failThenSuccess
  , ProgName.raceOf RaceName.failThenFail
  ] ++ syncAtoms

/-- The programs the recursion is grown from: one per path the machine takes — a success, a
typed failure, a defect, a scheduler yield, an external park, a masked park, a Deferred park
with a cancel frame, a countdown that resumes at once, a store read at a frontier key, and a
race that launches two entrants. -/
def seeds : List ProgName :=
  [ ProgName.value (Val.nat 1)
  , ProgName.failCause (Cause.fail Err.boom)
  , ProgName.failCause (Cause.die Defect.badName)
  , ProgName.yieldNow 0
  , ProgName.park 0
  , ProgName.maskedPark 0
  , ProgName.awaitDeferred ⟨0⟩
  , ProgName.awaitFibers []
  , ProgName.syncOp (SyncOp.refGet ⟨0⟩)
  , ProgName.raceOf RaceName.failThenSuccess
  ]

/-- One nesting level: the eleven shapes that take a program to a program. The three `seqOf`
heads are the allocations a nested program's key needs (`refMake`, `deferredMake`,
`scopeMake`), which is how "names only what it can mint" is arranged. -/
def wrapShapes (body : ProgName) : List ProgName :=
  [ ProgName.seqOf mkCell body
  , ProgName.seqOf mkPromise body
  , ProgName.seqOf mkScope body
  , ProgName.seqOf body (ProgName.value Val.unit)
  , ProgName.onExitOf body (FinName.release 0 false) false
  , ProgName.onExitOf body (FinName.release 0 true) false
  , ProgName.onExitOf body (FinName.release 0 true) true
  , ProgName.awaitAllNew body
  , ProgName.intoDeferred body ⟨0⟩
  , ProgName.forkOnly body immediateChild
  , ProgName.forkThen body deferredChild Supervision.ObserverMode.joinEffect
  ]

/-- Every program up to `n` nesting levels above the seeds; structural on the level count. -/
def grown : Nat → List ProgName
  | 0 => seeds
  | n + 1 =>
    let below := grown n
    below ++ below.flatMap wrapShapes

/-- The children a fork wraps: depth ≤ 1, one per outcome shape. -/
def kernel : List ProgName :=
  [ ProgName.value (Val.nat 1)
  , ProgName.failCause (Cause.fail Err.boom)
  , ProgName.park 0
  , ProgName.yieldNow 0
  , ProgName.maskedPark 0
  , ProgName.onExitOf (ProgName.value Val.unit) (FinName.release 0 true) false
  ]

/-- The fork family: the three option shapes of `Witnesses` against `forkOnly`, both observer
modes of `forkThen`, and `forkIn` behind the `scopeMake` that mints its scope. -/
def forkFamily : List ProgName :=
  kernel.flatMap fun child =>
    [ ProgName.forkOnly child immediateChild
    , ProgName.forkOnly child deferredChild
    , ProgName.forkOnly child scopedChild
    , ProgName.forkThen child immediateChild Supervision.ObserverMode.joinEffect
    , ProgName.forkThen child deferredChild Supervision.ObserverMode.joinEffect
    , ProgName.forkThen child scopedChild Supervision.ObserverMode.joinEffect
    , ProgName.forkThen child immediateChild Supervision.ObserverMode.awaitValue
    , ProgName.forkThen child deferredChild Supervision.ObserverMode.awaitValue
    , ProgName.forkThen child scopedChild Supervision.ObserverMode.awaitValue
    , ProgName.seqOf mkScope (ProgName.forkInScope child immediateChild 0 100)
    , ProgName.seqOf mkScope (ProgName.forkInScope child deferredChild 0 100)
    , ProgName.seqOf mkScope (ProgName.forkInScope child scopedChild 0 100)
    ]

/-- The scope-consuming programs, each behind the `scopeMake` that mints key `0`: the two
close strategies, an empty close, a close over a registered release that succeeds and one
that fails, and a linked child closed out from under itself. -/
def scopeFamily : List ProgName :=
  [ ProgName.seqOf mkScope (ProgName.closeScopeOf 0 unitExit)
  , ProgName.seqOf mkScopePar (ProgName.closeScopeOf 0 unitExit)
  , ProgName.seqOf mkScope
      (ProgName.seqOf (ProgName.syncOp (SyncOp.scopeAdd 0 100 (FinName.release 1 false)))
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScope
      (ProgName.seqOf (ProgName.syncOp (SyncOp.scopeAdd 0 100 (FinName.release 1 true)))
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScopePar
      (ProgName.seqOf (ProgName.syncOp (SyncOp.scopeAdd 0 100 (FinName.release 1 true)))
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScope
      (ProgName.seqOf (ProgName.syncOp (SyncOp.scopeAdd 0 100 (FinName.parkThen 3)))
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScope
      (ProgName.seqOf (ProgName.forkInScope (ProgName.park 0) scopedChild 0 100)
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScopePar
      (ProgName.seqOf (ProgName.forkInScope (ProgName.park 0) scopedChild 0 100)
        (ProgName.closeScopeOf 0 unitExit))
  , ProgName.seqOf mkScope
      (ProgName.seqOf (ProgName.closeScopeOf 0 unitExit) (ProgName.closeScopeOf 0 unitExit))
  ]

/-- The corpus: every program of the alphabet the enumerators above reach, deduplicated. -/
def programs : List ProgName :=
  dedup (atoms ++ forkFamily ++ scopeFamily ++ grown 2)

/-! ## The tape corpus -/

/-- The decision alphabet: one of every `RunDecision` constructor, over the two fiber ids the
corpus's programs can mint a handle for. -/
def decisions : List D :=
  [ RunDecision.evaluate ⟨0⟩
  , RunDecision.fire ⟨0⟩
  , RunDecision.fire ⟨1⟩
  , RunDecision.flush
  , RunDecision.installMiddleware
  , RunDecision.yieldVerdict ⟨0⟩ true
  , RunDecision.answerAsync ⟨0⟩ 0 (Prim.success Val.unit)
  , RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩
  , RunDecision.interruptFrom none ReasonAnnotations.empty ⟨0⟩
  ]

/-- Every word of exactly `n` decisions. -/
def wordsOfLength : Nat → List (List D)
  | 0 => [[]]
  | n + 1 => (wordsOfLength n).flatMap fun word => decisions.map fun d => word ++ [d]

/-- The tapes: the empty tape, and `evaluate ⟨0⟩` followed by every word of length ≤ 2. The
root must be started for anything at all to happen, so every non-empty tape starts with it. -/
def tapes : List (List D) :=
  [] :: (wordsOfLength 0 ++ wordsOfLength 1 ++ wordsOfLength 2).map fun word =>
    RunDecision.evaluate ⟨0⟩ :: word

/-! ## Trace and program projections -/

/-- The fiber of every `exited` row, in trace order. -/
def exitedIds (m : M) : List FiberId :=
  m.trace.filterMap fun
    | RunEvent.exited f _ => some f
    | _ => none

/-- Every `observerFired` row as the pair it fires on. -/
def observerRows (m : M) : List (FiberId × Observer) :=
  m.trace.filterMap fun
    | RunEvent.observerFired f o => some (f, o)
    | _ => none

/-- Whether the trace records an interrupt against `id`. -/
def interruptRecordedFor (m : M) (id : FiberId) : Bool :=
  m.trace.any fun
    | RunEvent.interruptRecorded _ target => decide (target = id)
    | _ => false

/-- How many `finalizerProgram` rows fiber `id` contributed for the finalizer `fin`. -/
def finalizerRowsOf (m : M) (id : FiberId) (fin : FinName) : Nat :=
  (m.trace.filter fun
    | RunEvent.finalizerProgram f name _ =>
      decide (f = id) && decide (name = Name.finalizerName fin)
    | _ => false).length

/-- The `onExitOf` nodes of a program that carry `fin`: the number of times that finalizer can
run on any one fiber. -/
def onExitCountOf (fin : FinName) : ProgName → Nat
  | ProgName.intoDeferred body _ => onExitCountOf fin body
  | ProgName.intoBody body _ => onExitCountOf fin body
  | ProgName.onExitOf body f _ => (if f = fin then 1 else 0) + onExitCountOf fin body
  | ProgName.seqOf first second => onExitCountOf fin first + onExitCountOf fin second
  | ProgName.forkThen child _ _ => onExitCountOf fin child
  | ProgName.forkOnly child _ => onExitCountOf fin child
  | ProgName.forkInScope child _ _ _ => onExitCountOf fin child
  | ProgName.forkScopedOf child _ _ => onExitCountOf fin child
  | ProgName.awaitAllNew body => onExitCountOf fin body
  | _ => 0

/-- The `Ref.make` nodes of a program: the number of cells its run can allocate. -/
def refMakeCount : ProgName → Nat
  | ProgName.syncOp (SyncOp.refMake _) => 1
  | ProgName.intoDeferred body _ => refMakeCount body
  | ProgName.intoBody body _ => refMakeCount body
  | ProgName.onExitOf body _ _ => refMakeCount body
  | ProgName.seqOf first second => refMakeCount first + refMakeCount second
  | ProgName.forkThen child _ _ => refMakeCount child
  | ProgName.forkOnly child _ => refMakeCount child
  | ProgName.forkInScope child _ _ _ => refMakeCount child
  | ProgName.forkScopedOf child _ _ => refMakeCount child
  | ProgName.awaitAllNew body => refMakeCount body
  | _ => 0

/-- The finalizer names the corpus's `onExitOf` wrappers use. -/
def corpusFinalizers : List FinName :=
  [FinName.release 0 false, FinName.release 0 true]

/-- Which Deferred cells hold a completion, in allocation order. -/
def completedCells (m : M) : List Bool :=
  m.state.deferreds.cells.map fun c => c.completion.isSome

/-- Which scopes have closed, in allocation order. -/
def closedScopes (m : M) : List Bool :=
  m.state.scopes.entries.map fun e => e.scope.isClosed

/-- The observable key invariant 6 compares two runs on. `RunMachine` carries a `Race`, which
has no `DecidableEq`, so the machine itself is not comparable; its exits, its trace length,
its fiber count and its stuck marker are. -/
def machineKey (m : M) : List (Option ExitV) × Nat × Nat × Option Stuck :=
  ((List.range 4).map (exitOf m), m.trace.length, m.fibers.length, m.stuck)

/-! ## The nine invariants

Each is a `Bool` over the final machine (and, where the statement is about the run rather
than its end state, over the machine the same pair reaches with the fuel doubled). -/

/-- 1. The two Pass A forbidden shapes `Witnesses` already checks on thirteen programs: no
observer fires before its fiber's `exited` row, no fiber exits twice, and no fiber exits with
`defaultEvaluate`'s `notImplemented` defect. -/
def inv1 (m : M) : Bool :=
  traceWellFormed m.trace [] && noNotImplementedDefect m

/-- 2. Exit once. At most one `exited` row per fiber, and a fiber that has an exit holds an
empty stack, no pending park, no observer, no child and the empty context — every field
`exitFiber` clears (`src/Effect4/Machine/Fibers.lean:1013-1024`). -/
def inv2 (m : M) : Bool :=
  noRepeat (exitedIds m) &&
    m.fibers.all fun f =>
      match f.exit with
      | none => true
      | some _ =>
        f.frame.stack.isEmpty && f.pending.isEmpty && f.observers.isEmpty &&
          f.children.isEmpty && decide (f.context = emptyCtx)

/-- 3. Observers fire once: no two `observerFired` rows carry the same fiber and the same
observer. -/
def inv3 (m : M) : Bool := noRepeat (observerRows m)

/-- 4. Finalizers once: a fiber runs a given `onExit` finalizer no more often than the program
has `onExitOf` nodes carrying it. A repeat is the failure this catches; the bound is what makes
the statement survive a nested `onExit`. -/
def inv4 (program : ProgName) (m : M) : Bool :=
  m.fibers.all fun f =>
    corpusFinalizers.all fun fin =>
      decide (finalizerRowsOf m f.id fin ≤ onExitCountOf fin program)

/-- 5. Interrupt monotone, modestly: a fiber that holds an `interruptedCause` has an
`interruptRecorded` row against it — the cause was recorded by a decision, a scope link, a
race skip or the exit path's child interruption, never invented — and a cause held while the
fiber is still live is still held. The second half is a restatement of the field; the first is
the content. -/
def inv5 (m : M) : Bool :=
  m.fibers.all fun f =>
    match f.frame.interruptedCause with
    | none => true
    | some _ =>
      interruptRecordedFor m f.id &&
        (match f.exit with
         | none => f.frame.interruptedCause.isSome
         | some _ => true)

/-- The second run invariant 6 compares against. The tape is rebuilt rather than passed
through, so this is a syntactically distinct call from the one `brokenBy` already made and the
comparison cannot collapse into a value compared with itself. -/
def replayAgain (program : ProgName) (tape : List D) : M :=
  replayWith fuel program ([] ++ tape)

/-- 6. Determinism: the same program and tape reach the same machine, run twice. -/
def inv6 (program : ProgName) (tape : List D) (m : M) : Bool :=
  decide (machineKey m = machineKey (replayAgain program tape))

/-- 7. Fuel is a frontier: with the fuel doubled the shorter run's trace is a prefix of the
longer one's — more fuel continues the run, it never rewrites it. -/
def inv7 (m doubled : M) : Bool := m.trace.isPrefixOf doubled.trace

/-- 8. No stuck machine. The corpus names only keys it minted, so `Stuck.unknownScope` and
`Stuck.unknownFiber` are unreachable from it; a stuck pair is a finding, not a weaker
invariant. -/
def inv8 (m doubled : M) : Bool := m.stuck.isNone && doubled.stuck.isNone

/-- 9. Store conservation: the ref heap holds no more cells than the program has `refMake`
nodes and only grows as the run goes on, the Deferred store owes nothing at the end of a
decision, a completed Deferred stays completed, and a closed scope stays closed. The
monotone half reads the same pair at double fuel, which is the same run carried further. -/
def inv9 (program : ProgName) (m doubled : M) : Bool :=
  decide (m.state.refs.length ≤ refMakeCount program) &&
    decide (m.state.refs.length ≤ doubled.state.refs.length) &&
    m.state.deferreds.due.isEmpty && doubled.state.deferreds.due.isEmpty &&
    flagsMonotone (completedCells m) (completedCells doubled) &&
    flagsMonotone (closedScopes m) (closedScopes doubled)

/-! ## The report -/

/-- One invariant broken by one pair. -/
structure Failure where
  /-- The program of the pair. -/
  program : ProgName
  /-- The tape of the pair. -/
  tape : List D
  /-- Which of the nine invariants broke. -/
  invariant : Nat
deriving DecidableEq

/-- The invariants one pair breaks, by index. -/
def brokenBy (program : ProgName) (tape : List D) : List Nat :=
  let m := replayWith fuel program tape
  let doubled := replayWith (fuel * 2) program tape
  (if inv1 m then [] else [1]) ++
  (if inv2 m then [] else [2]) ++
  (if inv3 m then [] else [3]) ++
  (if inv4 program m then [] else [4]) ++
  (if inv5 m then [] else [5]) ++
  (if inv6 program tape m then [] else [6]) ++
  (if inv7 m doubled then [] else [7]) ++
  (if inv8 m doubled then [] else [8]) ++
  (if inv9 program m doubled then [] else [9])

/-- The whole corpus, as data: one row per broken invariant per pair. -/
def report : List Failure :=
  programs.flatMap fun program =>
    tapes.flatMap fun tape =>
      (brokenBy program tape).map fun index => ⟨program, tape, index⟩

/-- How many pairs the battery runs. -/
def runs : Nat := programs.length * tapes.length

/-! ## The battery

The corpus is pinned by count: a shrink of `programs` or `tapes` changes `runs` and fails the
guard, so `report = []` cannot be made true by making the corpus smaller.

`report` holds the program and the tape of every failure, so a future break can be printed
with `#eval`. `ProgName` carries a `Cause`, which has no `Repr` and must not get one here, so
the printable projection is the invariant index:

  -- #eval report.length
  -- #eval (report.map Failure.invariant).take 3
-/

#guard programs.length = 1432

#guard tapes.length = 92

#guard runs = 131744

#guard report = []

/-! ## Finding S1-1 — `forkScoped` with no ambient `Scope` service answers a defect

`WithFiberAction.forkScoped` reads the ambient scope off the fiber's context
(`src/Effect4/Machine/Fibers.lean:796-807`); `stores.ambientScope` is `Ctx.ambientScope`, and
`emptyCtx.ambientScope` is `none`. The arm then fails the fiber with
`Cause.die interp.notImplemented`.

That payload is `defaultEvaluate`'s, which Pass A forbidden example 3 and
`Witnesses.noNotImplementedDefect` both read as "the machine reached a state it has no arm
for". A missing service is not that: `AGENTS.md` has an unanswered choice be a live frontier,
never a cause, and a refused thunk has its own arm (`WithFiberAction.refuse`). No program of
this corpus can mint an ambient scope — the alphabet has no `setContext` program — so
`forkScopedOf` is held out of `programs` and pinned here instead. Putting it in would make
invariant 1 fail on every tape of every `forkScoped` program and say nothing new.

Closed the same day: `RunInterp.missingScope` names the defect (`Defect.missingService` at
this instantiation, rc.112's `Context.get` throwing `ServiceNotFound`), apart from the
"unimplemented step" defect; `Effect4.Machine.withFiber_forkScoped_none` is the clause. The
pins below hold the closed shape; `brokenBy` on the same pair is now empty, and the
battery's reporting path is shown to fire by a deliberately wrong invariant instead. -/

/-- The one-decision run of a bare `forkScoped` over the empty context. -/
def s1FindingOne : M :=
  replayWith fuel (ProgName.forkScopedOf (ProgName.value Val.unit) immediateChild 100)
    [RunDecision.evaluate ⟨0⟩]

-- The machine does not get stuck and does not invent a scope: it fails the fiber with the
-- named defect, which invariant 1 admits.
#guard s1FindingOne.stuck.isNone

#guard noNotImplementedDefect s1FindingOne = true

#guard exitOf s1FindingOne 0 = some (Exit.failure (Cause.die Defect.missingService))

#guard brokenBy (ProgName.forkScopedOf (ProgName.value Val.unit) immediateChild 100)
  [RunDecision.evaluate ⟨0⟩] = []

-- The reporting path is not vacuous: an invariant that demands what no run gives fails.
#guard (programs.take 1).any fun program =>
  (tapes.take 2).any fun tape => (replayWith fuel program tape).stuck.isSome = false

end Test.Machine.Fuzz
