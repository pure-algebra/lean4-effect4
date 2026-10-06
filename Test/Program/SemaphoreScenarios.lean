import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Modules.Semaphore.Steps

/-!
# Semaphore on the machine: the wake's first check (decisions rows 259 to 261 and 265)

Decisions row 259 rules the live scan. It rests on a reading of the machine: a waiter runs
inside the task that resolves its hint (`DeferredStore.complete`,
`src/Effect4/Machine/Stores.lean`; `drainOwed` and the resume clause of `driveStep`,
`src/Effect4/Machine/Fibers.lean`). This battery runs Semaphore programs on the Lean machine and
compares each answer with the pinned Effect's, case by case. The pin's answers are the probe's
(`docs/research/2026-10-05-claude-lead/module-cards/semaphore-probes/semaphore-wake.rc112.out`).

| Case | The schedule | The pin's answer |
| --- | --- | --- |
| P1 | A total of 2. A holds 2 in a protected body. B asks for 2, then C for 1. A's hook releases 2 | B takes 2 inside the walk. The walk reads 0 and stops. C's entry is not visited |
| P2 | The root holds 1 and 1. B asks for 2, then C for 1. The root releases 1 | The release answers 1. The walk passes B and resumes C, which takes 1. B's entry stays in its place |
| P3 | The root holds 2. B asks for 1 and then for 1 again, with no yield. C asks for 1. The root releases 2 | B takes 1 and takes 1 again inside the walk. C waits |
| P4 | A holds 2, protected. B and C wait in the protected form, for 2 and for 1 | B's body and its release run inside the walk. Then C's body runs. Nothing stays taken |
| P7 | A total of 1, held. A raw waiter is interrupted, then a protected waiter | Each waiter's entry leaves, and `taken` does not change |
| P9 | P1, with B told to yield once, at its resume | The walk goes on, and C takes 1. B then reads 1 free and waits again with a new entry |

**The operations here are test fixtures.** `take` wraps the take step with a wait and a
withdrawal on interruption. `release` posts one helper, whose body is the walk (decisions row
238). `withPermits` is a protected body by `onExit`. `uninterruptible` stands for the mask and
`interruptible` for its restore, which is right under an interruptible caller only. The public
operations come with the wrapper's slice, after the mask.

**The steps are the library's** (`src/Effect4/Modules/Semaphore/Steps.lean`): the take step, the
release step, the visit and the withdrawal. One more run, T1, is the take that never waits.

**The settings of every run.**

- The tape is `[evaluate root, flush]`. P9's tape holds one more decision between the two:
  `yieldVerdict` for fiber 2, which is B.
- The fuel is 20000, and the compile fuel is 20000.
- The budget of operations before a yield is the default, 2048 for each fiber. No run but P9
  holds an injected yield.
- A child is forked with the default options: it starts at once. The helper is posted: a
  detached fork with a deferred start, uninterruptible.
- The root yields four times after it releases, and then it reads the cell.

A count is `[taken, the number of waiters, their counts, their stamps]`. A stamp tells one
enrolment from another: a waiter that waits again has a new stamp.

Placement. Each scenario is a finite control of the proposed claim `semaphore-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the steps' use in a
program. The cases P1, P3 and P9 are the finite controls of row 259's reading of the machine
(concept `reactive-scheduling`, requirement R12). Every guard is one run on one schedule. None
proves delivery, a cancellation law, a law of the wake across visits or liveness, and none is a
host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Queue (nilT noneT len snoc notT ifT noneOf)
open Effect4.Semaphore (takeStep takeIfAvailableStep releaseStep visitStep withdrawStep visitFrom
  eligibleT)

/-! ## The operations, as fixtures

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder. Here
every other term under the binder is closed or is this battery's own: a count that each
scenario writes as a literal, and the identity, the hint and the cursor that the operation
binds itself. The public wrapper will mint the name. -/

/-- Decisions row 238: a detached fork with a deferred start, uninterruptible. -/
def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- The pin's `onInterrupt`: `onExit` with a test of the exit. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- A policy: the take and the release that a scenario runs. The library's policy is `live`.
Each red control is one more policy. -/
structure Ops where
  take : TermSrc → TermSrc → Src NativeOp
  release : TermSrc → TermSrc → Src NativeOp

/-- The walk, over a visit step: one visit at a time. A visit that selects a waiter resolves
its hint, and the walk continues at that waiter's stamp plus one. The loop's cursor is an
option: none ends the walk. -/
def walkWith (visit : TermSrc → TermSrc → TermSrc) (q : TermSrc) : Src NativeOp :=
  iterateWith (app "some" [nat 0])
    { cursorTy := some (.option .nat)
      while_ := fun c => app "isSome" [c]
      body := fun c => eff do
        let r ← Ref.modify "s" (visit (app "getOrElse" [c, nat 0]) (var "s")) q
        selectOption "w" r (succeed noneT)
          (andThen (Deferred.succeed (field (var "w") "hint") unit)
            (succeed (app "some" [app "add" [field (var "w") "stamp", nat 1]])))
      step := fun _ a => a
      result := fun _ => unit }

/-- `release`, over a walk: the release step, then one posted helper where a waiter is
enrolled. Answer: the free count. -/
def releaseWith (walker : TermSrc → Src NativeOp) (count q : TermSrc) : Src NativeOp := eff do
  let r ← Ref.modify "s" (releaseStep count (var "s")) q
  let _ ← ifElse (tupleAt r 1)
    (andThen (withFiber (Action.fork (walker q) posted)) (succeed unit))
    (succeed unit)
  return tupleAt r 0

def withdraw (id q : TermSrc) : Src NativeOp :=
  andThen (Ref.modify "s" (withdrawStep id (var "s")) q) (succeed unit)

/-- `take`: the take step, and a wait on the request's hint where it does not take. A resumed
request runs the take step again, which checks the count again. An interrupted wait withdraws
the request. -/
def take (count q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    iterateWith (bool false)
      { while_ := fun done => notT done
        body := fun _ => eff do
          let hint ← Deferred.make .unit .never
          let took ← Ref.modify "s" (takeStep count id hint (var "s")) q
          ifElse took (succeed (bool true))
            (andThen (onInterrupt (interruptible (Deferred.await hint)) (withdraw id q))
              (succeed (bool false)))
        step := fun _ a => a
        result := fun _ => unit })

/-- The live scan (decisions row 259). -/
def live : Ops := { take := take, release := releaseWith (walkWith visitStep) }

/-- The protected form: the take, then the body under the restore, with the release at every
exit. The take and the hook's installation are one masked region. -/
def withPermits (ops : Ops) (count q : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  uninterruptible (andThen (ops.take count q)
    (onExit "e" (interruptible body) (andThen (ops.release count q) (succeed unit))))

/-! ## The three changed policies of the red controls -/

/-- A visit that looks at the head of the list alone (the card's section 9). -/
def visitHeadStep (cursor s : TermSrc) : TermSrc :=
  let waiters := field s "waiters"
  visitFrom
    (foldWith (app "take" [waiters, nat 1]) (noneOf waiters) fun _ w =>
      ifT (eligibleT cursor s w) waiters (noneOf waiters))
    s

def headOnly : Ops := { take := take, release := releaseWith (walkWith visitHeadStep) }

/-- A retry that takes with no second check (the card's section 9). -/
def takeNoCheck (count q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let hint ← Deferred.make .unit .never
    let took ← Ref.modify "s" (takeStep count id hint (var "s")) q
    ifElse took (succeed unit)
      (andThen (onInterrupt (interruptible (Deferred.await hint)) (withdraw id q))
        (Ref.update "s"
          (recordSet (var "s") "taken" (app "add" [field (var "s") "taken", count])) q)))

def noSecondCheck : Ops :=
  { take := takeNoCheck, release := releaseWith (walkWith visitStep) }

/-- A walk that commits a count for every waiter that fits, before any of them runs: the grant
at the wake, which row 259 rejects. It resolves the hints afterwards. -/
def grantWalk (q : TermSrc) : Src NativeOp := eff do
  let first ← Deferred.make .unit .never
  let granted ← Ref.make (app "take" [app "cons" [first, nilT], nat 0])
  let _ ← iterateWith (app "some" [nat 0])
    { cursorTy := some (.option .nat)
      while_ := fun c => app "isSome" [c]
      body := fun c => eff do
        let r ← Ref.modify "s" (visitStep (app "getOrElse" [c, nat 0]) (var "s")) q
        selectOption "w" r (succeed noneT)
          (andThen
            (Ref.update "s"
              (recordSet (var "s") "taken"
                (app "add" [field (var "s") "taken", field (var "w") "need"]))
              q)
            (andThen (Ref.update "g" (snoc (var "g") (field (var "w") "hint")) granted)
              (succeed (app "some" [app "add" [field (var "w") "stamp", nat 1]]))))
      step := fun _ a => a
      result := fun _ => unit }
  let hints ← Ref.get granted
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len hints]
      body := fun i => selectOption "h" (app "get" [hints, i]) (succeed unit)
        (andThen (Deferred.succeed (var "h") unit) (succeed unit))
      step := fun i _ => app "succ" [i]
      result := fun _ => unit }

/-- A granted request holds its permits when its hint resolves: it does not take again. -/
def takeGranted (count q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let hint ← Deferred.make .unit .never
    let took ← Ref.modify "s" (takeStep count id hint (var "s")) q
    ifElse took (succeed unit)
      (onInterrupt (interruptible (Deferred.await hint)) (withdraw id q)))

def grant : Ops := { take := takeGranted, release := releaseWith grantWalk }

/-! ## What a scenario observes -/

/-- The empty list of numbers. -/
def noNumbers : TermSrc := app "take" [app "cons" [nat 0, nilT], nat 0]

/-- A fiber writes its mark when it goes on. -/
def mark (log k : TermSrc) : Src NativeOp := Ref.update "l" (snoc (var "l") k) log

def needsOf (s : TermSrc) : TermSrc :=
  foldWith (field s "waiters") noNumbers fun acc w => snoc acc (field w "need")

def stampsOf (s : TermSrc) : TermSrc :=
  foldWith (field s "waiters") noNumbers fun acc w => snoc acc (field w "stamp")

/-- The cell's counts: `[taken, the number of waiters, their counts, their stamps]`. -/
def counts (q : TermSrc) : Src NativeOp := eff do
  let s ← Ref.get q
  return tuple [field s "taken", len (field s "waiters"), needsOf s, stampsOf s]

/-- The root yields four times: the posted helpers and the resumed fibers run. -/
def settle : Src NativeOp := forRange (nat 0) (nat 4) fun _ => yieldNow 0

/-! ## Runs -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

def budget : Api.Budget := { fuel := 20000, compileFuel := 20000 }

/-- A source's run on a tape of decisions, through the checked session. -/
def runOn (tape : List Api.Decision) (src : Src NativeOp) : Option Run :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => none
  | .ok b => some ((Run.open b "semaphore" budget).play (Rows.tape tape))

/-- The ordinary tape: the root evaluated, then one flush of every armed dispatcher. -/
def plain : List Api.Decision := [Api.evaluate, Api.flush]

/-- P9's tape. The root is evaluated to its first yield, where every other fiber is parked.
Fiber 2 is then told to yield at its next check, which is its resume. Then the flush. -/
def yieldAtResume : List Api.Decision := [Api.evaluate, .yieldVerdict ⟨2⟩ true, Api.flush]

/-- The root's exit on a tape. -/
def exitOn (tape : List Api.Decision) (src : Src NativeOp) : Option ExitV :=
  (runOn tape src).bind (·.exit)

def exitOf (src : Src NativeOp) : Option ExitV := exitOn plain src

/-- The fibers that exited, in the order of their exits. -/
def exitsOn (tape : List Api.Decision) (src : Src NativeOp) : Option (List Nat) :=
  (runOn tape src).map fun r => r.machine.trace.filterMap fun
    | .exited fiber _ => some fiber.value
    | _ => none

/-- The injected yields of a run: the fiber, and its count of operations at the yield. -/
def yieldsOn (tape : List Api.Decision) (src : Src NativeOp) : Option (List (Nat × Nat)) :=
  (runOn tape src).map fun r => r.machine.trace.filterMap fun
    | .yieldInjected fiber atOp => some (fiber.value, atOp)
    | _ => none

/-! ## The cases -/

/-- P1 and P9, the protected case. A is fiber 1, B fiber 2 and C fiber 3. The root yields once
before it opens the gate: P9's tape tells B to yield there. -/
def p1 (ops : Ops) : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 2)
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (withPermits ops (nat 2) q (Deferred.await gate))
  let _ ← fork (eff do
    let _ ← ops.take (nat 2) q
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take (nat 1) q
    mark log (nat 31))
  let before ← counts q
  let _ ← yieldNow 0
  let _ ← Deferred.succeed gate unit
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P2, the scan case. B is fiber 1 and C fiber 2. -/
def p2 (ops : Ops) : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 2)
  let log ← Ref.make noNumbers
  let _ ← ops.take (nat 1) q
  let _ ← ops.take (nat 1) q
  let _ ← fork (eff do
    let _ ← ops.take (nat 2) q
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take (nat 1) q
    mark log (nat 31))
  let before ← counts q
  let answer ← ops.release (nat 1) q
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, answer, after, l]

/-- P3, the overtaking case. B is fiber 1 and C fiber 2. B writes 21 after its first take and
22 after its second. -/
def p3 (ops : Ops) : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 2)
  let log ← Ref.make noNumbers
  let _ ← ops.take (nat 2) q
  let _ ← fork (eff do
    let _ ← ops.take (nat 1) q
    let _ ← mark log (nat 21)
    let _ ← ops.take (nat 1) q
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take (nat 1) q
    mark log (nat 31))
  let before ← counts q
  let _ ← ops.release (nat 2) q
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P4, two protected waiters whose bodies do not wait. A body writes its mark with the taken
count that it reads: 20 or 30, plus the count. -/
def p4 (ops : Ops) : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 2)
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (withPermits ops (nat 2) q (Deferred.await gate))
  let _ ← fork (withPermits ops (nat 2) q (eff do
    let s ← Ref.get q
    mark log (app "add" [nat 20, field s "taken"])))
  let _ ← fork (withPermits ops (nat 1) q (eff do
    let s ← Ref.get q
    mark log (app "add" [nat 30, field s "taken"])))
  let before ← counts q
  let _ ← Deferred.succeed gate unit
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P7, the withdrawal. The root holds the one permit. A raw waiter is interrupted, then a
protected waiter. The root then releases. -/
def p7 (ops : Ops) : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 1)
  let _ ← ops.take (nat 1) q
  let b ← fork (ops.take (nat 1) q)
  let whileB ← counts q
  let _ ← withFiber (Action.interrupt b)
  let afterB ← counts q
  let c ← fork (withPermits ops (nat 1) q (succeed unit))
  let whileC ← counts q
  let _ ← withFiber (Action.interrupt c)
  let afterC ← counts q
  let answer ← ops.release (nat 1) q
  let _ ← settle
  let afterRelease ← counts q
  return tuple [whileB, afterB, whileC, afterC, answer, afterRelease]

/-- T1, the take that never waits: it takes 2 of 2, and a second request for 1 does not take
and does not enrol. -/
def t1 : Src NativeOp := eff do
  let q ← Ref.make (Semaphore.empty 2)
  let first ← Ref.modify "s" (takeIfAvailableStep (nat 2) (var "s")) q
  let second ← Ref.modify "s" (takeIfAvailableStep (nat 1) (var "s")) q
  let after ← counts q
  return tuple [first, second, after]

/-- A count as a value. -/
def count (taken : Nat) (needs stamps : List Nat) : Val :=
  .list [.nat taken, .nat needs.length, .list (needs.map .nat), .list (stamps.map .nat)]

def marks (ks : List Nat) : Val := .list (ks.map .nat)

-- Each scenario builds under the live scan: the checker types every step inside its
-- `Ref.modify`.
#guard [p1 live, p2 live, p3 live, p4 live, p7 live].map verdict = List.replicate 5 "built"

/-! ### The pin's answers, on the machine -/

-- P1. B took 2 inside the walk. The next visit read no free permit and stopped. C still waits,
-- with its first entry: the stamp 1.
#guard exitOf (p1 live) = some (.success (.list
  [count 2 [2, 1] [0, 1], count 2 [1] [1], marks [22]]))
-- P2. The release answered 1. The walk passed B and resumed C, which took 1. B's entry stays
-- in its place: the stamp 0.
#guard exitOf (p2 live) = some (.success (.list
  [count 2 [2, 1] [0, 1], .nat 1, count 2 [2] [0], marks [31]]))
-- P3. B took 1 and took 1 again, inside the walk. C waits with its first entry.
#guard exitOf (p3 live) = some (.success (.list
  [count 2 [1, 1] [0, 1], count 2 [1] [1], marks [21, 22]]))
-- P4. B's body saw 2 taken, then C's body saw 1. Nothing stays taken, and nobody waits.
#guard exitOf (p4 live) = some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [] [], marks [22, 31]]))
-- P7. Each interrupted waiter's entry leaves, and `taken` stays 1. The release then answers 1
-- free and posts no helper.
#guard exitOf (p7 live) = some (.success (.list
  [count 1 [1] [0], count 1 [] [], count 1 [1] [1], count 1 [] [], .nat 1, count 0 [] []]))
-- P9. B yielded at its resume. The walk went on and resumed C, which took 1. B then found 1
-- free, and it waits again with a new entry: the stamp 2.
#guard exitOn yieldAtResume (p1 live) = some (.success (.list
  [count 2 [2, 1] [0, 1], count 1 [2] [2], marks [31]]))

-- T1. The take that never waits answers true, then false, and nobody is enrolled.
#guard verdict t1 = "built" &&
  exitOf t1 = some (.success (.list [.bool true, .bool false, count 2 [] []]))

/-! ### The reading of the machine, on the trace

A waiter that a visit resumes runs inside the helper's task: it exits before the helper
does. -/

-- P1. The exits, in order: A, then B, then the helper (fiber 4), then C at the root's end.
#guard exitsOn plain (p1 live) = some [1, 2, 4, 3, 0]
-- P3. B (fiber 1) exits before the helper (fiber 3).
#guard exitsOn plain (p3 live) = some [1, 3, 2, 0]
-- P4. B and C both run to their exits inside the first helper (fiber 4). B's own release
-- posts a second helper (fiber 5), which finds nobody.
#guard exitsOn plain (p4 live) = some [1, 2, 3, 4, 5, 0]
-- P9. C exits inside the walk, the helper next, and B only at the root's end.
#guard exitsOn yieldAtResume (p1 live) = some [1, 3, 4, 2, 0]
-- P9's one injected yield is B's, at its first operation after the resume. No other run
-- holds an injected yield: the budget of 2048 operations is not reached.
#guard yieldsOn yieldAtResume (p1 live) = some [(2, 1)]
#guard [p1 live, p2 live, p3 live, p4 live, p7 live].map (yieldsOn plain) =
  List.replicate 5 (some [])
-- The settings: each fiber's budget of operations before a yield, at the end of P1.
#guard ((runOn plain (p1 live)).map fun r => r.machine.fibers.map (·.maxOpsBeforeYield)) =
  some (List.replicate 5 2048)
-- Before P9's verdict, the four fibers are parked and none has exited: B's next check is its
-- resume.
#guard ((runOn [Api.evaluate] (p1 live)).map fun r =>
    r.machine.fibers.map fun f => (f.id.value, decide (f.parked = .notParked), f.exit.isSome)) =
  some [(0, false, false), (1, false, false), (2, false, false), (3, false, false)]
-- Each run finishes, and each row of each tape is played: no decision is refused.
#guard ([p1 live, p2 live, p3 live, p4 live, p7 live].map fun src =>
    (runOn plain src).map fun r => (decide (r.inspect.outcome = .finished), r.phases)) =
  List.replicate 5 (some (true, [.progressed, .progressed]))
#guard ((runOn yieldAtResume (p1 live)).map fun r =>
    (decide (r.inspect.outcome = .finished), r.phases)) =
  some (true, [.progressed, .progressed, .progressed])
-- One flush is every flush: two more change nothing.
#guard exitOn [Api.evaluate, Api.flush, Api.flush, Api.flush] (p1 live) = exitOf (p1 live)

/-! ### The red controls: each changed policy fails its own case

Each changed policy builds, so typing does not catch it. -/

#guard [p2 headOnly, p3 grant, p1 noSecondCheck].map verdict = List.replicate 3 "built"

-- A walk that wakes the head alone fails P2: B does not fit, so C never proceeds. One permit
-- stays free while C waits.
#guard exitOf (p2 headOnly) = some (.success (.list
  [count 2 [2, 1] [0, 1], .nat 1, count 1 [2, 1] [0, 1], marks []]))
#guard exitOf (p2 headOnly) != exitOf (p2 live)
-- The head-only walk still gives P1's answer: P2 is the case that tells the two apart.
#guard exitOf (p1 headOnly) = exitOf (p1 live)

-- A walk that commits for every fitting waiter before any of them runs fails P3: C holds a
-- permit, and B's second request waits (a new entry, the stamp 2).
#guard exitOf (p3 grant) = some (.success (.list
  [count 2 [1, 1] [0, 1], count 2 [1] [2], marks [21, 31]]))
#guard exitOf (p3 grant) != exitOf (p3 live)

-- A retry with no second check fails the accounting on P9: C takes 1 while B has yielded, and
-- B then takes 2. Three permits of two are taken.
#guard exitOn yieldAtResume (p1 noSecondCheck) = some (.success (.list
  [count 2 [2, 1] [0, 1], count 3 [] [], marks [31, 22]]))
-- With no yield the same retry gives P1's answer: P9's path is the one that shows the fault.
#guard exitOf (p1 noSecondCheck) = exitOf (p1 live)

end Test.Program.SemaphoreScenarios
