import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Library.Semaphore.Ops
import Effect4.Store.Carrier.Fold
import Effect4.Store.Domain.ProgramWire

/-! Program data shared by the battery and engine fixture writer. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Semaphore (takeStep takeIfAvailableStep releaseStep visitStep withdrawStep visitFrom
  eligibleT)

/-! ## The operations of a scenario -/

/-- The operations that a scenario runs: the handle stands first, as in the library. The
library's are `library`. A written form and a changed policy are more values. -/
structure Ops where
  take : TermSrc → TermSrc → Src NativeOp
  release : TermSrc → TermSrc → Src NativeOp
  withPermits : TermSrc → TermSrc → Src NativeOp → Src NativeOp

/-- The library's operations. -/
def library : Ops :=
  { take := Semaphore.take, release := Semaphore.release, withPermits := Semaphore.withPermits }

/-! ## The written forms: the fixtures of the earlier slice

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder. So a
caller's variable named `s` would read the cell's value there, and the same holds of `id`,
`hint`, `took`, `r`, `w` and `e` at their binders. The texts are the earlier slice's
(`git:59241284:Test/Program/SemaphoreScenarios.lean`), with the count before the handle. -/

namespace Written

/-- The pin's `onInterrupt`, with the exit under the written name `e`. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- The walk, over a visit step, with the names `s`, `r` and `w` written. -/
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
enrolled. -/
def releaseWith (walker : TermSrc → Src NativeOp) (count q : TermSrc) : Src NativeOp := eff do
  let r ← Ref.modify "s" (releaseStep count (var "s")) q
  let _ ← ifElse (tupleAt r 1)
    (andThen (withFiber (Action.fork (walker q) posted)) (succeed unit))
    (succeed unit)
  return tupleAt r 0

def withdraw (id q : TermSrc) : Src NativeOp :=
  andThen (Ref.modify "s" (withdrawStep id (var "s")) q) (succeed unit)

/-- `take`, as the fixture writes it: the stand-in mask, and a loop whose cursor is a Boolean. -/
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

/-- The protected form, as the fixture writes it: the take, then the body under the stand-in
restore, with the release at every exit. -/
def withPermits (count q : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  uninterruptible (andThen (take count q)
    (onExit "e" (interruptible body)
      (andThen (releaseWith (walkWith visitStep) count q) (succeed unit))))

/-- The written forms, as the operations of a scenario. -/
def ops : Ops :=
  { take := fun q count => take count q
    release := fun q count => releaseWith (walkWith visitStep) count q
    withPermits := fun q count body => withPermits count q body }

end Written

/-! ## A policy: Semaphore's part, with its knobs

The library's operations are the shared forms over three pieces of Semaphore's own: the take's
loop at a restore site, the helper's body, and the release around that helper. A policy holds
the first two. Each red control changes one. -/

/-- The walk over a visit step. The library's walk is the walk over `visitStep`. -/
def walkOver (visit : TermSrc → TermSrc → TermSrc) (q : TermSrc) : Src NativeOp :=
  iterateWith (app "some" [nat 0])
    { while_ := fun cursor => app "isSome" [cursor]
      body := fun cursor =>
        bindWith (Ref.modifyWith q (visit (app "getOrElse" [cursor, nat 0]))) fun selected =>
          selectOptionWith selected (succeed noneT) fun waiter =>
            andThen (Deferred.succeed (field waiter "hint") unit)
              (succeed (app "some" [app "add" [field waiter "stamp", nat 1]]))
      step := fun _ next => next
      result := fun _ => unit }

/-- `release` over a helper's body. The library's release is the release over `Semaphore.walk`. -/
def releaseOver (helper : TermSrc → Src NativeOp) (q count : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (releaseStep count)) fun reply =>
      andThen
        (ifElse (tupleAt reply 1)
          (andThen (withFiber (Action.fork (helper q) posted)) (succeed unit))
          (succeed unit))
        (succeed (tupleAt reply 0)))

/-- A policy: the take's loop at a restore site, and the body of a release's helper. -/
structure Policy where
  takeAt : (Src NativeOp → Src NativeOp) → TermSrc → TermSrc → Src NativeOp :=
    fun restore q count => waitRetryAt restore .nat Semaphore.ended (Semaphore.taker q count)
  helper : TermSrc → Src NativeOp := Semaphore.walk

/-- The operations of a policy: the take under its own mask, the release over the policy's
helper, and the protected form over both. -/
def opsOf (p : Policy) : Ops :=
  { take := fun q count => uninterruptibleMaskWith fun restore => p.takeAt restore q count
    release := releaseOver p.helper
    withPermits := fun q count body =>
      protectedBy (fun restore => p.takeAt restore q count)
        (fun _ => releaseOver p.helper q count) (fun _ => body) }

/-- The tree of a source at a caller's scope of names. -/
def treeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-! ### The three changed policies of the red controls -/

/-- A visit that looks at the head of the list alone (the card's section 9). -/
def visitHeadStep (cursor s : TermSrc) : TermSrc :=
  let waiters := field s "waiters"
  visitFrom
    (foldWith (app "take" [waiters, nat 1]) (noneOf waiters) fun _ w =>
      ifT (eligibleT cursor s w) waiters (noneOf waiters))
    s

def headOnly : Ops := opsOf { helper := walkOver visitHeadStep }

/-- A retry that takes with no second check (the card's section 9): one attempt, and after the
wait the request adds its count. -/
def takeNoCheckAt (restore : Src NativeOp → Src NativeOp) (q count : TermSrc) : Src NativeOp :=
  bindWith (Deferred.make .unit .never) fun id =>
    bindWith (Deferred.make .unit .never) fun hint =>
      bindWith (Ref.modifyWith q (takeStep count id hint)) fun took =>
        ifElse took (succeed count)
          (andThen (waitAt restore hint (Ref.modifyWith q (withdrawStep id)))
            (andThen
              (Ref.updateWith q fun s =>
                recordSet s "taken" (app "add" [field s "taken", count]))
              (succeed count)))

def noSecondCheck : Ops := opsOf { takeAt := takeNoCheckAt }

/-- A walk that commits a count for every waiter that fits, before any of them runs: the grant
at the wake, which row 259 rejects. It resolves the hints afterwards. -/
def grantWalk (q : TermSrc) : Src NativeOp :=
  bindWith (Deferred.make .unit .never) fun first =>
    bindWith (Ref.make (app "take" [app "cons" [first, nilT], nat 0])) fun granted =>
      andThen
        (iterateWith (app "some" [nat 0])
          { while_ := fun cursor => app "isSome" [cursor]
            body := fun cursor =>
              bindWith (Ref.modifyWith q (visitStep (app "getOrElse" [cursor, nat 0])))
                fun selected =>
                  selectOptionWith selected (succeed noneT) fun waiter =>
                    andThen
                      (Ref.updateWith q fun s =>
                        recordSet s "taken" (app "add" [field s "taken", field waiter "need"]))
                      (andThen (Ref.updateWith granted fun g => snoc g (field waiter "hint"))
                        (succeed (app "some" [app "add" [field waiter "stamp", nat 1]])))
            step := fun _ next => next
            result := fun _ => unit })
        (bindWith (Ref.get granted) fun hints =>
          iterateWith (nat 0)
            { while_ := fun i => app "lt" [i, len hints]
              body := fun i => selectOptionWith (app "get" [hints, i]) (succeed unit) fun hint =>
                andThen (Deferred.succeed hint unit) (succeed unit)
              step := fun i _ => app "succ" [i]
              result := fun _ => unit })

/-- A granted request holds its permits when its hint resolves: it does not take again. -/
def takeGrantedAt (restore : Src NativeOp → Src NativeOp) (q count : TermSrc) : Src NativeOp :=
  bindWith (Deferred.make .unit .never) fun id =>
    bindWith (Deferred.make .unit .never) fun hint =>
      bindWith (Ref.modifyWith q (takeStep count id hint)) fun took =>
        ifElse took (succeed count)
          (andThen (waitAt restore hint (Ref.modifyWith q (withdrawStep id))) (succeed count))

def grant : Ops := opsOf { takeAt := takeGrantedAt, helper := grantWalk }

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

/-- The root's exit of the ordinary run at a fuel: the root evaluated, then one flush. The truth
lane runs each program so, at the fuel 1000. -/
def exitAt (fuel : Nat) (src : Src NativeOp) : Option ExitV :=
  (Effect4.Api.Author.build (mk src)).toOption.bind fun b => (Api.run b.program fuel).exit

/-- The answer and error types of a built source. -/
def typesOf (src : Src NativeOp) : Option (Ty × Ty) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => (b.ty.answer, b.ty.error)

/-- The canonical bytes of a source's built program. -/
def bytesOf (src : Src NativeOp) : Option Store.Bytes :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => Api.bytesOf b.program

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
def p1With (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (ops.withPermits q (nat 2) (Deferred.await gate))
  let _ ← fork (eff do
    let _ ← ops.take q (nat 2)
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take q (nat 1)
    mark log (nat 31))
  let before ← counts q
  let _ ← yieldNow 0
  let _ ← Deferred.succeed gate unit
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P2, the scan case. B is fiber 1 and C fiber 2. -/
def p2With (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let _ ← ops.take q (nat 1)
  let _ ← ops.take q (nat 1)
  let _ ← fork (eff do
    let _ ← ops.take q (nat 2)
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take q (nat 1)
    mark log (nat 31))
  let before ← counts q
  let answer ← ops.release q (nat 1)
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, answer, after, l]

/-- P3, the overtaking case. B is fiber 1 and C fiber 2. B writes 21 after its first take and
22 after its second. -/
def p3With (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let _ ← ops.take q (nat 2)
  let _ ← fork (eff do
    let _ ← ops.take q (nat 1)
    let _ ← mark log (nat 21)
    let _ ← ops.take q (nat 1)
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take q (nat 1)
    mark log (nat 31))
  let before ← counts q
  let _ ← ops.release q (nat 2)
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P4, two protected waiters whose bodies do not wait. A body writes its mark with the taken
count that it reads: 20 or 30, plus the count. -/
def p4With (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (ops.withPermits q (nat 2) (Deferred.await gate))
  let _ ← fork (ops.withPermits q (nat 2) (eff do
    let s ← Ref.get q
    mark log (app "add" [nat 20, field s "taken"])))
  let _ ← fork (ops.withPermits q (nat 1) (eff do
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
def p7With (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let _ ← ops.take q (nat 1)
  let b ← fork (ops.take q (nat 1))
  let whileB ← counts q
  let _ ← withFiber (Action.interrupt b)
  let afterB ← counts q
  let c ← fork (ops.withPermits q (nat 1) (succeed unit))
  let whileC ← counts q
  let _ ← withFiber (Action.interrupt c)
  let afterC ← counts q
  let answer ← ops.release q (nat 1)
  let _ ← settle
  let afterRelease ← counts q
  return tuple [whileB, afterB, whileC, afterC, answer, afterRelease]

/-- T1, the take that never waits: it takes 2 of 2, and a second request for 1 does not take
and does not enrol. -/
def t1 : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let first ← Semaphore.takeIfAvailable q (nat 2)
  let second ← Semaphore.takeIfAvailable q (nat 1)
  let after ← counts q
  return tuple [first, second, after]

/-- The five cases over one set of operations, in order. -/
def casesWith (ops : Ops) : List (Src NativeOp) :=
  [p1With ops, p2With ops, p3With ops, p4With ops, p7With ops]

def p1 : Src NativeOp := p1With library
def p2 : Src NativeOp := p2With library
def p3 : Src NativeOp := p3With library
def p4 : Src NativeOp := p4With library
def p7 : Src NativeOp := p7With library

/-- A count as a value. -/
def count (taken : Nat) (needs stamps : List Nat) : Val :=
  .list [.nat taken, .nat needs.length, .list (needs.map .nat), .list (stamps.map .nat)]

def marks (ks : List Nat) : Val := .list (ks.map .nat)

/-! ## Three more scenarios: the forms that never wait, the README's example, the masked caller

Their guards are in `Test/Program/SemaphoreOps.lean` and `Test/Program/SemaphoreTraces.lean`.
They stand here because the truth lane runs each on the pinned Effect
(`tools/Drivers/Truth.lean`), and that lane reads its scenarios from this one battery. -/

/-- **The forms that never wait**, over a form of `withPermitsIfAvailable`. A total of 2. A
protected body runs with both permits, and it writes the taken count that it reads. The root
then takes 1. A second protected form asks for 2: one permit is free, so the step does not take.
Its body would write the mark 99. Two takes of 1 follow, each one step. The answer: the first
form's answer, the counts after it, the second form's answer, the two takes' answers, the
counts at the end, and the marks. -/
def ifAvailableWith (form : TermSrc → TermSrc → Src NativeOp → Src NativeOp) : Src NativeOp :=
  eff do
    let q ← Semaphore.make 2
    let log ← Ref.make noNumbers
    let a ← form q (nat 2) (eff do
      let s ← Ref.get q
      let _ ← mark log (field s "taken")
      return nat 7)
    let between ← counts q
    let _ ← Semaphore.take q (nat 1)
    let b ← form q (nat 2) (eff do
      let _ ← mark log (nat 99)
      return nat 8)
    let c ← Semaphore.takeIfAvailable q (nat 1)
    let d ← Semaphore.takeIfAvailable q (nat 1)
    let after ← counts q
    let l ← Ref.get log
    return tuple [a, between, b, c, d, after, l]

/-- The scenario over the library's form. -/
def ifAvailable : Src NativeOp := ifAvailableWith Semaphore.withPermitsIfAvailable

/-- **The README's example**, as the README writes it. The root takes the one permit. A worker
asks for it in the protected form, and it waits. The root releases: the walk resumes the worker,
which runs its body and releases. The answer: the free count that the release answers, and the
worker's answer. -/
def handoff : Src NativeOp := eff do
  let gate ← Semaphore.make 1
  let _ ← Semaphore.take gate (nat 1)
  let worker ← fork (Semaphore.withPermits gate (nat 1) (succeed (nat 7)))
  let free ← Semaphore.release gate (nat 1)
  let x ← join worker
  return tuple [free, x]

/-- **The protected permit under a masked caller**, over one set of operations. The root holds
the one permit. A child asks for it in the protected form, under `uninterruptible`: it waits. A
second child requests its interruption. The root releases. The body writes 10 plus the taken
count that it reads. The answer: the counts after the interrupt's request, what the body wrote,
whether the child's exit is an interruption, and the counts at the end. -/
def maskedCallerWith (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let got ← Ref.make (nat 0)
  let _ ← ops.take q (nat 1)
  let f ← fork (uninterruptible (ops.withPermits q (nat 1) (eff do
    let s ← Ref.get q
    Ref.set got (app "add" [nat 10, field s "taken"]))))
  let stop ← fork (withFiber (Action.interrupt f))
  let registered ← counts q
  let _ ← ops.release q (nat 1)
  let e ← await f
  let _ ← await stop
  let x ← Ref.get got
  let after ← counts q
  return tuple [registered, x, app "causeIsInterrupt" [e], after]

/-- The masked caller over the library's operations. -/
def maskedCaller : Src NativeOp := maskedCallerWith library

/-! ## The two entries, and the joined forms of P1 and P4

`Api.run` is the fork entry: the root evaluated, then every armed dispatcher flushed, round after
round. `Api.runSync` is the sync entry: the root evaluated, then the root's own dispatcher flushed,
and no dispatcher of another fiber (`runSyncExit`, `src/Effect4/Machine/Fibers.lean`, which
transcribes `runSyncExitWith`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`).

A release posts its helper on the dispatcher of the fiber that releases. In P1 and P4 that fiber
is a child: A's hook releases. So the sync entry ends before the walk, and the root answers what
it reads between the release and the walk. Where the root releases, the two entries give one
answer.

The truth lane's exit column compared the fork run's exit with the pin's sync exit whenever the
sync run settled (`git:8e93a284f:git:9c197bb67:harness/truth/run-truth.ts`). So P1 and P4 were no programs of
that lane: on each entry the two faces give one exit, and the column was red
(`docs/research/2026-10-06-seat-semw-evidence/README.md`). The lane ran the joined forms
instead. A joined form's root joins the waiting fibers and does not yield four times. Its sync
entry cannot settle, because the helper is on a child's dispatcher, and the lane then compared
the fork entry. The lane was deleted on 2026-10-20. -/

/-- The root's exit under the sync entry, at the truth lane's fuel. -/
def syncExitOf (src : Src NativeOp) : Option ExitV :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => (Api.runSync b.program 1000).2

/-- Whether an exit is the sync entry's defect: the root has not exited when its dispatcher is
empty. -/
def notSettled : ExitV → Bool
  | .failure c => c.reasons.any fun
      | .die .asyncFiber _ => true
      | _ => false
  | _ => false

/-- P1 with a join: the root joins B and does not yield four times. -/
def p1JoinedWith (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (ops.withPermits q (nat 2) (Deferred.await gate))
  let b ← fork (eff do
    let _ ← ops.take q (nat 2)
    mark log (nat 22))
  let _ ← fork (eff do
    let _ ← ops.take q (nat 1)
    mark log (nat 31))
  let before ← counts q
  let _ ← yieldNow 0
  let _ ← Deferred.succeed gate unit
  let _ ← join b
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

/-- P4 with two joins: the root joins B and then C. -/
def p4JoinedWith (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let log ← Ref.make noNumbers
  let gate ← Deferred.make .unit .never
  let _ ← fork (ops.withPermits q (nat 2) (Deferred.await gate))
  let b ← fork (ops.withPermits q (nat 2) (eff do
    let s ← Ref.get q
    mark log (app "add" [nat 20, field s "taken"])))
  let c ← fork (ops.withPermits q (nat 1) (eff do
    let s ← Ref.get q
    mark log (app "add" [nat 30, field s "taken"])))
  let before ← counts q
  let _ ← Deferred.succeed gate unit
  let _ ← join b
  let _ ← join c
  let after ← counts q
  let l ← Ref.get log
  return tuple [before, after, l]

def p1Joined : Src NativeOp := p1JoinedWith library
def p4Joined : Src NativeOp := p4JoinedWith library

/-! ## The engine's fixture

The three runs that cross to the generated engine (`ocaml/engine/test/semaphore/`): P1, P3 and
P9, the cases that row 259's reading rests on. P9 is P1's program under its own tape, and the
fixture holds that tape as data: one line of decisions. A run with no tape is the engine's own
drive loop, which is the ordinary tape. The writer beside the engine's test writes
`fixtureText`, and `Test/Program/SemaphoreEngine.lean` binds the committed file to it. -/

/-- The fixture's fuel: the fuel of every run above. -/
def fuel : Nat := 20000

/-- One run of the engine's fixture: its name, its source and its tape. An empty tape stands for
the engine's own drive loop: the root evaluated, and then one flush. -/
structure EngineRun where
  name : String
  src : Src NativeOp
  tape : List Api.Decision := []

/-- The decisions that a run replays: its tape, or the ordinary tape. -/
def EngineRun.decisions (r : EngineRun) : List Api.Decision :=
  if r.tape.isEmpty then plain else r.tape

/-- The runs of the engine's fixture, in the fixture's order. -/
def engineRuns : List EngineRun :=
  [{ name := "p1", src := p1 }, { name := "p3", src := p3 },
   { name := "p9", src := p1, tape := yieldAtResume }]

/-- A value's spelling as the engine's `show_val` writes it (`ocaml/engine/e4_engine.ml`), as an
algebra of the value fold: a Boolean, a number, and a list of such values at any depth. Every
other value has no spelling here, and the writer refuses it. -/
def showAlgebra : Store.ValAlgebra (fun _ => Option String) where
  val_unit := none
  val_bool b := some (toString b)
  val_nat n := some (toString n)
  val_str _ := none
  val_bytes _ := none
  val_list items := (items.mapM id).map fun parts => "list[" ++ ",".intercalate parts ++ "]"
  val_pair _ _ := none
  val_none := none
  val_some _ := none
  val_ctor _ _ := none
  val_ref _ _ := none
  val_handle _ _ := none
  val_negInt _ := none
  val_float _ := none

def showVal (v : Val) : Option String := Store.cata_val showAlgebra v

/-- An exit in the spelling of the engine's `show_exit`. Only a success has a spelling here. -/
def showExit : ExitV → Option String
  | .success v => (showVal v).map ("success " ++ ·)
  | .failure _ => none

/-- A decision's word in the fixture. The three kinds of the fixture's tapes have a word: the
engine's test reads each back (`test_semaphore.ml`). Every other decision has no word here, and
the writer refuses it. -/
def decisionWord : Api.Decision → Option String
  | .evaluate fiber => some s!"evaluate:{fiber.value}"
  | .flush => some "flush"
  | .yieldVerdict fiber verdict => some s!"yieldVerdict:{fiber.value}:{verdict}"
  | _ => none

/-- A tape's line in the fixture: no line for the empty tape, and one line of words otherwise.
`none` when a decision has no word. -/
def tapeLine (tape : List Api.Decision) : Option String :=
  if tape.isEmpty then some ""
  else (tape.mapM decisionWord).map fun words => "tape " ++ " ".intercalate words ++ "\n"

/-- The program that the build admits. -/
def buildOf (src : Src NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build (mk src)).toOption.map (·.program)

/-- The root's exit of a run of the fixture at a fuel: the raw replay of its decisions. -/
def EngineRun.exitAt (r : EngineRun) (fuel : Nat) : Option ExitV :=
  (buildOf r.src).bind fun p => (Api.replay p fuel r.decisions).exit

/-- One run of the fixture: its name, its fuel, its tape when it has one, its program's bytes
and its exit. -/
def runText (r : EngineRun) : Option String := do
  let program ← buildOf r.src
  let exit ← r.exitAt fuel
  let shown ← showExit exit
  let tape ← tapeLine r.tape
  pure s!"run {r.name}\nfuel {fuel}\n{tape}program {Wire.hexOf program}\nexit {shown}\nend\n"

def fixtureHeader : String :=
  "# GENERATED by ocaml/engine/test/semaphore/write.lean; do not edit.\n" ++
  "# Write again: lake env lean --run ocaml/engine/test/semaphore/write.lean\n"

/-- The fixture's whole text. `none` when a run does not build, does not finish, answers a value
with no spelling, or holds a decision with no word. -/
def fixtureText : Option String :=
  (engineRuns.mapM runText).map fun runs => fixtureHeader ++ String.join runs

end Test.Program.SemaphoreScenarios
