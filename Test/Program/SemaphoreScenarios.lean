import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Modules.Semaphore.Ops
import Effect4.Store.Carrier.Fold
import Effect4.Store.Domain.ProgramWire

/-!
# Semaphore's operations on the machine: the host probe's cases (rows 259 to 261, 265 and 276)

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

**The operations are the library's** (`src/Effect4/Modules/Semaphore/Ops.lean`).
`Semaphore.make`, `take`, `release`, `withPermits` and `takeIfAvailable` wrap the step terms with
the shared wrapper (`src/Effect4/Modules/Waiting.lean`): the mask that restores, one posted
helper for a release, and a withdrawal on interruption. Every binder of an operation is minted.
One more run, T1, is the take that never waits.

**The fixtures of the earlier slice stay here as written forms** (the namespace `Written`), as
that slice wrote them. Each writes its binders by name. `uninterruptible` stands for the mask
and `interruptible` for its restore, which is right under an interruptible caller only. They
give the library's answer on each case, and each program over them is another tree. They are the
red controls of the hygiene controls (`Test/Program/SemaphoreOps.lean`).

**A changed policy is a variant of Semaphore's part** (`Policy`): another visit, a retry that
takes with no second check, or a walk that grants. The policy with no change is the library's
operation, tree for tree.

**The settings of every run.**

- The tape is `[evaluate root, flush]`. P9's tape holds one more decision between the two:
  `yieldVerdict` for fiber 2, which is B.
- The fuel is 20000, and the compile fuel is 20000.
- The budget of operations before a yield is the default, 2048 for each fiber. No run but P9
  holds an injected yield.
- A child is forked with the default options: it starts at once. The helper is posted: a
  detached fork with a deferred start, uninterruptible.
- The root yields four times after it releases, and then it reads the cell. The joined forms of
  P1 and P4 join the waiting fibers instead: they are the truth lane's programs of those two
  cases (the section on the two entries).

A count is `[taken, the number of waiters, their counts, their stamps]`. A stamp tells one
enrolment from another: a waiter that waits again has a new stamp.

Placement. Each scenario is a finite control of the proposed claim `semaphore-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. The cases P1, P3 and P9 are the finite controls of row 259's reading of the machine
(concept `reactive-scheduling`, requirement R12). Every guard is one run on one schedule. None
proves delivery, a cancellation law, a law of the wake across visits or liveness, and none is a
host run: the host runs are the truth lane's (`harness/truth/Truth.lean`).
-/

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

-- The policy with no change is the library's operation, tree for tree, at a caller's scope.
#guard treeAt ["q", "n"] ((opsOf {}).take (var "q") (var "n")) ==
  treeAt ["q", "n"] (Semaphore.take (var "q") (var "n"))
#guard treeAt ["q", "n"] ((opsOf {}).release (var "q") (var "n")) ==
  treeAt ["q", "n"] (Semaphore.release (var "q") (var "n"))
#guard treeAt ["q", "n"] ((opsOf {}).withPermits (var "q") (var "n") (succeed (nat 1))) ==
  treeAt ["q", "n"] (Semaphore.withPermits (var "q") (var "n") (succeed (nat 1)))
#guard (treeAt ["q", "n"] (Semaphore.take (var "q") (var "n"))).isSome &&
  (treeAt ["q", "n"] (Semaphore.release (var "q") (var "n"))).isSome &&
  (treeAt ["q", "n"] (Semaphore.withPermits (var "q") (var "n") (succeed (nat 1)))).isSome
-- The walk over the library's visit is the library's walk.
#guard treeAt ["q"] (walkOver visitStep (var "q")) == treeAt ["q"] (Semaphore.walk (var "q"))
-- Red control of the comparison: a changed policy is another tree.
#guard treeAt ["q", "n"] ((opsOf { helper := walkOver (fun _ s => visitStep (nat 0) s) }).release
    (var "q") (var "n")) != treeAt ["q", "n"] (Semaphore.release (var "q") (var "n"))

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

-- Each scenario builds over the library's operations: the checker types every step inside its
-- `Ref.modify`, and the mask's saved state at each restore site.
#guard [p1, p2, p3, p4, p7].map verdict = List.replicate 5 "built"
-- P2's types: the counts, the release's answer, the counts and the marks, and no failure.
#guard typesOf p2 =
  some (.tuple [.tuple [.nat, .nat, .list .nat, .list .nat], .nat,
    .tuple [.nat, .nat, .list .nat, .list .nat], .list .nat], .never)

/-! ### The pin's answers, on the machine -/

-- P1. B took 2 inside the walk. The next visit read no free permit and stopped. C still waits,
-- with its first entry: the stamp 1.
#guard exitOf p1 = some (.success (.list
  [count 2 [2, 1] [0, 1], count 2 [1] [1], marks [22]]))
-- P2. The release answered 1. The walk passed B and resumed C, which took 1. B's entry stays
-- in its place: the stamp 0.
#guard exitOf p2 = some (.success (.list
  [count 2 [2, 1] [0, 1], .nat 1, count 2 [2] [0], marks [31]]))
-- P3. B took 1 and took 1 again, inside the walk. C waits with its first entry.
#guard exitOf p3 = some (.success (.list
  [count 2 [1, 1] [0, 1], count 2 [1] [1], marks [21, 22]]))
-- P4. B's body saw 2 taken, then C's body saw 1. Nothing stays taken, and nobody waits.
#guard exitOf p4 = some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [] [], marks [22, 31]]))
-- P7. Each interrupted waiter's entry leaves, and `taken` stays 1. The release then answers 1
-- free and posts no helper.
#guard exitOf p7 = some (.success (.list
  [count 1 [1] [0], count 1 [] [], count 1 [1] [1], count 1 [] [], .nat 1, count 0 [] []]))
-- P9. B yielded at its resume. The walk went on and resumed C, which took 1. B then found 1
-- free, and it waits again with a new entry: the stamp 2.
#guard exitOn yieldAtResume p1 = some (.success (.list
  [count 2 [2, 1] [0, 1], count 1 [2] [2], marks [31]]))

-- T1. The take that never waits answers true, then false, and nobody is enrolled.
#guard verdict t1 = "built" &&
  exitOf t1 = some (.success (.list [.bool true, .bool false, count 2 [] []]))

-- The ordinary run gives each answer too, at the truth lane's fuel: the root evaluated, then
-- one flush. So no case needs a flush of its own.
#guard (t1 :: casesWith library).all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src
-- Red control of the fuel: at a fuel of 5 no case has an exit.
#guard (t1 :: casesWith library).all fun src => (exitAt 5 src).isNone

/-! ### The reading of the machine, on the trace

A waiter that a visit resumes runs inside the helper's task: it exits before the helper
does. -/

-- P1. The exits, in order: A, then B, then the helper (fiber 4), then C at the root's end.
#guard exitsOn plain p1 = some [1, 2, 4, 3, 0]
-- P3. B (fiber 1) exits before the helper (fiber 3).
#guard exitsOn plain p3 = some [1, 3, 2, 0]
-- P4. B and C both run to their exits inside the first helper (fiber 4). B's own release
-- posts a second helper (fiber 5), which finds nobody.
#guard exitsOn plain p4 = some [1, 2, 3, 4, 5, 0]
-- P9. C exits inside the walk, the helper next, and B only at the root's end.
#guard exitsOn yieldAtResume p1 = some [1, 3, 4, 2, 0]
-- P9's one injected yield is B's, at its first operation after the resume. No other run
-- holds an injected yield: the budget of 2048 operations is not reached.
#guard yieldsOn yieldAtResume p1 = some [(2, 1)]
#guard [p1, p2, p3, p4, p7].map (yieldsOn plain) = List.replicate 5 (some [])
-- The settings: each fiber's budget of operations before a yield, at the end of P1.
#guard ((runOn plain p1).map fun r => r.machine.fibers.map (·.maxOpsBeforeYield)) =
  some (List.replicate 5 2048)
-- Before P9's verdict, the four fibers are parked and none has exited: B's next check is its
-- resume.
#guard ((runOn [Api.evaluate] p1).map fun r =>
    r.machine.fibers.map fun f => (f.id.value, decide (f.parked = .notParked), f.exit.isSome)) =
  some [(0, false, false), (1, false, false), (2, false, false), (3, false, false)]
-- Each run finishes, and each row of each tape is played: no decision is refused.
#guard ([p1, p2, p3, p4, p7].map fun src =>
    (runOn plain src).map fun r => (decide (r.inspect.outcome = .finished), r.phases)) =
  List.replicate 5 (some (true, [.progressed, .progressed]))
#guard ((runOn yieldAtResume p1).map fun r =>
    (decide (r.inspect.outcome = .finished), r.phases)) =
  some (true, [.progressed, .progressed, .progressed])
-- One flush is every flush: two more change nothing.
#guard exitOn [Api.evaluate, Api.flush, Api.flush, Api.flush] p1 = exitOf p1

/-! ### The red controls: each changed policy fails its own case

Each changed policy builds, so typing does not catch it. -/

#guard [p2With headOnly, p3With grant, p1With noSecondCheck].map verdict =
  List.replicate 3 "built"

-- A walk that wakes the head alone fails P2: B does not fit, so C never proceeds. One permit
-- stays free while C waits.
#guard exitOf (p2With headOnly) = some (.success (.list
  [count 2 [2, 1] [0, 1], .nat 1, count 1 [2, 1] [0, 1], marks []]))
#guard exitOf (p2With headOnly) != exitOf p2
-- The head-only walk still gives P1's answer: P2 is the case that tells the two apart.
#guard exitOf (p1With headOnly) = exitOf p1

-- A walk that commits for every fitting waiter before any of them runs fails P3: C holds a
-- permit, and B's second request waits (a new entry, the stamp 2).
#guard exitOf (p3With grant) = some (.success (.list
  [count 2 [1, 1] [0, 1], count 2 [1] [2], marks [21, 31]]))
#guard exitOf (p3With grant) != exitOf p3

-- A retry with no second check fails the accounting on P9: C takes 1 while B has yielded, and
-- B then takes 2. Three permits of two are taken.
#guard exitOn yieldAtResume (p1With noSecondCheck) = some (.success (.list
  [count 2 [2, 1] [0, 1], count 3 [] [], marks [31, 22]]))
-- With no yield the same retry gives P1's answer: P9's path is the one that shows the fault.
#guard exitOf (p1With noSecondCheck) = exitOf p1

/-! ## The trees: the library's programs against the written forms

A tree holds no name: a binder is a level. The library's operations are other trees than the
earlier fixture's, in five places:

- the mask that restores stands where the fixture wrote `uninterruptible` and `interruptible`;
- `take` is the shared wrapper: its loop's cursor is an option of the result, with a defect on
  the arm that never runs, and it answers the count;
- `release` runs under `uninterruptible`, and the walk's cursor states no type;
- the protected form is one `protectedBy`, whose hook is the release itself;
- a withdrawal is its row alone.

So each case's program has other bytes over the written forms, and it gives the same answer. -/

-- Each case over the written forms builds, and it gives the library's answer: on these
-- schedules no caller is masked, so the stand-ins are right.
#guard (casesWith Written.ops).map verdict = List.replicate 5 "built"
#guard (casesWith Written.ops).map exitOf == (casesWith library).map exitOf
#guard exitOn yieldAtResume (p1With Written.ops) == exitOn yieldAtResume p1
-- Each is another tree, and the five programs of each kind are five byte strings.
#guard (List.zip (casesWith library) (casesWith Written.ops)).all fun pair =>
  bytesOf pair.1 != bytesOf pair.2
#guard ((casesWith library).map bytesOf).all Option.isSome &&
  ((casesWith library).map bytesOf).eraseDups.length = 5
-- The construction is one `Ref.make` of the initial value: the fixtures' tree.
#guard elaborate (Semaphore.make 2) ==
  elaborate (Ref.make (Semaphore.empty 2) : Src NativeOp)

/-! ## Three more scenarios: the forms that never wait, the README's example, the masked caller

Their guards are in `Test/Program/SemaphoreOps.lean` and `Test/Program/SemaphoreTraces.lean`.
They stand here because the truth lane runs each on the pinned Effect
(`harness/truth/Truth.lean`), and that lane reads its scenarios from this one battery. -/

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

The truth lane's exit column compares the fork run's exit with the pin's sync exit whenever the
sync run settles (`harness/truth/run-truth.ts`). So P1 and P4 are no programs of that lane: on
each entry the two faces give one exit, and the column is red
(`docs/research/2026-10-06-seat-semw-evidence/README.md`). The lane runs the joined forms
instead. A joined form's root joins the waiting fibers and does not yield four times. Its sync
entry cannot settle, because the helper is on a child's dispatcher, and the lane then compares
the fork entry. -/

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

-- P1 and P4 under the sync entry: the release is in the cell, both waiters still wait, and no
-- mark is written. The sync entry settles, on another exit than the fork entry's.
#guard [p1, p4].map syncExitOf = List.replicate 2 (some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [2, 1] [0, 1], marks []])))
#guard [p1, p4].all fun src =>
  !(syncExitOf src).any notSettled && syncExitOf src != exitAt 1000 src
-- Where the root releases, and where nobody waits, the two entries give one exit.
#guard [p2, p3, p7, t1, ifAvailable, handoff, maskedCaller].all fun src =>
  (syncExitOf src).isSome && syncExitOf src == exitAt 1000 src

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

-- Each joined form builds, at its case's types, and it is another tree than its case.
#guard [p1Joined, p4Joined].map verdict = ["built", "built"]
#guard [p1Joined, p4Joined].map typesOf == [p1, p4].map typesOf
#guard (bytesOf p1Joined).isSome && (bytesOf p4Joined).isSome &&
  bytesOf p1Joined != bytesOf p1 && bytesOf p4Joined != bytesOf p4 &&
  bytesOf p1Joined != bytesOf p4Joined
-- Each gives its case's answer on the fork entry: on the checked session, and at the truth
-- lane's fuel.
#guard exitOf p1Joined = some (.success (.list
  [count 2 [2, 1] [0, 1], count 2 [1] [1], marks [22]]))
#guard exitOf p4Joined = some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [] [], marks [22, 31]]))
#guard exitOf p1Joined == exitOf p1 && exitOf p4Joined == exitOf p4
#guard [p1Joined, p4Joined].all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src
-- Red control of the fuel: at a fuel of 5 neither has an exit.
#guard [p1Joined, p4Joined].all fun src => (exitAt 5 src).isNone
-- The sync entry does not settle either: the root waits in its join, and the helper is on A's
-- dispatcher.
#guard [p1Joined, p4Joined].all fun src => (syncExitOf src).any notSettled
-- Red control of that reading: the README's example joins too, and its root releases. Its sync
-- entry settles.
#guard (syncExitOf handoff).any (!notSettled ·)
-- A join returns inside the helper's task: the root exits before the helper does. In the joined
-- P4, B's own release posts a second helper (fiber 5), which runs after the root's exit.
#guard exitsOn plain p1Joined = some [1, 2, 3, 0, 4]
#guard exitsOn plain p4Joined = some [1, 2, 3, 0, 4, 5]
-- The written forms give the same two answers.
#guard [p1JoinedWith Written.ops, p4JoinedWith Written.ops].map exitOf ==
  [exitOf p1Joined, exitOf p4Joined]
-- P9's tape on the joined P1. B yields at its resume, C takes, and B waits again. So the join
-- does not return: the run is a frontier, with the root and B parked and no exit of either. The
-- case P9 keeps the form that yields.
#guard exitOn yieldAtResume p1Joined = none
#guard exitsOn yieldAtResume p1Joined = some [1, 3, 4]
#guard ((runOn yieldAtResume p1Joined).map fun r =>
    (decide (r.inspect.outcome = .frontier), r.machine.fibers.map fun f =>
      (f.id.value, decide (f.parked = .notParked), f.exit.isSome))) =
  some (true, [(0, false, false), (1, true, true), (2, false, false), (3, true, true),
    (4, true, true)])

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

-- Every run has a text. The raw replay that the fixture records gives the checked session's
-- exit on the same decisions.
#guard fixtureText.isSome
#guard engineRuns.all fun r => r.exitAt fuel == some (exitOn r.decisions r.src)
-- A run with no tape is the ordinary run, `Api.run`: the engine's own drive loop.
#guard (engineRuns.filter (·.tape.isEmpty)).all fun r =>
  r.exitAt fuel == (buildOf r.src).map fun p => (Api.run p fuel).exit
-- No run finishes at the engine test's small fuel, and none has an exit there.
#guard engineRuns.all fun r => (buildOf r.src).any fun p =>
  (Api.replay p 3 r.decisions).outcome != .finished && (r.exitAt 3).isNone
-- P9's tape as the fixture writes it, and the two runs without a tape.
#guard engineRuns.map (fun r => tapeLine r.tape) =
  [some "", some "", some "tape evaluate:0 yieldVerdict:2:true flush\n"]
-- Red control of the words: a decision of another kind has no word, and its tape has no line.
#guard decisionWord (.fire ⟨1⟩) = none && tapeLine [Api.evaluate, .fire ⟨1⟩] = none
-- Red controls of P9's one decision, as the engine's test runs them. With the verdict false,
-- and with no verdict at all, P1's program gives P1's exit and not P9's.
#guard exitOn [Api.evaluate, .yieldVerdict ⟨2⟩ false, Api.flush] p1 = exitOf p1
#guard exitOn yieldAtResume p1 != exitOf p1

end Test.Program.SemaphoreScenarios
