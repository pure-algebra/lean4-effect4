import Test.Program.SemaphoreScenariosData
import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Library.Semaphore.Ops
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

**The operations are the library's** (`src/Effect4/Library/Semaphore/Ops.lean`).
`Semaphore.make`, `take`, `release`, `withPermits` and `takeIfAvailable` wrap the step terms with
the shared wrapper (`src/Effect4/Library/Waiting.lean`): the mask that restores, one posted
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

/-! ## The written forms: the fixtures of the earlier slice

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder. So a
caller's variable named `s` would read the cell's value there, and the same holds of `id`,
`hint`, `took`, `r`, `w` and `e` at their binders. The texts are the earlier slice's
(`git:59241284:Test/Program/SemaphoreScenarios.lean`), with the count before the handle. -/

namespace Written

end Written

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

-- P1 and P4 under the sync entry: the release is in the cell, both waiters still wait, and no
-- mark is written. The sync entry settles, on another exit than the fork entry's.
#guard [p1, p4].map syncExitOf = List.replicate 2 (some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [2, 1] [0, 1], marks []])))
#guard [p1, p4].all fun src =>
  !(syncExitOf src).any notSettled && syncExitOf src != exitAt 1000 src
-- Where the root releases, and where nobody waits, the two entries give one exit.
#guard [p2, p3, p7, t1, ifAvailable, handoff, maskedCaller].all fun src =>
  (syncExitOf src).isSome && syncExitOf src == exitAt 1000 src

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
