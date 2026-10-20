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

P1, P3 and P9 cross to the generated engine, and their exits are pinned there
(`ocaml/engine/test/semaphore/`, bound by `Test/Program/SemaphoreEngine.lean`). This battery pins
the other cases, P1 and P4 under the sync entry, and the joined forms.

Placement. Each scenario is a finite control of the proposed claim `semaphore-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. The cases P1, P3 and P9 are the finite controls of row 259's reading of the machine
(concept `reactive-scheduling`, requirement R12). Every guard is one run on one schedule. None
proves delivery, a cancellation law, a law of the wake across visits or liveness, and none is a
host run: the host runs are the truth lane's (`tools/Drivers/Truth.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Semaphore (takeStep takeIfAvailableStep releaseStep visitStep withdrawStep visitFrom
  eligibleT)

/-! ## The cases that no engine fixture pins -/

-- P2's types: the counts, the release's answer, the counts and the marks, and no failure.
#guard typesOf p2 =
  some (.tuple [.tuple [.nat, .nat, .list .nat, .list .nat], .nat,
    .tuple [.nat, .nat, .list .nat, .list .nat], .list .nat], .never)
-- P2. The release answered 1. The walk passed B and resumed C, which took 1. B's entry stays
-- in its place: the stamp 0.
#guard exitOf p2 = some (.success (.list
  [count 2 [2, 1] [0, 1], .nat 1, count 2 [2] [0], marks [31]]))
-- P4. B's body saw 2 taken, then C's body saw 1. Nothing stays taken, and nobody waits.
#guard exitOf p4 = some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [] [], marks [22, 31]]))
-- P7. Each interrupted waiter's entry leaves, and `taken` stays 1. The release then answers 1
-- free and posts no helper.
#guard exitOf p7 = some (.success (.list
  [count 1 [1] [0], count 1 [] [], count 1 [1] [1], count 1 [] [], .nat 1, count 0 [] []]))
-- T1. The take that never waits answers true, then false, and nobody is enrolled.
#guard exitOf t1 = some (.success (.list [.bool true, .bool false, count 2 [] []]))

/-! ## The sync entry and the joined forms -/

-- P1 and P4 under the sync entry: the release is in the cell, both waiters still wait, and no
-- mark is written.
#guard [p1, p4].map syncExitOf = List.replicate 2 (some (.success (.list
  [count 2 [2, 1] [0, 1], count 0 [2, 1] [0, 1], marks []])))
-- Each joined form gives its case's answer on the fork entry.
#guard exitOf p1Joined == exitOf p1 && exitOf p4Joined == exitOf p4
-- P9's tape on the joined P1: B waits again, so the join does not return, and the run is a
-- frontier with no exit.
#guard exitOn yieldAtResume p1Joined = none

end Test.Program.SemaphoreScenarios
