import Effect4.Api.TestClock
import Effect4.Program.Authoring.Sugar

/-!
# Test clock contract — the tape is the clock; the warps are folds

`Api.TestClock` (`src/Effect4/Api/TestClock.lean`). A raw run parks at the first sleep; the
same program under a tape that adjusts once per sleep finishes with the clock at the sum
of the sleeps; `synthesize` writes that tape from the tree; `fastForward` finishes without
a clock at time zero; `dilateTime k` needs the scaled tape and lands at `k` times the sum;
both warps fix a sleep-free program. The programs are written by name with the generated
row wrappers and pinned against the trees written by level.
-/

set_option autoImplicit false

namespace Test.Api.TestClockContract

open Effect4 Effect4.Program Effect4.Api Effect4.Api.TestClock
open Effect4.Program.Authoring

/-- Sleep 100, sleep 50, read the clock. -/
def twoSleeps : Api.Program :=
  .bind (.perform .sleep (.lit (.nat 100)))
    (.bind (.perform .sleep (.lit (.nat 50))) (.perform .clockNow (.lit .unit)))

def twoSleepsByName : Src NativeOp :=
  andThen (Effect.sleep (nat 100)) <| andThen (Effect.sleep (nat 50)) <| Effect.currentTimeMillis

#guard elaborate twoSleepsByName = .ok twoSleeps
#guard Api.wellTyped twoSleeps

/-! ## The tape is the clock -/

#guard sleepDeadlines twoSleeps = [100, 50]
#guard (Api.run twoSleeps 100).outcome = .frontier
#guard (TestClock.run twoSleeps 100 [100, 50]).exit = some (.success (.nat 150))
#guard (Api.replay twoSleeps 100 (synthesize twoSleeps)).exit = some (.success (.nat 150))
-- One adjustment short: the second sleep is still pending.
#guard (TestClock.run twoSleeps 100 [100]).outcome = .frontier
-- One large adjustment fires both sleeps in deadline order: the sleeper reads the clock at
-- its own deadline (`TestClock.run`'s loop stages the clock at each fire), and the clock
-- ends at the adjustment's end once nothing is due.
#guard (TestClock.run twoSleeps 100 [1000]).exit = some (.success (.nat 150))
#guard (TestClock.run twoSleeps 100 [1000]).stores.timers.now = 1000

/-! ## The warps -/

#guard (Api.run (fastForward twoSleeps) 100).exit = some (.success (.nat 0))
#guard Api.wellTyped (fastForward twoSleeps)
#guard sleepDeadlines (fastForward twoSleeps) = []

#guard sleepDeadlines (dilateTime 2 twoSleeps) = [200, 100]
#guard (Api.replay (dilateTime 2 twoSleeps) 100 (synthesize (dilateTime 2 twoSleeps))).exit
  = some (.success (.nat 300))
-- The undilated tape is too short for the dilated program.
#guard (TestClock.run (dilateTime 2 twoSleeps) 100 [100, 50]).outcome = .frontier
#guard Api.wellTyped (dilateTime 2 twoSleeps)

/-- A sleep-free program is a fixed point of both warps: the identity fold. -/
def noSleep : Api.Program := .bind (.perform .refMake (.lit (.nat 1))) (.perform .refGet (.var 0))

#guard fastForward noSleep = noSleep
#guard dilateTime 7 noSleep = noSleep

-- The tree of a sleep is what the row wrapper says it is.
#guard elaborate (Effect.sleep (nat 5) : Src NativeOp) = .ok (.perform .sleep (.lit (.nat 5)))

#print axioms Effect4.Api.TestClock.fastForward
#print axioms Effect4.Api.TestClock.sleepDeadlines

end Test.Api.TestClockContract
