import Effect4.Laws.Modules.Latch.Steps

/-! The battery of the Latch's steps (decisions row 330, slice L3): rc.112's batching on the
model, a reader of the agreement at a state, and the controls of an open latch and an empty
flush. -/

set_option autoImplicit false

open Effect4.Program Effect4.Program.Authoring Effect4.Latch.Model Effect4.Modules Effect4.Machine

namespace Test.Program.LatchSteps

/-- Two waiters before the first release. -/
def s0 : State := { isOpen := false, waiters := [1, 2] }

-- rc.112's batching (`scheduleUnsafe`, `flushScheduled`): the first release schedules one flush
-- with [1, 2]; a waiter that enrols before the flush joins that batch at the next release,
-- which posts nothing; the flush resumes [1, 2, 9] in order (probe MODS-10).
#guard (wake false s0).2 == (true, true)

def s1 : State := { (wake false s0).1 with waiters := [9] }

#guard (wake false s1).2 == (true, false)
#guard (flush (wake false s1).1).2 == [1, 2, 9]
#guard (flush (flush (wake false s1).1).1).2 == []

-- Control: an open latch answers false and posts nothing; `open` on a closed latch opens it.
#guard (wake true { isOpen := true, waiters := [1] }).2 == (false, false)
#guard (wake true s0).1.isOpen && !(wake false s0).1.isOpen

-- Control: `close` answers whether it closed.
#guard (close { isOpen := true }).2 && !(close { isOpen := false }).2

-- Reader: the wake's term reads the model's reply and next state, at every scope.
example (tb : Effect4.Modules.Table) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (readsCell : Reads cellSrc env path vals (cellVal tb s0)) :
    Reads (Effect4.Latch.wakeStep false cellSrc) env path vals
      (Val.tuple [Val.tuple [.bool true, .bool true], cellVal tb (wake false s0).1]) :=
  wakeStep_agrees tb s0 readsCell false

end Test.Program.LatchSteps
