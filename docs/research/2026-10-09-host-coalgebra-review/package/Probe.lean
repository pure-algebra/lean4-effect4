import EffectsTest.Coalgebra.CoalgebraContract

set_option autoImplicit false

namespace HostCoalgebraReview
open Effects EffectsTest.Coalgebra

-- CO-4 negative control: a simulation places no demand at a source cut.
def stopped : System Ask Nat Unit := fun _ => none

def Related : Unit → Program Ask Nat → Prop := fun _ _ => True

-- This witness is a control for the proposed H8 consumer, not a new library law.
theorem stopped_sim : IsSim stopped Program.system Related := by
  intro x y h step hstep
  change (none : Option (Step Ask Nat Unit)) = some step at hstep
  cases hstep

example : IsSim stopped Program.system Related := stopped_sim
#guard stopped.run counter 4 () 5 == some (none, 5)
#guard counter.run askTwice 5 == some (11, 7)
#guard Program.system.run counter 4 askTwice 5 == some (some 11, 7)

-- CO-5 positive reader: the completed-run theorem applies to the real finite machine.
example : counter.run askTwice 5 = some (11, 7) :=
  Program.run_of_sim_program machine_sim (EffectsTest.Coalgebra.Related.start 0) counter
    (by decide : machine.run counter 4 (2, 0) 5 = some (some 11, 7))

#eval stopped.run counter 4 () 5
#eval counter.run askTwice 5

end HostCoalgebraReview
