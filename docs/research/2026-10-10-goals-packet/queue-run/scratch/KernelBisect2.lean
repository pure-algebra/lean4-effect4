import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: the minted loop at a fixed literal, and its pieces with a symbolic one. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

namespace KBProbe2

def loop0 (total : Nat) : Module NativeOp :=
  { main := iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } }

/-- A fixed literal. -/
example : (Program.Authoring.elaborateModule (loop0 3)).toOption.isSome = true := by
  rfl

/-- The minted lift alone, at the empty environment, with a symbolic literal. -/
example (total : Nat) :
    (iterateWith (Op := NativeOp) (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } {} []).toOption.isSome = true := by
  rfl

/-- The minted lift with a step that reads no minted name. -/
example (total : Nat) :
    (iterateWith (Op := NativeOp) (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun _ _ => bool true } {} []).toOption.isSome = true := by
  rfl

/-- `decide +kernel` on the closed fixed-literal module. -/
example : (Program.Authoring.elaborateModule (loop0 3)).toOption.isSome = true := by
  decide +kernel

end KBProbe2
