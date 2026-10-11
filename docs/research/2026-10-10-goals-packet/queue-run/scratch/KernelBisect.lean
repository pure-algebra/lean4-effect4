import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: where the elaboration of a symbolic literal gets stuck. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open Effect4.Modules

namespace KBProbe

def rows : List RowDef := [Test.Dogfood.P3WorkerQueue.take, Test.Dogfood.P3WorkerQueue.runJob]

/-- A literal answered inside a loop. -/
def loop1 (total : Nat) : Module NativeOp :=
  { rows := rows
    main := iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } }

example (total : Nat) : (Program.Authoring.elaborateModule (loop1 total)).toOption.isSome = true := by
  rfl

/-- A literal answered inside a loop, with no rows. -/
def loop0 (total : Nat) : Module NativeOp :=
  { main := iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => succeed (nat total)
          step := fun c _ => c } }

example (total : Nat) : (Program.Authoring.elaborateModule (loop0 total)).toOption.isSome = true := by
  rfl

/-- The raw lift, with no minted names. -/
def loopRaw (total : Nat) : Module NativeOp :=
  { main := iterate "c" "a" none (bool true) (bool true) (var "c") (var "c") (succeed (nat total)) }

example (total : Nat) : (Program.Authoring.elaborateModule (loopRaw total)).toOption.isSome = true := by
  rfl

/-- The elaborated tree of the raw lift, at the empty environment. -/
example (total : Nat) :
    (iterate (Op := NativeOp) "c" "a" none (bool true) (bool true) (var "c") (var "c")
      (succeed (nat total)) {} []).toOption.isSome = true := by
  rfl

end KBProbe
