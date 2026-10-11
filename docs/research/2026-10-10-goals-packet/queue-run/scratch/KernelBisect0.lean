import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: the bisection's first steps. Each `example` states that a module's elaboration
succeeds at a symbolic literal, by `rfl`. The expected outcome of each is in its docstring; a
failing one reports an error, which `scratch/kernelbisect0.out` records. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open Effect4.Modules

namespace KBProbe0

def rows : List RowDef := [Test.Dogfood.P3WorkerQueue.take, Test.Dogfood.P3WorkerQueue.runJob]

/-- The gate's test on a counted cell. Expected: reduces. -/
def gateModule (total : Nat) : Module NativeOp :=
  { rows := rows
    main := eff do
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
      ifElse (app "eq" [n, nat total]) (Deferred.succeed gate (nat 0)) (succeed (bool false)) }

example (total : Nat) :
    (Program.Authoring.elaborateModule (gateModule total)).toOption.isSome = true := by
  rfl

/-- The same test inside a loop. Expected: does not reduce. -/
def loopModule (total : Nat) : Module NativeOp :=
  { rows := rows
    main := eff do
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      iterateWith (bool true)
        { while_ := fun _ => bool true
          body := fun _ => eff do
            let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
            ifElse (app "eq" [n, nat total]) (Deferred.succeed gate (nat 0)) (succeed (bool false))
          step := fun c _ => c } }

example (total : Nat) :
    (Program.Authoring.elaborateModule (loopModule total)).toOption.isSome = true := by
  rfl

/-- The same test inside a scope. Expected: reduces. -/
def scopeModule (total : Nat) : Module NativeOp :=
  { rows := rows
    main := eff do
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      scope (eff do
        let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
        ifElse (app "eq" [n, nat total]) (Deferred.succeed gate (nat 0)) (succeed (bool false))) }

example (total : Nat) :
    (Program.Authoring.elaborateModule (scopeModule total)).toOption.isSome = true := by
  rfl

/-- One worker over the cells the crew makes. Expected: does not reduce; at three jobs it does. -/
def workerModule (total : Nat) : Module NativeOp :=
  { rows := rows
    main := eff do
      let q ← Queue.bounded .nat capacity
      let opened ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let released ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let assigned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      worker .none 1 q opened released assigned count gate total }

example (total : Nat) :
    (Program.Authoring.elaborateModule (workerModule total)).toOption.isSome = true := by
  rfl

example : (Program.Authoring.elaborateModule (workerModule 3)).toOption.isSome = true := by
  rfl

end KBProbe0
