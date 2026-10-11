import Test.Dogfood.Scenario
import Test.Dogfood.P3WorkerQueue

/-! The workers program, shared by the scenario and its invariant proofs. -/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Workers

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P3WorkerQueue (take runJob)

/-! ## 1. The program -/

/-- One worker with an identity. Its connection carries the identity: the acquisition notes it in
`opened` and answers it, and the release notes the acquired value in `released`. Then the worker
takes jobs forever. It notes each job with its own identity in `assigned`, runs the job, handles
a failed job and counts it. With `twice`, the worker registers the same release a second time:
the fault of the cleanup clause's red control. -/
def worker (twice : Bool) (id : Nat) (opened released assigned count gate : TermSrc)
    (total : Nat) : Src NativeOp :=
  scope (eff do
    let _conn ← acquireRelease "conn" "exit"
      (andThen (note opened (nat id)) (succeed (nat id)))
      (note released (var "conn"))
    let _again ← (if twice then
        acquireRelease "conn" "exit" (succeed (nat id)) (note released (var "conn"))
      else succeed (nat id))
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          let _ ← note assigned (app "pair" [job, nat id])
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet "n" (app "succ" [var "n"]) count
          ifElse (app "eq" [n, nat total])
            (Deferred.succeed gate (nat 0)) (succeed (bool false))
        step := fun c _ => c })

/-- Two workers forked into a scope with rc.112's `Effect.forkScoped` options. The cells are, in
allocation order: `opened`, `released`, `assigned` and `count`. The root answers the released
connections and the count. -/
def crewWith (twice : Bool) (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let opened ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let released ← Ref.make (ascribe (.list .nat) (app "nil" []))
      let assigned ← Ref.make (ascribe (.list (.prod .nat .nat)) (app "nil" []))
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make .nat .nat
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped
          (worker twice 1 opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        let _w2 ← withFiber (Action.forkScoped
          (worker twice 2 opened released assigned count gate total)
          (Effect4.Codegen.Forms.defaults true))
        Deferred.await gate)
      let closed ← Ref.get released
      let n ← Ref.get count
      return app "pair" [closed, n] }

/-- The scenario's program: the crew, each release registered once. -/
def crew (total : Nat) : Module NativeOp := crewWith false total

end Test.Dogfood.Scenario.Workers
