import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: can the kernel run machine commands on a crew fiber with symbolic values? -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace SymProbe2

abbrev NC := Prim EffName EffThunk Val Err Defect FiberId Ann
abbrev NF := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- The crew's program at three jobs. -/
def crewRoot : NativeEff :=
  match Program.Authoring.elaborateModule (crew 3) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- Worker 1's continuation after its take: the point of the loop body's first bind. -/
def bodyPoint (env : List Val) : Point :=
  { path := [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0], env := env, fuel := 1986, tape := [] }

/-- Worker 1, running, with its take's answer `v` as its current primitive, above the body's
continuation and an arbitrary stack. -/
def worker1 (v : Val) (env : List Val) (K : List NC) : NF :=
  { RunFiber.make ⟨1⟩ (Prim.success v) true (2048, false) emptyCtx with
    frame :=
      { current := .success v
        stack := .onSuccess (.success .unit) (.cont (bodyPoint env)) :: K
        interruptible := true
        interruptedCause := none
        deferredInterrupt := false }
    running := true
    currentOpCount := 5 }

/-- A machine holding that fiber over some stores. -/
def machine (v : Val) (env : List Val) (K : List NC) (st : Stores) : Api.Machine :=
  { (RunMachine.empty st : Api.Machine) with fibers := [worker1 v env K], nextId := 4 }

/-- The head of a fiber's current primitive, with the path its name carries. -/
def headPath : NC → Option (List Nat)
  | .onSuccess _ (.cont p) => some p.path
  | .sync (.pure p) => some p.path
  | _ => none

/-- The commands run on the machine, at the crew's own evaluator. -/
def run (n : Nat) (m : Api.Machine) : Api.Machine :=
  letI := evaluatorFor crewRoot []
  (driveState (interpOf crewRoot []) n m [.loop ⟨1⟩ false]).1

#eval (((run 1 (machine (.nat 7) (List.replicate 8 .unit) [] Stores.empty)).fiber? ⟨1⟩).map
  fun f => headPath f.frame.current)
#eval (((run 2 (machine (.nat 7) (List.replicate 8 .unit) [] Stores.empty)).fiber? ⟨1⟩).map
  fun f => (headPath f.frame.current, f.frame.stack.length, f.currentOpCount))
#eval (((run 3 (machine (.nat 7) (List.replicate 8 .unit) [] Stores.empty)).fiber? ⟨1⟩).map
  fun f => (headPath f.frame.current, f.frame.stack.length, f.currentOpCount))

set_option profiler true in
/-- One command, symbolic in the job, the scope's values, the stack below and the stores. -/
example (x0 x1 x2 x3 x4 x5 x6 x7 v : Val) (K : List NC) (st : Stores) :
    (((run 1 (machine v [x0, x1, x2, x3, x4, x5, x6, x7] K st)).fiber? ⟨1⟩).map
      fun f => headPath f.frame.current) = some (some [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1]) := by
  rfl

/-- Whether a primitive is a store operation, and the path of a stack's top continuation. -/
def isOp : NC → Bool
  | .sync (.op _) => true
  | _ => false

def topCont : List NC → Option (List Nat)
  | .onSuccess _ (.cont p) :: _ => some p.path
  | _ => none

set_option profiler true in
/-- Two commands: the note's store operation is next, above the body's continuation. -/
example (x0 x1 x2 x3 x4 x5 x6 x7 v : Val) (K : List NC) (st : Stores) :
    (((run 2 (machine v [x0, x1, x2, x3, x4, x5, x6, x7] K st)).fiber? ⟨1⟩).map
      fun f => (isOp f.frame.current, topCont f.frame.stack, f.currentOpCount)) =
      some (true, some [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], 7) := by
  rfl

/-- The crew's five cells, with the assignment holding `xs`, in some stores. -/
def withCells (st : Stores) (c0 c1 c2 c4 : Val) (xs : List Val) : Stores :=
  { st with refs := [c0, c1, c2, .list xs, c4] }

#eval (((run 3 (machine (.nat 7) [.handle 2 0, .handle 2 1, .handle 2 2, .handle 2 3, .handle 2 4,
    .handle 3 0, .unit, .unit] [] (withCells Stores.empty .unit .unit .unit .unit []))).state.refs[3]?))

set_option profiler true in
/-- Three commands: the note appends `[v, 1]` to the assignment, symbolic in the job, the
assignment's entries, the other cells, the stack below and the rest of the stores. The scope
holds the crew's handles where the worker reads them. -/
example (x5 x6 x7 v c0 c1 c2 c4 : Val) (xs : List Val) (K : List NC) (st : Stores) :
    (run 3 (machine v [.handle 2 0, .handle 2 1, .handle 2 2, .handle 2 3, .handle 2 4, x5, x6, x7] K
      (withCells st c0 c1 c2 c4 xs))).state.refs[3]? = some (.list (xs ++ [.list [v, .nat 1]])) := by
  rfl

end SymProbe2
