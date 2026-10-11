import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: can the kernel compile a continuation of the crew's code with symbolic
values, on the crew program at a fixed job count? -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace SymProbe

/-- The crew's program at three jobs. -/
def crewRoot : NativeEff :=
  match Program.Authoring.elaborateModule (crew 3) with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- Worker 1's continuation after its take: the point of the loop body's first bind. -/
def bodyPoint (env : List Val) : Point :=
  { path := [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0], env := env, fuel := 1986, tape := [] }

/-- The head of a compiled primitive, with the path that its name carries. -/
def headOf : Prim EffName EffThunk Val Err Defect FiberId Ann → String
  | .onSuccess _ (.cont p) => s!"onSuccess cont {p.path} env {p.env.length}"
  | .sync (.op _) => "sync op"
  | .sync (.pure p) => s!"sync pure {p.path}"
  | .success _ => "success"
  | _ => "other"

#eval headOf (contAOf crewRoot (.cont (bodyPoint (List.replicate 8 .unit))) (Val.nat 7))

set_option profiler true in
/-- The kernel computes the continuation's code with eight symbolic values in scope and a
symbolic job. -/
example (x0 x1 x2 x3 x4 x5 x6 x7 v : Val) :
    (match contAOf crewRoot (.cont (bodyPoint [x0, x1, x2, x3, x4, x5, x6, x7])) v with
      | .onSuccess _ (.cont p) => some p.path
      | _ => none) = some [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1] := by
  rfl

end SymProbe
