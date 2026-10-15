import Effect4.Author

/-! Program data shared by the battery and scenario fixtures. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P3WorkerQueue

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The program -/

/-- `Queue.take` answered by the host: the next job's id. -/
def take : RowDef := Row.host "Jobs.take" .unit .nat
/-- Run one job on the host; it may fail with (tag, message). -/
def runJob : RowDef := Row.host "Jobs.run" .nat .unit (.prod .string .string)

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

/-! ## 4. Which theorem reaches the program -/

-- The pool calls host rows: its row table is not empty, so `run_eq_ref` does not reach it.

end Test.Dogfood.P3WorkerQueue
