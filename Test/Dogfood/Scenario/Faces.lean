import Test.Dogfood.Scenario.Workers
import Test.Dogfood.Scenario.QueueWorkers
import Test.Dogfood.Scenario.Routing
import Test.Dogfood.Scenario.Atomic
import Test.Dogfood.Scenario.Timeout

/-!
# The scenarios' printed modules: each prints and reads back (decisions row 254)

A scenario's host run starts from its printed module. This battery pins two answers for each
scenario's program: the module printer prints it, and the module reader gives the built program
back. The five programs are `Workers.crew`, `QueueWorkers.crew`, `Routing.request`,
`Atomic.shop` and `Timeout.fetch`.

Three of them needed the state plan's T5 for these answers. The crew's logs and the shop's
window are rows whose binder terms no name images: they print since part A. The fetch's retry
loop states its cursor's type: it reads back since part B's second step (DI-91). The crew over
the queue holds the Queue's five public operations, whose printed text and reading
`Test/Program/QueueFaces.lean` pins one by one.

Placement. Finite controls of `read_print` and `read_exact` (R8's top nodes,
`src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`) on seven
programs. No guard states target typing, and none states a host run. The host clause of each
scenario stands on the keyed lane, which performs the scenario's named runs on its printed
module (`harness/truth/session/Keyed.lean`; `Test/Dogfood/README.md`, the section "The host
runs").
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.Faces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood (printVerdict readBackVerdict)

/-- The printer's answer on a module's built program, and whether its printing reads back. -/
def shows (m : Module NativeOp) : Option (String × Bool) :=
  (Effect4.Api.Author.build m).toOption.map fun b => (printVerdict b, readBackVerdict b)

/-- Whether the printed module of one program reads back as the built program of another. -/
def readsAs (printed other : Module NativeOp) : Bool :=
  match Effect4.Api.Author.build printed, Effect4.Api.Author.build other with
  | .ok a, .ok b =>
    match Effect4.Api.printModule "main" a.program a.table with
    | some m => decide (Effect4.Api.readModule m a.table = .ok b.program)
    | none => false
  | _, _ => false

-- The crew, at two totals of jobs.
#guard shows (Workers.crew 2) = some ("printed", true)
#guard shows (Workers.crew 3) = some ("printed", true)
-- The crew over the public Queue, at two totals of jobs.
#guard shows (QueueWorkers.crew 3) = some ("printed", true)
#guard shows (QueueWorkers.crew 2) = some ("printed", true)
-- The handler's request.
#guard shows (Routing.request "secret" 2 "2") = some ("printed", true)
-- The shop, without a fault.
#guard shows (Atomic.shop .none) = some ("printed", true)
-- The fetch: its retry loop states its cursor's type.
#guard shows Timeout.fetch = some ("printed", true)

-- Red control of the comparison: a crew's module reads as that crew's program, and as no
-- other total's.
#guard readsAs (Workers.crew 2) (Workers.crew 2) && !readsAs (Workers.crew 2) (Workers.crew 3)
-- The same control on the crew over the queue. Its module reads as that crew's program. It reads
-- as no other total's, and not as the crew whose take leaves its job in the buffer.
#guard readsAs (QueueWorkers.crew 3) (QueueWorkers.crew 3) &&
  !readsAs (QueueWorkers.crew 3) (QueueWorkers.crew 2) &&
  !readsAs (QueueWorkers.crew 3) (QueueWorkers.crewWith .keeps 3)

end Test.Dogfood.Scenario.Faces
