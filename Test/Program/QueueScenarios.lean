import Test.Program.QueueScenariosData
import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Library.Queue.Ops
import Effect4.Laws.Library.Queue.Profile

/-!
# The Queue's operations on the machine: the probe's eight scenarios (rows 233 and 255)

Each scenario is one program over the library's operations
(`src/Effect4/Library/Queue/Ops.lean`), run on the Lean machine on one schedule. The answers are
the probe's (`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean` and its
output beside it).

**The operations are the library's.** `Queue.bounded`, `Queue.offer`, `Queue.take` and
`Queue.size` wrap the step terms with the shared waiting wrapper
(`src/Effect4/Library/Waiting.lean`): the mask that restores, a posted helper for each
notification, and a withdrawal on interruption. Every binder of an operation is minted.

R1, R2, R4 and R5 cross to the generated engine, and their exits are pinned there
(`ocaml/engine/test/queue/`, bound by `Test/Program/QueueEngine.lean`). This battery pins the
other scenarios, and the first two at a message type of strings.

Placement. Each scenario is a finite control of the proposed claim `queue-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. Every guard is one run. None proves delivery, a cancellation law or liveness, and none
is a host run: the host runs are the truth lane's (`tools/Drivers/Truth.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

-- R4's types: the two offers' answers and the two messages, and no failure.
#guard typesOf r4 = some (.tuple [.bool, .nat, .bool, .nat], .never)

-- The machine's answers, as the probe recorded them.
#guard exitOf r3 = some (.success (.list [.nat 1, .nat 2]))
#guard exitOf r6 = some (.success (.list [.nat 1, .nat 0, .nat 0]))
-- R7: the reified exit of the interrupted taker: a failure with one interruption, by fiber 0.
#guard exitOf r7 = some (.success (.ctor 1 [.ctor 0 [.list [.ctor 2 [.some (.ctor 0 [.nat 0]),
  .ctor 0 [.list [.pair (.str "stack1") .unit, .pair (.str "stack0") .unit]]]]]]))
-- R8: A's mark, then the offerer's, then B's message.
#guard exitOf r8 = some (.success (.list [.nat 1, .nat 101, .nat 2]))

/-! ## At a message type of strings -/

#guard exitOf r1Strings =
  some (.success (.list [.bool true, .bool true, .str "a", .str "b"]))
#guard exitOf r4Strings =
  some (.success (.list [.bool true, .str "a", .bool true, .str "b"]))
-- Red control of the message type: a number offered into a cell of strings does not build.
#guard verdict (eff do
  let q ← Queue.bounded .string 2
  let a ← Queue.offer .string q (nat 1)
  return a) != "built"

end Test.Program.QueueScenarios
