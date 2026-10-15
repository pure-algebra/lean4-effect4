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

**The fixtures of the earlier slices stay here as written forms** (the namespace `Written`).
Each writes its binders by name, and each takes its mask as an argument:

- `restoring` is the mask that restores. With it a written form is the library's operation, tree
  for tree: each scenario's program has the same canonical bytes over either.
- `standIn` is the earlier fixture: `uninterruptible` for the mask and `interruptible` for its
  restore. It is right under an interruptible caller only. Its programs are other trees, and
  they give the same answers on these eight scenarios, where no caller is masked.

The written forms are the red controls of the hygiene controls (`Test/Program/QueueOps.lean`):
a caller's variable of a written name reads the operation's own binder there.

Placement. Each scenario is a finite control of the proposed claim `queue-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. Every guard is one run. None proves delivery, a cancellation law or liveness, and none
is a host run: the host runs are the truth lane's (`harness/truth/Truth.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The written forms: the fixtures of the earlier slices

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder. So a
caller's variable named `s` would read the cell's value there, and the same holds of `id`,
`hint`, `r` and `e` at their binders. -/

namespace Written

end Written

-- Each scenario builds: the checker types every step inside its `Ref.modify`, and the mask's
-- saved state at each restore site.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map verdict = List.replicate 8 "built"
-- R4's types: the two offers' answers and the two messages, and no failure.
#guard typesOf r4 = some (.tuple [.bool, .nat, .bool, .nat], .never)

-- The machine's answers, as the probe recorded them.
#guard exitOf r1 = some (.success (.list [.bool true, .bool true, .nat 1, .nat 2]))
#guard exitOf r2 = some (.success (.nat 7))
#guard exitOf r3 = some (.success (.list [.nat 1, .nat 2]))
#guard exitOf r4 = some (.success (.list [.bool true, .nat 1, .bool true, .nat 2]))
#guard exitOf r5 = some (.success (.list [.nat 5, .nat 0]))
#guard exitOf r6 = some (.success (.list [.nat 1, .nat 0, .nat 0]))
-- R7: the reified exit of the interrupted taker: a failure with one interruption, by fiber 0.
#guard exitOf r7 = some (.success (.ctor 1 [.ctor 0 [.list [.ctor 2 [.some (.ctor 0 [.nat 0]),
  .ctor 0 [.list [.pair (.str "stack1") .unit, .pair (.str "stack0") .unit]]]]]]))
-- R8: A's mark, then the offerer's, then B's message.
#guard exitOf r8 = some (.success (.list [.nat 1, .nat 101, .nat 2]))

-- Red control of the pins: R8's log in the first draft's order, the wake before the answer.
#guard exitOf r8 != some (.success (.list [.nat 1, .nat 2, .nat 101]))

-- The ordinary run gives each answer too, at the truth lane's fuel: the root evaluated, then
-- one flush. So no scenario needs a flush of its own.
#guard (scenariosWith library).all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src
-- Red control of the fuel: at a fuel of 5 no scenario has an exit.
#guard (scenariosWith library).all fun src => (exitAt 5 src).isNone

/-! ## The trees are kept: the library's operations against the written forms

`Api.bytesOf` is the canonical bytes of a built program. A tree holds no name: a binder is a
level. So the library's operation and the written form under the mask that restores are one
tree, and each scenario's program has the same bytes over either. -/

-- Each scenario over the library's operations has the bytes of the same scenario over the
-- written forms, under the mask that restores.
#guard (scenariosWith library).map bytesOf ==
  (scenariosWith (Written.ops Written.restoring)).map bytesOf
#guard ((scenariosWith library).map bytesOf).all Option.isSome
-- The construction is one `Ref.make` of the initial value: the fixtures' tree.
#guard elaborate (Queue.bounded .nat 2) == elaborate (Ref.make (Queue.empty .nat 2) : Src NativeOp)
-- Red control of the comparison: the eight programs are eight byte strings.
#guard ((scenariosWith library).map bytesOf).eraseDups.length = 8
-- The earlier fixture, with its two stand-ins, is another tree in each scenario: the mask is the
-- one difference of the library's programs from it.
#guard (List.zip (scenariosWith library) (scenariosWith (Written.ops Written.standIn))).all
  fun pair => bytesOf pair.1 != bytesOf pair.2
-- Under these eight schedules no caller is masked, so the stand-ins give the same answers.
#guard (scenariosWith (Written.ops Written.standIn)).map exitOf ==
  (scenariosWith library).map exitOf

/-! ## The same operations on the abstract model -/

open Effect4.Queue.Model in
/-- R1 on the model: both offers accepted, then the two messages in order. -/
def model1 : OfferReply × OfferReply × TakeReply × TakeReply :=
  let s : State := { capacity := some 2 }
  let a := Queue.Model.offer s 100 1
  let b := Queue.Model.offer a.1 101 2
  let x := Queue.Model.take b.1 ⟨1, 1, 1⟩
  let y := Queue.Model.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, y.2.1)

open Effect4.Queue.Model in
/-- R4 on the model: the second offer waits; the take frees room and answers it; then the
second message. -/
def model4 : OfferReply × OfferReply × TakeReply × List Signal × TakeReply :=
  let s : State := { capacity := some 1 }
  let a := Queue.Model.offer s 100 1
  let b := Queue.Model.offer a.1 101 2
  let x := Queue.Model.take b.1 ⟨1, 1, 1⟩
  let y := Queue.Model.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, x.2.2, y.2.1)

#guard model1 = (.accepted true, .accepted true, .got [1], .got [2])
#guard model4 = (.accepted true, .wait, .got [1], [⟨101, .offered true⟩], .got [2])

#guard [r1Strings, r4Strings].map verdict = ["built", "built"]
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
