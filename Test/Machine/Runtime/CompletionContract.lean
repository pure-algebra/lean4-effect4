import Effect4.Api
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.StoresLaws

/-!
# External Completion answers

D6 keeps code on internal commands and first-order Completion data on the tape.
These finite replays cover exit answers, a Ref read evaluated on resumption,
wrong and repeated tokens, and the input-validity gap `E4-HANDLE-CE-001`.
The Layer machine's own instance of these constructors (`D6-FB-LAYER-REF`) retired
with the join of 2026-09-07: one `RunMachine` instantiation answers them now.
-/

set_option autoImplicit false

namespace Test.Runtime.CompletionContract

open Effect4 Effect4.Machine Effect4.Program

def waiting : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit)) (.callback .deferredAwait (.var 0))

def reply (answer : Completion Val Err Defect FiberId Ann) (token : Nat := 0) : Api.Decision :=
  .answerAsync Api.root token answer

def answerWith (answer : Completion Val Err Defect FiberId Ann) : Api.Run :=
  Api.replay waiting 80 [Api.evaluate, reply answer]

#guard (Api.typeOf waiting).isSome
#guard (Api.run waiting 80).outcome = Api.Outcome.frontier
#guard (answerWith (.ofExit (.success (.nat 9)))).exit = some (.success (.nat 9))
#guard (answerWith (.ofExit (.failure (Cause.fail Err.boom)))).exit =
  some (.failure (Cause.fail Err.boom))
#guard (answerWith (.ofExit (.success (.nat 9)))).outcome = Api.Outcome.finished

-- Wrong tokens leave the async waiting; a duplicate cannot overwrite its first exit.
#guard (Api.replay waiting 80 [Api.evaluate, reply (.ofExit (.success (.nat 9))) 1]).outcome =
  Api.Outcome.frontier
#guard (Api.replay waiting 80 [Api.evaluate, reply (.ofExit (.success (.nat 9))),
  reply (.ofExit (.success (.nat 10)))]).exit = some (.success (.nat 9))

def parked : Api.Machine := (Api.run waiting 80).machine
def withRef (v : Val) : Api.Machine := { parked with state := { parked.state with refs := [v] } }

def readReply (v : Val) : Api.Machine :=
  (replayEval (interpOf waiting) 80 [reply (.ofRefGet ⟨0⟩)] (withRef v)).machine

#guard ((readReply (.nat 3)).fiber? Api.root).bind RunFiber.exit = some (.success (.nat 3))
#guard ((readReply (.nat 8)).fiber? Api.root).bind RunFiber.exit = some (.success (.nat 8))
#guard (interpOf waiting).answerCode (.ofRefGet ⟨0⟩) =
  Prim.sync (EffThunk.store (Thunk.op (SyncOp.refGet ⟨0⟩)))
#guard stores.answerCode (.ofExit (.success (.nat 9))) = Prim.success (.nat 9)

-- E4-HANDLE-CE-001: the answer format does not certify that its handles exist.
def forgedFiber : Api.Run := answerWith (.ofExit (.success (.fiber ⟨7⟩)))
#guard forgedFiber.outcome = Api.Outcome.finished
#guard forgedFiber.exit = some (.success (.fiber ⟨7⟩))
#guard (forgedFiber.machine.fiber? ⟨7⟩).isNone

def forgedCell : Api.Run := answerWith (.ofExit (.success (.cell ⟨7⟩)))
#guard forgedCell.exit = some (.success (.cell ⟨7⟩))
#guard !(Val.cell ⟨7⟩).validIn forgedCell.stores

end Test.Runtime.CompletionContract
