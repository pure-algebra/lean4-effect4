import Effect4.Program.Handles
import Effect4.Machine.Witnesses
import Test.Machine.Runtime.CompletionContract

/-! Handle invariant battery (C13, `handles_minted`). Every `#guard` is a decidable check on
an explicit machine: `Minted` at the compiled alphabet, `MintedAt Name.keys Thunk.keys` at the
stores' alphabet on the witness families, and the tape premise `AnswersValid`. The two
`E4-HANDLE-CE-001` examples fail the premise and leave machines that are not minted; the
rows `E4-HANDLE-CE-002` and `E4-HANDLE-CE-003` are the refusals the header of
`Effect4.Machine.Handles` names. -/

set_option autoImplicit false

namespace Test.Runtime.HandlesContract

open Effect4 Effect4.Machine Effect4.Program
open Test.Runtime.CompletionContract (waiting reply answerWith forgedFiber forgedCell)

/-! ## The stores' alphabet: the witness families are minted -/

abbrev MintedS (m : Witnesses.M) : Prop := MintedAt Name.keys Thunk.keys m

#guard MintedS Witnesses.w1DeferredJoin
#guard MintedS Witnesses.w1ImmediateJoin
#guard MintedS Witnesses.w1AwaitFailing
#guard MintedS Witnesses.w1JoinFailing
#guard MintedS Witnesses.w2
#guard MintedS Witnesses.w3EmptyPending
#guard MintedS Witnesses.w3StopsLaunch
#guard MintedS Witnesses.w3NextLaunch
#guard MintedS Witnesses.w3AllFail
#guard MintedS Witnesses.w4Sibling
#guard MintedS Witnesses.w4CompleteTwice
#guard MintedS Witnesses.w4SiblingThenMore
#guard MintedS Witnesses.w4InterruptWaiter
#guard MintedS Witnesses.w15Armed
#guard MintedS Witnesses.w15Flushed

/-- The initial machine of a witness family (`Witnesses.replay` before the tape). -/
def initial (state : Stores) (program : ProgName) : Witnesses.M :=
  Witnesses.spawnRoot (RunMachine.empty state) program emptyCtx

-- The tapes with an external answer pass the premise: the answer is a unit.
#guard AnswersValidAt stores Witnesses.fuel
  [RunDecision.evaluate ⟨0⟩,
    RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩,
    RunDecision.answerAsync ⟨1⟩ 0 (Completion.ofExit (Exit.success Val.unit))]
  (initial Stores.empty (ProgName.forkOnly Witnesses.w2Child Witnesses.daemonChild))
#guard AnswersValidAt stores Witnesses.fuel
  [RunDecision.evaluate ⟨0⟩, RunDecision.answerAsync ⟨1⟩ 0 (Completion.ofExit (Exit.success Val.unit)),
    RunDecision.flush]
  (initial Stores.empty Witnesses.w15Program)
-- The same tape answering with a fiber the machine never minted fails it.
#guard !(AnswersValidAt stores Witnesses.fuel
  [RunDecision.evaluate ⟨0⟩, RunDecision.answerAsync ⟨1⟩ 0 (Completion.ofExit (Exit.success (Val.fiber ⟨9⟩))),
    RunDecision.flush]
  (initial Stores.empty Witnesses.w15Program))
-- An answer naming a fiber that exists passes: the root is fiber `0`.
#guard AnswersValidAt stores Witnesses.fuel
  [RunDecision.evaluate ⟨0⟩, RunDecision.answerAsync ⟨1⟩ 0 (Completion.ofExit (Exit.success (Val.fiber ⟨0⟩))),
    RunDecision.flush]
  (initial Stores.empty Witnesses.w15Program)

/-! ## The compiled alphabet: loaded, run and answered programs -/

#guard Minted (Api.load waiting 80)
#guard Minted (Api.run waiting 80).machine
#guard (Api.run waiting 80).outcome = Api.Outcome.frontier

-- A valid answer: a number, and the Deferred the program itself made (`promise ⟨0⟩`).
#guard AnswersValid waiting 80 [Api.evaluate, reply (.ofExit (.success (.nat 9)))]
#guard Minted (answerWith (.ofExit (.success (.nat 9)))).machine
#guard AnswersValid waiting 80 [Api.evaluate, reply (.ofExit (.success (.promise ⟨0⟩)))]
#guard Minted (answerWith (.ofExit (.success (.promise ⟨0⟩)))).machine
#guard (answerWith (.ofExit (.success (.promise ⟨0⟩)))).exit = some (.success (.promise ⟨0⟩))

-- E4-HANDLE-CE-001: the two forged answers fail the premise, and the machines they leave are
-- not minted. The theorem does not apply to them; replay admission is unchanged.
#guard !(AnswersValid waiting 80 [Api.evaluate, reply (.ofExit (.success (.fiber ⟨7⟩)))])
#guard !(AnswersValid waiting 80 [Api.evaluate, reply (.ofExit (.success (.cell ⟨7⟩)))])
#guard !(Minted forgedFiber.machine)
#guard !(Minted forgedCell.machine)
#guard forgedFiber.outcome = Api.Outcome.finished
#guard forgedCell.outcome = Api.Outcome.finished

-- The premise is checked where the answer lands: a wrong token leaves the async waiting and
-- the machine minted, but the premise still refuses the forged handle.
#guard !(AnswersValid waiting 80 [Api.evaluate, reply (.ofExit (.success (.fiber ⟨7⟩))) 1])
#guard Minted (Api.replay waiting 80 [Api.evaluate, reply (.ofExit (.success (.fiber ⟨7⟩))) 1]).machine

-- A Ref-read answer checks the cell at the point of resumption. Its stored value belongs
-- to the starting-machine premise, which is independent of the answer's own key.
#guard AnswersValidAt (interpOf waiting) 80 [reply (.ofRefGet ⟨0⟩)]
  (Test.Runtime.CompletionContract.withRef (.nat 8))
#guard Minted (Test.Runtime.CompletionContract.readReply (.nat 8))
#guard !(AnswersValidAt (interpOf waiting) 80 [reply (.ofRefGet ⟨1⟩)]
  (Test.Runtime.CompletionContract.withRef (.nat 8)))
#guard AnswersValidAt (interpOf waiting) 80 [reply (.ofRefGet ⟨0⟩)]
  (Test.Runtime.CompletionContract.withRef (.fiber ⟨7⟩))
#guard !(Minted (Test.Runtime.CompletionContract.withRef (.fiber ⟨7⟩)))
#guard !(Minted (Test.Runtime.CompletionContract.readReply (.fiber ⟨7⟩)))

-- Replay stops at the first fuel frontier, so a later answer is not inspected or run.
#guard AnswersValid waiting 0 [Api.evaluate, reply (.ofExit (.success (.fiber ⟨7⟩)))]
#guard Minted (Api.replay waiting 0 [Api.evaluate, reply (.ofExit (.success (.fiber ⟨7⟩)))]).machine

-- Handles inside reified exits and exit lists remain visible to the traversal.
#guard (Val.exitCons (.exitOk (.fiber ⟨7⟩)) (.exitCons (.cell ⟨3⟩) .exitNil)).keys =
  [Handle.fiber ⟨7⟩, Handle.cell ⟨3⟩]

/-! ## Forks mint fibers, stores mint cells -/

def immediateChild : Supervision.ForkOptions := ⟨true, false, Supervision.MaskMode.inherit⟩
def deferredChild : Supervision.ForkOptions := ⟨false, false, Supervision.MaskMode.inherit⟩

/-- A deferred-start fork joined by the parent; the tape's `fire` starts the child. -/
def pForkJoin : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 42))) deferredChild))
    (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect)

#guard (Api.typeOf pForkJoin).isSome
#guard Minted (Api.replay pForkJoin 80 [Api.evaluate]).machine
#guard Minted (Api.replay pForkJoin 80 [Api.evaluate, RunDecision.fire Api.root]).machine
#guard (Api.replay pForkJoin 80 [Api.evaluate, RunDecision.fire Api.root]).fiberCount = 2

/-- The parent makes a Deferred, forks a child that awaits it, completes it and joins. -/
def pDeferred : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.callback .deferredAwait (.var 0)) immediateChild))
      (.bind (.perform .deferredSucceed
                (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
        (.awaitFiber (.var 1) Supervision.ObserverMode.joinEffect)))

#guard (Api.typeOf pDeferred).isSome
#guard Minted (Api.run pDeferred 80).machine
#guard (Api.run pDeferred 80).exit = some (.success (.nat 7))

/-- A Ref made, written and read: the cell handle is minted by the store. -/
def pRef : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 1)))
    (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 5)) .nil))))
      (.perform .refGet (.var 0)))

#guard (Api.typeOf pRef).isSome
#guard Minted (Api.run pRef 80).machine
#guard (Api.run pRef 80).exit = some (.success (.nat 5))

/-! ## The refused positions -/

-- E4-HANDLE-CE-002: the cause's interruptor is provenance, not a handle. The tape interrupts
-- the root from a fiber that does not exist; the exit carries it, and the machine is minted.
def interruptedFromNowhere : Api.Run :=
  Api.replay waiting 80 [Api.evaluate, RunDecision.interruptFrom (some ⟨7⟩) ReasonAnnotations.empty Api.root]

#guard interruptedFromNowhere.exit = some (.failure
  (Cause.annotate (Cause.interrupt (some ⟨7⟩)) (stackAnnotationsOf Api.root) false))
#guard (interruptedFromNowhere.machine.fiber? ⟨7⟩).isNone
#guard Minted interruptedFromNowhere.machine
#guard AnswersValid waiting 80 [Api.evaluate, RunDecision.interruptFrom (some ⟨7⟩) ReasonAnnotations.empty Api.root]

-- E4-HANDLE-CE-003: `Val.validIn` is the store's view and says nothing about fibers, so it
-- cannot carry the invariant alone; `Handle.existsIn` asks the machine.
#guard (Val.fiber ⟨7⟩).validIn forgedFiber.stores
#guard !(Handle.fiber ⟨7⟩).existsIn forgedFiber.machine.world
#guard !(Val.cell ⟨7⟩).validIn forgedCell.stores
#guard !(Handle.cell ⟨7⟩).existsIn forgedCell.machine.world

-- Race settlement reads both the accepted exit and the live entrants. The duplicate
-- winner is bookkeeping only. These probes pin the precise collected positions.
def raceCarrier (state : Supervision.RaceAllState Val Err Defect FiberId Ann) : Api.Machine :=
  { Api.load waiting 80 with races := [⟨0, Api.root, 0, state, false, [], false⟩] }

#guard Minted (raceCarrier (Supervision.RaceAllState.initial []))
#guard !(Minted (raceCarrier { Supervision.RaceAllState.initial [] with
  accepted := some (.success (.fiber ⟨7⟩)) }))
#guard !(Minted (raceCarrier { Supervision.RaceAllState.initial [] with live := [⟨7⟩] }))
#guard Minted (raceCarrier { Supervision.RaceAllState.initial [] with
  winner := some (⟨7⟩, .fiber ⟨7⟩) })

-- Deferred waiter targets are excluded; the completion code is collected separately.
def orphanWaiterStore : Stores :=
  { Stores.empty with deferreds := ⟨[⟨none, [(⟨7⟩, 0)]⟩], []⟩ }

#guard MintedS (RunMachine.empty orphanWaiterStore)
#guard !(MintedS (RunMachine.empty { orphanWaiterStore with
  deferreds := ⟨[⟨some (.success (.fiber ⟨7⟩)), [(⟨7⟩, 0)]⟩], []⟩ }))

/-! ## The theorem on an explicit run -/

theorem waiting_answered_minted :
    Minted (Api.replay waiting 80 [Api.evaluate, reply (.ofExit (.success (.nat 9)))]).machine :=
  handles_minted waiting 80 _ [] ⟨load_minted waiting 80, by decide⟩

theorem forkJoin_minted :
    Minted (Api.replay pForkJoin 80 [Api.evaluate, RunDecision.fire Api.root]).machine :=
  handles_minted pForkJoin 80 _ [] ⟨load_minted pForkJoin 80, by decide⟩

-- E4-CHECK-CE-010: numeric interruptor provenance is not a dereferenced handle.
example (cell : DeferredKey) (id : FiberId) :
    (SyncOp.deferredInterruptWith cell id).keys = [Handle.promise cell] := rfl

end Test.Runtime.HandlesContract
