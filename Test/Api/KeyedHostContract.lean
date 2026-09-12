import Effect4.Laws.Api.HostSession
import Effect4.Program.Profile
import Effect4.Program.Stream

/-! Finite v2 controls and retained T-12 counterexamples. No oracle answers are loaded.
The general receipt/storage law is reply_commute, not the bounded machine probes below. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Test.Api.KeyedHostContract
open Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession

def table : RowTable := [Profile.Scalar.waitRow]
def opts : Supervision.ForkOptions := { daemon := false, startImmediately := true, maskMode := .inherit }
def program : Api.Program :=
  .bind (.withFiber (.fork (.callback (.external 0) (.lit (.nat 2))) opts))
    (.bind (.withFiber (.fork (.callback (.external 0) (.lit (.nat 3))) opts))
      (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))
def initial : Session program table where
  admitted := {
    ty := ⟨.exitOf .nat (.prod .string .string), .never, .empty⟩
    typed := by cbv
    lawful := by decide
    runnable := by decide
    intFreeTable := by decide
    intFreeType := by decide }
  header := ⟨version, "multi", "keyed-v2", table⟩
  machine := Api.load program 1000

def parked := (advance initial 1000 Api.evaluate).session
def ca : Call := ⟨version, "multi", table, 0, ⟨1⟩, .external 0, .nat 2⟩
def cb : Call := ⟨version, "multi", table, 1, ⟨2⟩, .external 0, .nat 3⟩
def bound := (bindCall (bindCall parked ca 0).session cb 1).session
def a : Reply := ⟨version, "multi", 0, ⟨⟨1⟩, 0⟩, .ofExit (.success (.nat 2))⟩
def b : Reply := ⟨version, "multi", 1, ⟨⟨2⟩, 1⟩, .ofExit (.success (.nat 3))⟩
def ab := (submit (submit bound a).session b).session
def ba := (submit (submit bound b).session a).session
#guard (outstanding parked).map (fun x => (x.1, x.2.1)) = [(⟨1⟩, 0), (⟨2⟩, 1)]
#guard bound.active.length = 2
#guard bound.nextCall = 2
#guard (bindCall bound { ca with callId := 2 } 0).phase = .refused .duplicateCall
#guard (submit bound b).phase = .preflight
#guard ab.pending = ba.pending
#guard ab.active = ba.active
#guard ab.consumed = []
#guard ab.machine.state = bound.machine.state
#guard (applyPending ab 1000).phase = .refused .selectionRequired
#guard (submit ab a).phase = .refused .pendingReply
#guard (submit bound { a with key := ⟨⟨1⟩, 1⟩ }).phase = .refused .noCall
#guard (submit bound { a with callId := 1 }).phase = .refused .callOrder
#guard (submit bound { a with completion := .ofExit (.success (.str "wrong")) }).phase = .refused .envelope
#guard (applyReply ab a.key 0).session.pending = ab.pending
#guard (applyReply ab b.key 1000).session.consumed = [1]
#guard readReply (applyReply ab b.key 1000).session.pending a.key = some a
#guard (submit (applyReply ab b.key 1000).session b).phase = .refused .noCall
#guard (applyReply (applyReply ab b.key 1000).session a.key 1000).session.consumed = [1, 0]
#guard (inspect (applyReply (applyReply ab b.key 1000).session a.key 1000).session).exit =
  some (.success (Val.exitOk (.nat 3)))

-- Cancellation retires all guards it removes, keeping accepted payloads out of consumption.
def cancelled := (advance ab 1000 (.interruptFrom none .empty ⟨1⟩)).session
#guard cancelled.retired = [⟨⟨ca, 0⟩, some a⟩]
#guard readReply cancelled.pending b.key = some b
#guard cancelled.consumed = []
#guard (submit cancelled a).phase = .refused .noCall

-- Stream boundary: Some [] is not a public chunk, and end is a successful payload.
#guard Stream.chunk? .none = some none
#guard Stream.chunk? (.some (.list [.nat 1, .nat 2])) = some (some [.nat 1, .nat 2])
#guard Stream.chunk? (.some (.list [])) = none
#guard Stream.chunk? (.nat 0) = none
#guard (Api.typeOf (Stream.scopedPulls 0 3) (Stream.table "Host.Stream" .nat .never)).isSome

-- E4-HOST-CE-005: applying independent-key answers resumes shared effects, so AB ≠ BA.
def pair (x y : Term) : Term := .app "pair" (.cons x (.cons y .nil))
def child (n : Nat) : Api.Program := .bind (.callback (.external 0) (.lit (.nat n)))
  (.perform .refSet (pair (.var 0) (.lit (.nat n))))
def shared : Api.Program := .bind (.perform .refMake (.lit (.nat 0)))
  (.bind (.withFiber (.fork (child 1) opts))
    (.bind (.withFiber (.fork (child 2) opts))
      (.bind (.awaitFiber (.var 1) .awaitValue)
        (.bind (.awaitFiber (.var 2) .awaitValue) (.perform .refGet (.var 0))))))
def da : Api.Decision := .answerAsync ⟨1⟩ 0 (.ofExit (.success (.nat 1)))
def db : Api.Decision := .answerAsync ⟨2⟩ 1 (.ofExit (.success (.nat 2)))
#guard (Api.admitProgram shared table).isOk
#guard match Api.replayChecked shared 1000 [Api.evaluate, da, db, .flush] [] [] table with
  | .inl run => run.exit = some (.success (.nat 2)) | .inr _ => false
#guard match Api.replayChecked shared 1000 [Api.evaluate, db, da, .flush] [] [] table with
  | .inl run => run.exit = some (.success (.nat 1)) | .inr _ => false

-- E4-HOST-CE-006: the unkeyed answer queue attaches results in registration order.
#guard (Api.run program 1000 [] [b.completion, a.completion] table).exit =
  some (.success (Val.exitOk (.nat 2)))
#guard (inspect (applyReply (applyReply ab a.key 1000).session b.key 1000).session).exit =
  some (.success (Val.exitOk (.nat 3)))

#check @reply_commute
end Test.Api.KeyedHostContract
