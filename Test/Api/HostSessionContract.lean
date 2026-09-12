import Effect4.Laws.Api.HostSession
import Effect4.Program.Profile

/-! Finite checked-session controls. Every call is a real park in the existing machine.
The forced pair failure is a protocol/type control, not a Scalar.spec RowStep assertion. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Test.Api.HostSessionContract
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession

def table : RowTable := [Profile.Scalar.waitRow]
def program : Api.Program :=
  .bind (.callback (.external 0) (.lit (.nat 2))) (.callback (.external 0) (.lit (.nat 3)))
def header : Header := ⟨2, "session-A", "serial-root-scalar-v1", table⟩
def admitted : Api.AdmittedProgram program table where
  ty := ⟨.nat, .prod .string .string, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  intFreeType := by decide

def initial : Session program table := { admitted, header, machine := Api.load program 100 }
def parked : Session program table := (advance initial 100 Api.evaluate).session
def call0 : Call := ⟨2, "session-A", table, 0, Api.root, .external 0, .nat 2⟩
def bound0 : Session program table := (bindCall parked call0 0).session
def reply0 : Reply := ⟨2, "session-A", 0, ⟨Api.root, 0⟩, .ofExit (.success (.nat 2))⟩
def pending0 : Session program table := (submit bound0 reply0).session
def after0 : Session program table := (applyPending pending0 100).session

def call1 : Call := { call0 with callId := 1, request := .nat 3 }
def bound1 : Session program table := (bindCall after0 call1 1).session
def reply1 : Reply := { reply0 with callId := 1, key := ⟨Api.root, 1⟩, completion := .ofExit (.success (.nat 3)) }
def pending1 : Session program table := (submit bound1 reply1).session
def finished : Session program table := (applyPending pending1 100).session

#guard match start program table "serial-root-scalar-v1" header 100 with | .ok _ => true | _ => false
#guard match start program table "serial-root-scalar-v1" { header with version := 99 } 100 with | .error .version => true | _ => false
#guard outstanding parked = [(Api.root, 0, .external 0, .nat 2)]
#guard parked.machine.state.externals.answers = []
#guard (bindCall parked call0 0).phase = .bound
#guard (submit bound0 reply0).phase = .preflight
#guard pending0.applied = 0
#guard requestOf pending0.machine Api.root 0 = some (.external 0, .nat 2)
#guard (applyPending pending0 0).phase = .frontier
#guard pendingReplies (applyPending pending0 0).session = [reply0]
#guard (applyPending pending0 0).session.applied = 0
#guard requestOf (applyPending pending0 0).session.machine Api.root 0 = some (.external 0, .nat 2)
#guard (applyPending pending0 100).phase = .applied
#guard after0.applied = 1
#guard after0.consumed = [0]
#guard (inspect after0).outcome = .frontier
#guard outstanding after0 = [(Api.root, 1, .external 0, .nat 3)]
#guard (submit after0 reply0).phase = .refused .noCall
#guard (bindCall after0 call1 1).phase = .bound
#guard (submit bound1 reply0).phase = .refused .noCall
#guard (inspect finished).exit = some (.success (.nat 3))
#guard finished.applied = 2
#guard finished.consumed = [0, 1]

-- One command consumes the reply even if the subsequent evaluation lacks fuel.
def shortApplied : Session program table := (applyPending pending0 1).session
#guard (applyPending pending0 1).phase = .applied
#guard shortApplied.applied = 1
#guard requestOf shortApplied.machine Api.root 0 = none
#guard (inspect shortApplied).outcome = .frontier
#guard outstanding (advance shortApplied 100 Api.evaluate).session = [(Api.root, 1, .external 0, .nat 3)]

-- Independent identity/type mutations at the same valid park.
#guard (bindCall parked { call0 with version := 99 } 0).phase = .refused .version
#guard (bindCall parked { call0 with session := "session-B" } 0).phase = .refused .session
#guard (bindCall parked { call0 with table := [] } 0).phase = .refused .table
#guard (bindCall parked { call0 with table := [{ Profile.Scalar.waitRow with trailing := ["x"] }] } 0).phase = .refused .table
#guard (bindCall parked { call0 with fiber := ⟨1⟩ } 0).phase = .refused .staleCall
#guard (bindCall parked { call0 with op := .external 1 } 0).phase = .refused .staleCall
#guard (bindCall parked { call0 with request := .nat 4 } 0).phase = .refused .staleCall
#guard (bindCall parked call0 1).phase = .refused .staleCall
#guard (submit bound0 { reply0 with version := 99 }).phase = .refused .version
#guard (submit bound0 { reply0 with session := "session-B" }).phase = .refused .session
#guard (submit bound0 { reply0 with completion := .ofExit (.success (.str "wrong")) }).phase = .refused .envelope
#guard (submit bound0 { reply0 with completion := .ofExit (.failure (Cause.fail (.tag 0))) }).phase = .refused .envelope
#guard (submit pending0 reply0).phase = .refused .pendingReply
#guard (advance pending0 100 Api.evaluate).phase = .progressed
#guard (advance bound0 100 (.answerAsync Api.root 0 reply0.completion)).phase = .refused .directAnswer

def failedReply : Reply := { reply0 with completion := .ofExit (.failure (Cause.fail (.tagged "Scalar" "selected failure"))) }
def failed : Session program table := (applyPending (submit bound0 failedReply).session 100).session
#guard (inspect failed).exit = some (.failure (Cause.fail (.tagged "Scalar" "selected failure")))
#guard failed.applied = 1

-- Cancellation retires the pending association; a late reply cannot become another answer.
def cancelled : Session program table := (advance pending0 100 (.interruptFrom none .empty Api.root)).session
#guard requestOf cancelled.machine Api.root 0 = none
#guard (submit cancelled reply0).phase = .refused .noCall
#guard cancelled.applied = 0
#guard cancelled.retired = [⟨⟨call0, 0⟩, some reply0⟩]
#guard cancelled.pending = []

#check @preflight_envelope
#check @applyPending_zero
#check @applied_guard_absent
#check @applied_reply_refused
#check @advance_answer_refuses
end Test.Api.HostSessionContract
