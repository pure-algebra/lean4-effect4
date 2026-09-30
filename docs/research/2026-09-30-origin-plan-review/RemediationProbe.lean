import Effect4.Api
import Effect4.Program.Profile

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.OriginRemediationReview
open Effect4 Effect4.Machine Effect4.Program

def sleeper : Api.Program := .perform .sleep (.lit (.nat 1))
def replyTape (v : Val) : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success v))]

def checkedRefusal (p : Api.Program) (tape : List Api.Decision) (table : RowTable := []) :
    Option (Nat × Program.Refusal) :=
  match Api.replayChecked p 80 tape [] table with
  | .inl _ => none
  | .inr (position, _, refusal, _) => some (position, refusal)

#guard checkedRefusal sleeper (replyTape (.nat 42)) =
  some (1, .notExternal Api.root 0)
#guard checkedRefusal sleeper (replyTape .unit) =
  some (1, .notExternal Api.root 0)

-- This existing API certifies the program, not the decision tape.
#guard (match Api.check sleeper with
  | .error _ => false
  | .ok t => (t.replay (replyTape (.nat 42)) ⟨80, 80⟩).exit ==
      some (.success (.nat 42)))

-- Normal clock-driven completion remains available on the checked route.
#guard (match Api.replayChecked sleeper 80
    [Api.evaluate, .advance (ClockMillis.ofNat 1), Api.flush] with
  | .inr _ => false
  | .inl r => r.exit == some (.success .unit))

-- A real external row has separate positive and type-refusal controls.
def externalWait : Api.Program := .perform (.external 0) (.lit (.nat 1))
def waitTable : RowTable := [Profile.Scalar.waitRow]
#guard checkedRefusal externalWait (replyTape .unit) waitTable =
  some (1, .answerType Api.root 0 .nat)
#guard (match Api.replayChecked externalWait 80 (replyTape (.nat 42)) [] waitTable with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.nat 42)))

-- Admission can accept a scalar which the runtime then converts into a handle.
def emptyMachine : NativeMachine := RunMachine.empty Stores.empty
#guard Program.admitAnswer Profile.Resource.acquireRow emptyMachine Api.root 0
  (.ofExit (.success (.nat 0))) = none
#guard Val.hasTy (.nat 0) Profile.Resource.acquireRow.answer [] = false
#guard externalValue Profile.Resource.acquireRow.answer [] (.nat 0) =
  some ([Profile.Resource.target], Value.external 0)

-- Inspect the existing separate compilation limit before changing the wrapper.
def tiny : Api.Program := .succeed (.lit (.nat 7))
#guard (Api.replay tiny 80 [Api.evaluate] [] [] 0).outcome = .frontier
#guard (Api.replay tiny 80 [Api.evaluate] [] [] 0).exit = none
#guard (match Api.replayChecked tiny 80 [Api.evaluate] with
  | .inl r => r.outcome == .finished && r.exit == some (.success (.nat 7))
  | .inr _ => false)

#eval IO.println "Remediation probes: all 12 finite guards passed."

end Test.OriginRemediationReview
