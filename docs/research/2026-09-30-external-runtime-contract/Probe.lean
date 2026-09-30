import Effect4.Api
import Effect4.Program.Profile

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.ExternalRuntimeContract
open Effect4 Effect4.Machine Effect4.Program

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "research probe"

def wrongFiberProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.str "wrong"))) ⟨true, true, .interruptible⟩))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def wrongFiberTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush]

#guard Api.typeOf wrongFiberProgram [fiberRow] = some (EffTy.pure .nat)
#guard (match Api.replayChecked wrongFiberProgram 500 wrongFiberTape [] [fiberRow] with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.str "wrong")))

-- Same call and actual fiber identity, with the declared child result: the positive control.
def rightFiberProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 7))) ⟨true, true, .interruptible⟩))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

#guard Api.typeOf rightFiberProgram [fiberRow] = some (EffTy.pure .nat)
#guard (match Api.replayChecked rightFiberProgram 500 wrongFiberTape [] [fiberRow] with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.nat 7)))

theorem wrongFiber_checked_type :
    Api.typeOf wrongFiberProgram [fiberRow] = some (EffTy.pure .nat) := by rfl'

#print axioms wrongFiber_checked_type

-- An allocation reply is tied to the current machine allocation index.
-- Two fixed replies accepted against the same snapshot need not both be applicable later.
def allocationRow : Row := Profile.Resource.acquireRow
def beforeAllocation : NativeMachine := RunMachine.empty Stores.empty
def afterAllocation : NativeMachine :=
  { beforeAllocation with state := { Stores.empty with
      externals := { Stores.empty.externals with allocated := [Profile.Resource.target] } } }
def allocationReply : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 0))

#guard Program.admitAnswer allocationRow beforeAllocation Api.root 0 allocationReply = none
#guard Program.admitAnswer allocationRow beforeAllocation ⟨1⟩ 1 allocationReply = none
#guard Program.admitAnswer allocationRow afterAllocation ⟨1⟩ 1 allocationReply =
  some (.answerType ⟨1⟩ 1 allocationRow.answer)
#guard Program.admitAnswer allocationRow beforeAllocation ⟨1⟩ 1
  (.ofExit (.success (.nat 1))) = some (.answerType ⟨1⟩ 1 allocationRow.answer)

-- Ordinary direct replies cannot reuse or nest external handles today.
#guard (externalValue allocationRow.answer [Profile.Resource.target] (Value.external 0)).isNone
#guard (externalValue (.option allocationRow.answer) [] (.some (.nat 0))).isNone
#guard (externalValue (.option allocationRow.answer) [Profile.Resource.target]
  (.some (Value.external 0))).isNone

#eval IO.println "External contract probes: 11 finite guards passed."

end Test.ExternalRuntimeContract
