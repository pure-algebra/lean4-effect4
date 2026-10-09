import Effect4.Api
import Effect4.Program.Profile

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace ImmediateBudget
open Effect4 Effect4.Machine Effect4.Program

def program : Api.Program := .perform (.external 0) (.lit (.nat 2))
def table : RowTable := [Profile.Scalar.waitRow]
def answer : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 7))

def loaded (answers : List (Completion Val Err Defect FiberId Ann)) (ops : Nat := 2) : Api.Machine :=
  let m := Api.load program 100 answers
  match m.fiber? Api.root with
  | none => m
  | some f => m.update { f with maxOpsBeforeYield := ops, currentOpCount := 0 }

def step (m : Api.Machine) (d : Api.Decision) : Api.Machine :=
  letI := evaluatorFor program table
  (stepDecisionState (interpOf program table) 100 m d).1

def immediate : Api.Machine := step (loaded [answer]) Api.evaluate
def parked : Api.Machine := step (step (loaded []) Api.evaluate) (.answerAsync Api.root 0 answer)

def report (m : Api.Machine) : Bool × Bool × Nat × List Nat :=
  ((m.fiber? Api.root).any (·.exit.isSome),
    m.trace.any fun event => match event with | .yieldInjected _ _ => true | _ => false,
    m.trace.length, (awaits m).map (·.token))

#eval report immediate
#eval report parked
#guard (report immediate).1 = false
#guard (report immediate).2.1 = true
#guard (report parked).1 = true
#guard (report parked).2.1 = false

-- At a high operation budget, both controls finish with the expected exit.
def immediateHigh : Api.Machine := step (loaded [answer] 100) Api.evaluate
def parkedHigh : Api.Machine := step (step (loaded [] 100) Api.evaluate) (.answerAsync Api.root 0 answer)
#eval report immediateHigh
#eval report parkedHigh
#guard (immediateHigh.fiber? Api.root).bind RunFiber.exit = some (.success (.nat 7))
#guard (parkedHigh.fiber? Api.root).bind RunFiber.exit = some (.success (.nat 7))

end ImmediateBudget
