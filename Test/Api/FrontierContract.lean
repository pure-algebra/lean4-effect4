import Effect4.Api

/-! P2b: distinguish the driver's two exhaustion sites and pin compile fuel
independently of command fuel. Host-guard regression is in HostSessionContract. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Test.Api.FrontierContract
open Effect4 Effect4.Machine Effect4.Program

def program : Api.Program := .succeed (.lit (.nat 42))
def nested : Api.Program := .bind (.succeed (.lit (.nat 1))) program

def exhaustionTag (fuel : Nat) (tape : List Api.Decision) : Nat :=
  letI := evaluatorFor program
  match replayEval (interpOf program) fuel tape (Api.load program 32) with
  | .frontier .fuel _ => 0
  | .frontier .tape _ => 1
  | .finished _ => 2
  | .stuck _ _ => 3

theorem command_exhaustion : exhaustionTag 0 [Api.evaluate] = 0 := by decide
theorem tape_exhaustion : exhaustionTag 40 [] = 1 := by decide

#guard exhaustionTag 40 [Api.evaluate] = 2
#guard (Api.replay nested 100 [Api.evaluate] [] [] [] 1).outcome = .frontier
#guard (Api.replay nested 100 [Api.evaluate] [] [] [] 32).exit = some (.success (.nat 42))
#guard (Api.replay program 0 [Api.evaluate] [] [] [] 32).outcome = .frontier
#guard (Api.run nested 100 [] [] [] 32).exit = some (.success (.nat 42))
#guard (Api.runSync nested 100 [] [] [] 32).2 = .success (.nat 42)

#print axioms command_exhaustion
#print axioms tape_exhaustion
end Test.Api.FrontierContract
