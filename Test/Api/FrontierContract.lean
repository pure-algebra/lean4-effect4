import Effect4.Laws.Api.Frontier
import Effect4.Laws.Program.ReasonsR
import Effect4.Program.Profile

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
def sleeping : Api.Program := .callback .sleep (.lit (.nat 4))
def waiting : Api.Program := .callback (.external 0) (.lit (.nat 7))
def waitTable : RowTable := [Profile.Scalar.waitRow]

#guard (Api.run sleeping 100).reasons = [.awaitTimer Api.root 4]
#guard (Api.run waiting 100 [] [] waitTable).reasons = [.awaitHost ⟨Api.root, 0⟩]
#guard (Api.replay program 100 []).reasons = [.awaitDecision]
#guard (Api.replay program 0 [Api.evaluate] [] [] [] 32).reasons = [.commandFuel]
#guard (Api.replay nested 100 [Api.evaluate] [] [] [] 1).reasons =
  [.commandFuel, .compileFuel Api.root]
#guard (Api.run program 100).reasons = []
#guard (Api.replay waiting 100 [Api.evaluate, Api.evaluate] [] [] waitTable).reasons =
  [.awaitHost ⟨Api.root, 0⟩]
#guard Api.HostProtocol.observe (Api.run sleeping 100).machine = .parked
#guard Api.HostProtocol.observe (Api.run waiting 100 [] [] waitTable).machine = .awaitingAsync
#guard Api.HostProtocol.observe (Api.replay program 100 []).machine = .idle
#guard Api.HostProtocol.observe (Api.run program 100).machine = .terminated

theorem sleeping_complete : Api.Tape.Complete sleeping [] [Api.evaluate, Api.flush] 100 := by
  have hr : (Api.replay sleeping 100 [Api.evaluate, Api.flush]).reasons = [.awaitTimer Api.root 4] := by decide
  change (∀ key, Api.FrontierReason.awaitHost key ∉ (Api.replay sleeping 100 [Api.evaluate, Api.flush]).reasons) ∧
    Api.FrontierReason.awaitDecision ∉ (Api.replay sleeping 100 [Api.evaluate, Api.flush]).reasons
  rw [hr]
  simp

#print axioms sleeping_complete
#print axioms Effect4.Api.awaitHost_mem
#print axioms Effect4.Api.awaitDecision_iff
#print axioms Effect4.Api.commandFuel_iff
#print axioms Effect4.Api.exists_awaitHost_iff
#print axioms Effect4.Api.all_exited_not_runnable
#print axioms Effect4.Api.observe_awaitingAsync_iff
#print axioms Effect4.Api.observe_terminated_iff
#print axioms Effect4.Api.observe_idle_iff
#print axioms Effect4.Api.observe_idle_tape_iff
#print axioms Effect4.Api.observe_of_reasons
#print axioms Effect4.Program.Sched.reasons_eq_ref
#print axioms Effect4.Program.Sched.book_reasons_eq_ref
end Test.Api.FrontierContract
