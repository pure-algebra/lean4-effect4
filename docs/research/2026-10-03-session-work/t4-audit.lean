import Test.Api.HostSessionContract
import Effect4.Laws.Program.Typed.Admission

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession
open Test.Api.HostSessionContract

#print axioms PreparedSuccess
#print axioms preflight_success_prepared_fits
#print axioms submit_success_prepared_fits
#print axioms received_prepares_nat
#check preflight_success_prepared_fits
#check submit_success_prepared_fits

-- Admission of a failing reserved defect does not establish ExitOk.
-- This checked discriminator keeps the success-only bridge from implying a blanket law.
def reservedReply : Reply :=
  { reply0 with completion := .ofExit (.failure (Cause.die .badName)) }
#guard preflight bound0 reservedReply =
  .ok (.answerAsync Api.root 0 reservedReply.completion)
#guard admit table bound0.machine (.answerAsync Api.root 0 reservedReply.completion) = none
#guard externalAdmits table 0 reservedReply.completion [] = true

example (w : Typed.World) :
    ¬Typed.ExitOk w admitted.ty (.failure (Cause.die .badName)) := by
  intro admittedExit
  have forbidden := admittedExit.2 (.die .badName .empty) (by decide)
  exact forbidden.1 rfl
