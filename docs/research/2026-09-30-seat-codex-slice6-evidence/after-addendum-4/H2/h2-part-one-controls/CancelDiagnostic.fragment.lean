
namespace Test.Program.H2CancelDiagnostic
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects
abbrev W := Effect4.Program.Typed.World

def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))
def sleepCancel : EffName := .withWaiter (.store .cancelSleep) Api.root 0

/-- The existing sleep cancellation's successful store reply reaches its pure failure. -/
theorem cancellation_exit (w : W) (cause : CauseV)
    (typed : TypedProg sleeping w (EffTy.pure .unit)
      ((interpR sleeping).cancelThenFail sleepCancel cause)) :
    ExitOk w (EffTy.pure .unit) (.failure cause) := by
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv typed
  obtain ⟨_, _, next⟩ := TypedProg.store_inv body
  have unit : ExitOk w mid (.success .unit) :=
    unguard_payload_inv sleeping w mid _ _ (next w (leHost_refl w) .unit rfl)
  exact TypedProg.pure_inv (run w (leHost_refl w) (.success .unit) ⟨rfl, unit⟩)

/-- The exact old cancel_typed signature needs the same shape premise as strongExit_of_clean. -/
theorem old_cancel_statement_false (w : W) : ¬ (
    ∀ cause : CauseV, cleanExit (.failure cause) = true →
      TypedProg sleeping w (EffTy.pure .unit)
        ((interpR sleeping).cancelThenFail sleepCancel cause)) := by
  intro claimed
  exact Test.Program.H2PartOne.badName_refused w _
    (cancellation_exit w _ (claimed (Cause.die .badName) rfl))

#print axioms cancellation_exit
#print axioms old_cancel_statement_false
end Test.Program.H2CancelDiagnostic
