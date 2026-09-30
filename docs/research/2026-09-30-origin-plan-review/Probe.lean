import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Keeps
import Effect4.Program.Admit

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.OriginPlanReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed

-- A model of the proposed paired append, not an implementation of the ledger.
theorem pairedAppend_keeps_agreement {A : Type} (r : A) :
    Keeps (fun s : List A × List A => s.1 = s.2)
      (fun s => (s.1 ++ [r], s.2 ++ [r])) := by
  intro s
  apply propext
  constructor
  · exact List.append_cancel_right
  · intro h
    exact congrArg (fun xs => xs ++ [r]) h

-- The actual outer decision can mutate the machine without running commands.
def trivial : NativeEff := .succeed (.lit .unit)
def loaded : NativeMachine := Api.load trivial 20 []
#guard loaded.middlewareInstalled = false
#guard (steppedBy trivial 0 [] loaded .installMiddleware).middlewareInstalled = true

-- The existing M6 reachability definition accepts arbitrary async answers.
def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def badTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))]
def bad : RState := (replayR sleeper 80 badTape).machine

#guard Api.typeOf sleeper = some (EffTy.pure .unit)
#guard ((bad.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem bad_reachable : RReachable (sleeper : ProgramSource) 80 bad :=
  ⟨badTape, rfl⟩

theorem bad_exit_not_typed (w : Typed.World) :
    ¬ StrongExit w (EffTy.pure .unit) (.success (.nat 42)) := by
  intro h
  exact Bool.noConfusion h.1

theorem bad_has_bad_exit : ∃ f ∈ bad.fibers,
    f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by decide

theorem bad_not_typed (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_has_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  apply he (EffTy.pure .unit)
  rw [hid]
  exact h.1.root

-- The exact current capstone, specialized to this program and reached machine.
-- This refutes an open target; no accepted theorem is contradicted.
theorem current_m6_capstone_false : ¬ (
    Api.typeOf sleeper [] = some (EffTy.pure .unit) →
    ClosedEff (EffTy.pure .unit) →
    RReachable (sleeper : ProgramSource) 80 bad →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad) := by
  intro h
  obtain ⟨w, hw⟩ := h (by rfl') ⟨rfl, rfl⟩ bad_reachable
  exact bad_not_typed w hw

#print axioms pairedAppend_keeps_agreement
#print axioms bad_reachable
#print axioms bad_exit_not_typed
#print axioms bad_has_bad_exit
#print axioms bad_not_typed
#print axioms current_m6_capstone_false

end Test.OriginPlanReview
