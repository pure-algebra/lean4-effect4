import Effect4.Laws.Program.Typed.Assembly

/-! E4-SCHED-CE-015: retain the host-answer counterexample against the reviewed reachability
statement, and a nonvacuous timer control for the answer-free replacement. This does not
repair the host-free counterexamples or prove the M6 obligations. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Test.Counterexamples.Machine.Semantics.M6Capstone
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- The old statement, preserved solely to retain the falsifier. -/
def ReviewedRReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, m = (replayR root.program fuel tape).machine

-- The existing M6 reachability definition accepts arbitrary async answers.
def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def badTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))]
def bad : RState := (replayR sleeper 80 badTape).machine

#guard Api.typeOf sleeper = some (EffTy.pure .unit)
#guard ((bad.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem bad_reachable : ReviewedRReachable (sleeper : ProgramSource) 80 bad :=
  ⟨badTape, rfl⟩

theorem bad_exit_not_typed (w : Typed.World) :
    ¬ FitsExit w (EffTy.pure .unit) (.success (.nat 42)) := by
  intro h
  exact h

theorem bad_has_bad_exit : ∃ f ∈ bad.fibers,
    f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by decide

theorem bad_not_typed (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_has_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → FitsExit w ty (.success (.nat 42)) at he
  apply bad_exit_not_typed w
  apply he (EffTy.pure .unit)
  rw [hid]
  exact h.1.root

-- The exact current capstone, specialized to this program and reached machine.
-- This refutes an open target; no accepted theorem is contradicted.
theorem current_m6_capstone_false : ¬ (
    Api.typeOf sleeper [] = some (EffTy.pure .unit) →
    ClosedEff (EffTy.pure .unit) →
    ReviewedRReachable (sleeper : ProgramSource) 80 bad →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad) := by
  intro h
  obtain ⟨w, hw⟩ := h (by rfl') ⟨rfl, rfl⟩ bad_reachable
  exact bad_not_typed w hw


/-- The forged answer is outside the repaired reachability premise. -/
theorem badTape_rejected : ¬ (∀ d ∈ badTape, NoHostAnswer d) := by
  intro h
  exact h (.answerAsync Api.root 0 (.ofExit (.success (.nat 42)))) (by decide)

def timerTape : List Api.Decision :=
  [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 100000), Api.flush]
def timed : RState := (replayR sleeper 80 timerTape).machine

theorem timerTape_answerFree : ∀ d ∈ timerTape, NoHostAnswer d := by
  intro d hd
  simp only [timerTape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> trivial

theorem timed_reachable : RReachable (sleeper : ProgramSource) 80 timed :=
  ⟨timerTape, timerTape_answerFree, rfl⟩

#guard (timed.fiber? Api.root).bind RunFiber.exit = some (.success .unit)

#print axioms bad_reachable
#print axioms bad_exit_not_typed
#print axioms bad_has_bad_exit
#print axioms bad_not_typed
#print axioms current_m6_capstone_false
#print axioms badTape_rejected
#print axioms timerTape_answerFree
#print axioms timed_reachable
end Test.Counterexamples.Machine.Semantics.M6Capstone
