import Effect4.Laws.Program.Footprint
import Effect4.Laws.Machine.FinalizerRun

/-!
Concept: scope-lifetime-finalization, R11.
Claim: at most one finalizer start per registration, consumed by FinalizerTransfer.
This instance accounts for the exact events of the shared labelled word.
Its reach includes every native frame, interpreter, carried cause, and finalizer name selection.
It establishes no source-use uniqueness, log provenance, progress, or host agreement.
-/

set_option autoImplicit false
namespace Effect4.Program.Moves
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.FinalizerCredits

/-- An administrative event owns no finalizer accounting entry. -/
theorem administrative_finalizer (choose : EffName → Bool) (event : REvent)
    (quiet : administrative event = true) :
    runStarted choose event = false ∧ runRegistered choose event = false := by
  cases event <;> simp only [administrative, Bool.false_eq_true] at quiet <;> exact ⟨rfl, rfl⟩

/-- An administrative word owns no finalizer accounting entry. -/
theorem Administrative.finalizer (choose : EffName → Bool) {events : List REvent}
    (quiet : Administrative events) :
    events.countP (runStarted choose) = 0 ∧ events.countP (runRegistered choose) = 0 := by
  induction events with
  | nil => exact ⟨rfl, rfl⟩
  | cons event rest ih =>
    have parts := Bool.and_eq_true_iff.mp quiet
    have item := administrative_finalizer choose event parts.1
    have tail := ih parts.2
    constructor
    · simpa only [List.countP_cons, item.1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using tail.1
    · simpa only [List.countP_cons, item.2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using tail.2


/-- The actual exit-selected pop retains its finalizer debit. -/
theorem popExit_debit (choose : EffName → Bool) (f : NFrame) (exit : ExitV) :
    answer choose (popExit f exit).answer + stack choose (popExit f exit).fiber.stack ≤ stack choose f.stack := by
  cases exit <;> exact getCont_le choose f _ _ _

/-- The actual exit-selected pop starts no finalizer before its replacement. -/
theorem popExit_no_start (choose : EffName → Bool) (f : NFrame) (exit : ExitV) :
    (popExit f exit).events.countP (started choose) = 0 := by
  cases exit <;> exact getCont_no_start choose f _ _ _

/-- Every labelled operation spends only its saved or newly registered finalizer credits. -/
theorem LabelledMove.finalizer (choose : EffName → Bool) {label : MoveLabel} {f g : NFrame}
    (move : LabelledMove label f g) :
    stack choose g.stack + label.events.countP (runStarted choose) ≤
      stack choose f.stack + label.events.countP (runRegistered choose) := by
  cases move with
  | answer f code emitted quiet =>
    rw [(quiet.finalizer choose).1, (quiet.finalizer choose).2]
    exact Nat.le_refl _
  | push f name emitted quiet =>
    rw [(quiet.finalizer choose).1, (quiet.finalizer choose).2]
    exact Nat.le_refl _
  | step id interp f g emitted found =>
    have debit := step_debit choose interp f
    rw [found] at debit
    simp only [frame_starts, frame_registrations]
    change emitted.countP (started choose) + stack choose g.stack ≤ stack choose f.stack + emitted.countP (registered choose) at debit
    omega
  | finish id interp f exit emitted found =>
    have debit := step_debit choose interp f
    rw [found] at debit
    have empty := step_finished_stack interp f exit (congrArg Prod.fst found)
    simp only [frame_starts, frame_registrations, empty, stack, List.countP_nil, Nat.zero_add]
    change emitted.countP (started choose) + 0 ≤ _ at debit
    exact debit
  | pop id f demand skip cause =>
    have debit := getCont_le choose f demand skip cause
    have silent := getCont_no_start choose f demand skip cause
    simp only [frame_starts, frame_registrations, silent, Nat.add_zero]
    simp only [FinalizerCredits.pop] at debit
    omega
  | popAnswer id f exit code launched selectedFrame =>
    have debit := popExit_debit choose f exit
    have silent := popExit_no_start choose f exit
    cases launched with
    | none =>
      simp only [exitEvents, List.append_nil, frame_starts, frame_registrations, silent, Nat.add_zero]
      omega
    | some name =>
      obtain ⟨body, flag, found⟩ := selectedFrame name rfl
      rw [found] at debit
      change (if choose name then 1 else 0) + stack choose (popExit f exit).fiber.stack ≤ _ at debit
      simp only [exitEvents, List.countP_append, frame_starts, frame_registrations, silent,
        List.countP_singleton, runStarted, runRegistered, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
      exact Nat.le_trans (Nat.add_comm _ _ ▸ debit) (Nat.le_add_right _ _)
  | mask f =>
    unfold FrameFiber.uninterruptible
    split <;> exact Nat.le_refl _
  | unmask f =>
    unfold FrameFiber.interruptibleRegion
    split <;> exact Nat.le_refl _
  | pendingFailure f => exact Nat.le_refl _
  | idle f emitted quiet =>
    rw [(quiet.finalizer choose).1, (quiet.finalizer choose).2]
    exact Nat.le_refl _

/-- The finalizer instance sums along the shared word, then reads its actual trace extension. -/
theorem TracedMoves.finalizer (choose : EffName → Bool) {m n : NativeMachine} {f g : NFrame}
    (word : TracedMoves m f n g) :
    n.trace.countP (runStarted choose) + stack choose g.stack + m.trace.countP (runRegistered choose) ≤
      m.trace.countP (runStarted choose) + stack choose f.stack + n.trace.countP (runRegistered choose) := by
  obtain ⟨labels, moves, trace⟩ := word
  have debit := Moves.balance (fun frame => stack choose frame.stack)
    (fun label => label.events.countP (runRegistered choose))
    (fun label => label.events.countP (runStarted choose))
    (fun _ _ _ move => move.finalizer choose) moves
  rw [trace]
  simp only [List.countP_append, events, List.countP_flatMap, Function.comp_def]
  omega

end Effect4.Program.Moves
