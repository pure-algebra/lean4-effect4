import Effect4.Laws.Machine.Lift

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: source-opportunity decision accounting for the original Workers and Atomic claims.
The existing decision invariant supplies worlds, command ownership, and drained-task ownership.
A machine fact supplies its own actual command, edit, and prepared-reply obligations.
This construction adds no admission, progress, or host agreement premise or conclusion.
-/
set_option autoImplicit false
namespace Effect4.Machine.Lift
open Effect4 Effect4.Machine Effect4.Laws.Effects
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w} {o : WorldOrder W} {interp : RunInterp ν σ β ε δ ι α χ St κ}
variable {J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
variable {O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}
variable {A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop}

omit [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
/-- The interrupt decision is one word of the existing edits, at the actual lookup states.
Consumers: the saved-stack equality and shared place balance outside the command loop. -/
theorem interruptEdit_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (updated : ∀ m target old, m.fiber? target = some old → ∀ who extra,
      Edge m (m.update (interruptRecord interp who extra old).1)
        (.update (interruptRecord interp who extra old).1))
    (recorded : ∀ m who target, Edge m (m.emit [.interruptRecorded who target])
      (.emit [.interruptRecorded who target]))
    (deferred : ∀ m target, Edge m (m.emit [.interruptDeferred target])
      (.emit [.interruptDeferred target]))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (who : Option FiberId)
    (extra : ReasonAnnotations α) (target : FiberId) (fiber : RunFiber ν σ β ε δ ι α χ κ φ)
    (found : m.fiber? target = some fiber) :
    ∃ word, Effect4.Contracts.Path Edge m (interruptEdit interp m who extra target fiber) word := by
  unfold interruptEdit
  dsimp only
  split
  · exact ⟨_, .cons (recorded m who target) (.cons (deferred _ target)
      (.cons (updated ((m.emit [.interruptRecorded who target]).emit [.interruptDeferred target])
        target fiber found who extra) (.nil _)))⟩
  · exact ⟨_, .cons (recorded m who target)
      (.cons (updated (m.emit [.interruptRecorded who target]) target fiber found who extra) (.nil _))⟩

/-- Attach a machine fact while retaining the actual decision invariant's world and queues.
Consumer: source-budget histories; the reply premise reads the actual prepared first resume. -/
theorem DecisionLift.withMachineFact (base : DecisionLift o interp J I O A)
    (P : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (step : ∀ ts w m c rest, m.stuck = none → Guarded J I O ts w m (c :: rest) →
      P m → P (driveStep interp m c rest).1)
    (edits : MachineEdits interp P)
    (answer : ∀ w m id token value, J w m → P m → m.stuck = none →
      A w m (.answerAsync id token value) →
      P (driveStep interp {m with state := (prepareAsyncAnswer interp m id token value).1}
        (.resume id token (prepareAsyncAnswer interp m id token value).2) [Cmd.drainDue]).1) :
    DecisionLift o interp (fun w m => J w m ∧ P m) I O A := by
  refine {
    step := ?_, nil := base.nil, evaluate := ?_, drain := ?_, ran := ?_, task := ?_,
    skip := base.skip, yield := ?_, interrupt := ?_, middleware := ?_,
    clockNone := ?_, clockSome := ?_, answer := ?_ }
  · intro ts w m c rest running held
    have before : Guarded J I O ts w m (c :: rest) := ⟨held.1.1, held.2⟩
    obtain ⟨next, order, moved⟩ := base.step ts w m c rest running before
    exact ⟨next, order, ⟨moved.1, step ts w m c rest running before held.1.2⟩, moved.2⟩
  · intro w m id held running
    exact base.evaluate w m id held.1 running
  · intro w m owner fiber held found
    have moved := base.drain w m owner fiber held.1 found
    exact ⟨⟨moved.1, edits.drain m owner fiber held.2 found⟩, moved.2⟩
  · intro w m owner task held
    exact ⟨base.ran w m owner task held.1, edits.ran m owner task held.2⟩
  · intro w m owner task tasks held running snapshot
    exact base.task w m owner task tasks held.1 running snapshot
  · intro w m id verdict held
    exact ⟨base.yield w m id verdict held.1, edits.yield m id verdict held.2⟩
  · intro w m who extra target fiber held found
    exact ⟨base.interrupt w m who extra target fiber held.1 found,
      edits.interrupt m who extra target fiber held.2 found⟩
  · intro w m held
    exact ⟨base.middleware w m held.1, edits.middleware m held.2⟩
  · intro w m millis state held running clock
    obtain ⟨next, order, moved⟩ := base.clockNone w m millis state held.1 running clock
    have fact := edits.clock m millis held.2 running
    rw [clock] at fact
    exact ⟨next, order, moved, fact⟩
  · intro w m millis owed state held running clock
    obtain ⟨next, order, moved, queue⟩ := base.clockSome w m millis owed state held.1 running clock
    have fact := edits.clock m millis held.2 running
    rw [clock] at fact
    exact ⟨next, order, ⟨moved, edits.owed _ owed fact⟩, queue⟩
  · intro w m id token value held running admitted
    obtain ⟨next, order, moved⟩ := base.answer w m id token value held.1 running admitted
    exact ⟨next, order, ⟨moved.1, answer w m id token value held.1 held.2 running admitted⟩, moved.2⟩

end Effect4.Machine.Lift
