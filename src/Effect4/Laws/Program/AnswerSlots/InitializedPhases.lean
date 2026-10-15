import Effect4.Laws.Program.AnswerSlots.InitializedHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: initialization phase and forced-yield store counts retain actual current-code permission.
Reach: monotone store lengths, unchanged owner and explicit equality of transient lengths.
Limit: root exclusivity and native store updates remain separate producers.
Consumer: forced-yield constant callbacks and initialized native evaluation.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Every actual successful answer retains initialization ownership or stable readiness. -/
theorem value_phase (spec : Spec) (world : World) (kind : Kind) (value : Val)
    (good : ValueAt spec world kind value) : Phase spec world := by
  cases kind with
  | stable _ | allocated _ | yielded _ _ => exact good.1
  | gate => exact .inr good.2

/-- Every current code retains initialization ownership or stable readiness. -/
theorem code_phase (spec : Spec) (world : World) (kind : Kind) (program : NCode)
    (owned : CodeAt spec world kind program) : Phase spec world := by
  induction owned with
  | success good => exact value_phase spec _ _ _ good
  | failure phase => exact phase
  | initial stage | allocating small stage | gateAllocating stage => exact .inl stage.2.1
  | stable ready => exact .inr ready
  | frontier zero phase | yielding phase => exact phase
  | bound first callback ih => exact ih
  | yieldThen phase => exact phase

/-- A forced-yield reply with unchanged allocation counts preserves all answer classes. -/
theorem value_rebase (spec : Spec) (first last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferred : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (kind : Kind) (value : Val) (good : ValueAt spec first kind value) : ValueAt spec last kind value := by
  cases kind with
  | stable kind => exact ⟨phase_future spec first last future good.1, good.2⟩
  | allocated index | yielded index deferreds =>
    exact ⟨phase_future spec first last future good.1, good.2.1,
      refs.symm.trans good.2.2.1, deferred.symm.trans good.2.2.2⟩
  | gate => exact ⟨good.1, ready_future spec first last future good.2⟩

/-- The actual initializer stage depends only on its owner and current allocation counts. -/
theorem stage_rebase (spec : Spec) (first last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferred : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (index : Nat) (point : Point) (stage : RootStage spec first index point) : RootStage spec last index point := by
  obtain ⟨bound, owner, path, env, beforeRefs, beforeDeferred, source⟩ := stage
  exact ⟨bound, future.1.symm.trans owner, path, env,
    refs.symm.trans beforeRefs, deferred.symm.trans beforeDeferred, source⟩

/-- Current code transports through a forced yield only when transient allocation counts agree. -/
theorem code_rebase (spec : Spec) (first : World) (kind : Kind) (program : NCode)
    (owned : CodeAt spec first kind program) (last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferred : first.state.deferreds.cells.length = last.state.deferreds.cells.length) : CodeAt spec last kind program := by
  induction owned generalizing last with
  | success good => exact .success (value_rebase spec _ _ future refs deferred _ _ good)
  | failure phase => exact .failure (phase_future spec _ _ future phase)
  | initial stage => exact .initial (stage_rebase spec _ _ future refs deferred _ _ stage)
  | allocating small stage => exact .allocating small (stage_rebase spec _ _ future refs deferred _ _ stage)
  | gateAllocating stage => exact .gateAllocating (stage_rebase spec _ _ future refs deferred _ _ stage)
  | stable ready held => exact .stable (ready_future spec _ _ future ready) held
  | frontier zero phase => exact .frontier zero (phase_future spec _ _ future phase)
  | yielding phase beforeRefs beforeDeferred =>
    exact .yielding (phase_future spec _ _ future phase)
      (refs.symm.trans beforeRefs) (deferred.symm.trans beforeDeferred)
  | bound first callback ih =>
    refine .bound (ih last future refs deferred) ?_
    intro nextWorld nextFuture view answer good
    exact callback nextWorld
      ⟨future.1.trans nextFuture.1, Nat.le_trans future.2.1 nextFuture.2.1,
        Nat.le_trans future.2.2 nextFuture.2.2⟩ view answer good
  | yieldThen phase held ih => exact .yieldThen (phase_future spec _ _ future phase) (ih last future refs deferred)
end Effect4.Program.AnswerSlots.Initialized
