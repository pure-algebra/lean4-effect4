import Effect4.Laws.Program.AnswerSlots.AllocationFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: synthetic yields retain transient allocation answers and their actual initial heap.
Reach: the shared initializer graph, exact pending-prefix contents and stable entry readiness.
Consumer: the common native current-head and forced-yield producers.
This transport supplies no source history or numeric application invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Every returned initializer answer retains the root-or-ready phase. -/
theorem value_phase (spec : Spec) (world : World) (kind : Kind spec.stable.Kind) (value : Val)
    (good : ValueAt spec world kind value) : Phase spec world := by
  cases kind <;> exact good.1

/-- Every current initializer code retains the root-or-ready phase. -/
theorem code_phase (spec : Spec) (world : World) (kind : Kind spec.stable.Kind) (program : NCode)
    (owned : CodeAt spec world kind program) : Phase spec world := by
  induction owned with
  | success good => exact value_phase spec _ _ _ good
  | failure phase => exact phase
  | initial stage => exact .inl stage.owner
  | allocating _ stage => exact .inl stage.owner
  | gateAllocating stage => exact .inl stage.owner
  | entered _ entry => exact .inl entry.owner
  | stable ready => exact .inr ready
  | frontier _ phase => exact phase
  | yielding phase => exact phase
  | bound _ _ ih => exact ih
  | yieldThen phase => exact phase

/-- A pending source entry cannot already belong to the stable phase. -/
theorem pending_not_ready (spec : Spec) (world : World) (pending : world.entered = false) : ¬ Ready spec world := by
  intro ready
  have impossible : false = true := pending.symm.trans ready.1
  cases impossible

/-- Equal allocation counts and exact pending contents retain an existing actual source point. -/
theorem rootStage_rebase (spec : Spec) (first last : World) (index : Nat) (point : Point)
    (stage : RootStage spec first index point) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferreds : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (pending : last.entered = false)
    (contents : last.state.refs = Initialization.values spec.initialization last.state.refs.length) :
    RootStage spec last index point := by
  have count := refs.symm.trans stage.stage.source.2.2.2.1
  refine ⟨future.owner.symm.trans stage.owner, ⟨?_, ?_⟩, deferreds.symm.trans stage.deferreds, pending⟩
  · exact ⟨stage.stage.source.1, stage.stage.source.2.1, stage.stage.source.2.2.1, count,
      stage.stage.source.2.2.2.2⟩
  · exact contents.trans (congrArg (Initialization.values spec.initialization) count)

/-- An unconsumed actual entry marker retains its exact heap across a pending yield. -/
theorem entry_rebase (spec : Spec) (first last : World) (point : Point) (entry : Entry spec first point)
    (future : Future first last) (refs : first.state.refs.length = last.state.refs.length)
    (pending : last.entered = false)
    (contents : last.state.refs = Initialization.values spec.initialization last.state.refs.length) : Entry spec last point := by
  have oldCount : first.state.refs.length = spec.initialization.width := by
    rw [entry.contents, Initialization.values_length]
  refine ⟨future.owner.symm.trans entry.owner, entry.source, entry.path, entry.env, ?_, ?_, pending⟩
  · exact contents.trans (congrArg (Initialization.values spec.initialization) (refs.symm.trans oldCount))
  · exact ⟨Nat.le_trans entry.cells.1 future.refs, Nat.le_trans entry.cells.2 future.deferreds⟩

/-- A pending yield's answer reconstructs every transient allocation class from actual equal counts. -/
theorem value_rebase (spec : Spec) (first last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferreds : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (pending : last.entered = false)
    (contents : last.state.refs = Initialization.values spec.initialization last.state.refs.length)
    (kind : Kind spec.stable.Kind) (value : Val) (good : ValueAt spec first kind value) :
    ValueAt spec last kind value := by
  cases kind with
  | stable kind => exact ⟨phase_future spec first last future good.1, good.2⟩
  | allocated index =>
    obtain ⟨phase, key, count, empty, oldContents, oldPending⟩ := good
    have nextCount := refs.symm.trans count
    exact ⟨phase_future spec first last future phase, key, nextCount, deferreds.symm.trans empty,
      contents.trans (congrArg (Initialization.values spec.initialization) nextCount), pending⟩
  | gate =>
    obtain ⟨phase, key, cells, oldContents, oldPending⟩ := good
    have count : first.state.refs.length = spec.initialization.width := by
      rw [oldContents, Initialization.values_length]
    exact ⟨phase_future spec first last future phase, key,
      ⟨Nat.le_trans cells.1 future.refs, Nat.le_trans cells.2 future.deferreds⟩,
      contents.trans (congrArg (Initialization.values spec.initialization) (refs.symm.trans count)), pending⟩
  | yielded refCount deferredCount =>
    obtain ⟨phase, key, count, empty, oldReady, oldContents, oldPending⟩ := good
    have nextCount := refs.symm.trans count
    exact ⟨phase_future spec first last future phase, key, nextCount, deferreds.symm.trans empty,
      pending_not_ready spec last pending,
      contents.trans (congrArg (Initialization.values spec.initialization) nextCount), pending⟩

/-- Current transient code is rebased only with the actual pending-prefix heap certificate. -/
theorem code_rebase (spec : Spec) (first : World) (kind : Kind spec.stable.Kind) (program : NCode)
    (owned : CodeAt spec first kind program) (last : World) (future : Future first last)
    (refs : first.state.refs.length = last.state.refs.length)
    (deferreds : first.state.deferreds.cells.length = last.state.deferreds.cells.length)
    (pending : last.entered = false)
    (contents : last.state.refs = Initialization.values spec.initialization last.state.refs.length) :
    CodeAt spec last kind program := by
  induction owned generalizing last with
  | success good => exact .success (value_rebase spec _ _ future refs deferreds pending contents _ _ good)
  | failure phase => exact .failure (phase_future spec _ _ future phase)
  | initial stage active => exact .initial (rootStage_rebase spec _ _ _ _ stage future refs deferreds pending contents) active
  | allocating small stage => exact .allocating small (rootStage_rebase spec _ _ _ _ stage future refs deferreds pending contents)
  | gateAllocating stage available => exact .gateAllocating (rootStage_rebase spec _ _ _ _ stage future refs deferreds pending contents) available
  | entered fragment entry => exact .entered fragment (entry_rebase spec _ _ _ entry future refs pending contents)
  | stable ready code => exact False.elim (pending_not_ready spec last pending (ready_future spec _ _ future ready))
  | frontier zero phase => exact .frontier zero (phase_future spec _ _ future phase)
  | yielding phase oldRefs oldDeferred oldReady oldContents oldPending =>
    have nextRefs := refs.symm.trans oldRefs
    exact .yielding (phase_future spec _ _ future phase) nextRefs (deferreds.symm.trans oldDeferred)
      (pending_not_ready spec last pending)
      (contents.trans (congrArg (Initialization.values spec.initialization) nextRefs)) pending
  | bound first callback ih =>
    refine .bound (ih last future refs deferreds pending contents) ?_
    intro nextWorld nextFuture view answer good
    exact callback nextWorld ((model spec []).future_trans _ _ _ future nextFuture) view answer good
  | yieldThen phase first oldPending ih =>
    exact .yieldThen (phase_future spec _ _ future phase) (ih last future refs deferreds pending contents)
      (fun _ => ⟨pending, contents⟩)

/-- A stable phase excludes every still-pending allocation answer. -/
theorem value_future_ready (spec : Spec) (first last : World) (future : Future first last)
    (ready : Ready spec first) (kind : Kind spec.stable.Kind) (value : Val)
    (good : ValueAt spec first kind value) : ValueAt spec last kind value := by
  cases kind with
  | stable kind => exact ⟨phase_future spec first last future good.1, good.2⟩
  | allocated index => exact False.elim (pending_not_ready spec first good.2.2.2.2.2 ready)
  | gate => exact False.elim (pending_not_ready spec first good.2.2.2.2 ready)
  | yielded refs deferreds => exact False.elim (good.2.2.2.2.1 ready)

/-- Stable current code tolerates actual heap writes after its entry marker has been consumed. -/
theorem code_future_ready (spec : Spec) (first : World) (kind : Kind spec.stable.Kind) (program : NCode)
    (owned : CodeAt spec first kind program) (last : World) (future : Future first last)
    (ready : Ready spec first) : CodeAt spec last kind program := by
  induction owned generalizing last with
  | success good => exact .success (value_future_ready spec _ _ future ready _ _ good)
  | failure phase => exact .failure (phase_future spec _ _ future phase)
  | initial stage active | allocating small stage | gateAllocating stage available =>
    exact False.elim (pending_not_ready spec _ stage.pending ready)
  | entered fragment entry => exact False.elim (pending_not_ready spec _ entry.pending ready)
  | stable current code => exact .stable (ready_future spec _ _ future current) code
  | frontier zero phase => exact .frontier zero (phase_future spec _ _ future phase)
  | yielding phase refs deferreds pending => exact False.elim (pending ready)
  | bound first callback ih =>
    refine .bound (ih last future ready) ?_
    intro nextWorld nextFuture view answer good
    exact callback nextWorld ((model spec []).future_trans _ _ _ future nextFuture) view answer good
  | yieldThen phase first pending ih =>
    exact .yieldThen (phase_future spec _ _ future phase) (ih last future ready)
      (fun missing => False.elim (missing (ready_future spec _ _ future ready)))

end Effect4.Program.AnswerSlots.AllocationAdapter
