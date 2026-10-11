import Test.Dogfood.Scenario.Programs
import Test.Dogfood.Scenario.Atomic.Model
import Effect4.Laws.Program.NativeHeap
import Effect4.Laws.Program.NativeHistory
import Effect4.Laws.Program.NativeHeapHistory

/-!
# Actual scenario sources in the lexical fragment

Concept: store-typing R4, serving `Atomic.bounded` and `QueueWorkers.Assertions.jobs_step`.
The queue statement retains every natural job count.
The Atomic statement reads the actual successful author build.
These source facts supply the fragment premise of native source scope.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.SourceFragment
open Effect4 Effect4.Program Effect4.Laws.Auto Effect4.Program.SourceScope

/-- The queue crew's actual source belongs to the lexical fragment at every job count. -/
theorem queue_fragment (total : Nat) : Fragment (Programs.queueProgram total) := by
  unfold Fragment
  kernel_rfl

/-- A successful queue build retains the checked fragment for its actual source. -/
theorem queue_built_fragment (total : Nat) (b : Api.Built)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b) : Fragment b.program := by
  rw [Programs.queue_built_program total b built]
  exact queue_fragment total

/-- The actual shop's elaboration contains only supported lexical source heads. -/
theorem atomic_fragment_census :
    ((Authoring.elaborateModule (Atomic.shop .none)).toOption.map fun root =>
      (Node.addresses (.eff root)).all fun path => (Node.at_ (.eff root) path).all directHead) = some true := by
  kernel_rfl

/-- A successful shop build retains its checked source fragment. -/
theorem atomic_built_fragment (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b) : Fragment b.program := by
  have census := atomic_fragment_census
  rw [(Api.Author.build_retains built).1] at census
  exact Option.some.inj census

/-- The loaded queue root retains source scope at every compiler budget. -/
theorem queue_root_at (total compileFuel : Nat) :
    CodeAt (Programs.queueProgram total) (resolve (Programs.queueProgram total) (rootPoint compileFuel)) :=
  resolve_scoped _ (queue_fragment total) _ rfl

/-- The actual loaded shop root retains source scope at every compiler budget. -/
theorem atomic_root_at (b : Api.Built) (built : Api.Author.build (Atomic.shop .none) = .ok b)
    (compileFuel : Nat) : CodeAt b.program (resolve b.program (rootPoint compileFuel)) :=
  resolve_scoped _ (atomic_built_fragment b built) _ rfl

/-- Every actual queue history retains its source fields for every job count and budget. -/
theorem queue_history_at (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b)
    (m : NativeMachine) (history : Effect4.Run.ControlHistory b compileFuel m) : ConfigurationAt b.program m :=
  history_at b (queue_built_fragment total b built) compileFuel m history

/-- Every actual shop history retains its source fields at every budget. -/
theorem atomic_history_at (compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b)
    (m : NativeMachine) (history : Effect4.Run.ControlHistory b compileFuel m) : ConfigurationAt b.program m :=
  history_at b (atomic_built_fragment b built) compileFuel m history

/-- The actual queue's write-site laws retain their cell predicate through every control history. -/
theorem queue_heap_at (total compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (QueueWorkers.crew total) = .ok b) (P : Effect4.Store.Val → Prop)
    (sites : HeapSites.SitesKeep b.program P) (m : NativeMachine)
    (history : Effect4.Run.ControlHistory b compileFuel m) : HeapSites.HeapOk P m.state.refs :=
  heap_history_at b (queue_built_fragment total b built) compileFuel P sites m history

/-- The actual shop's write-site laws retain their cell predicate through every control history. -/
theorem atomic_heap_at (compileFuel : Nat) (b : Api.Built)
    (built : Api.Author.build (Atomic.shop .none) = .ok b) (P : Effect4.Store.Val → Prop)
    (sites : HeapSites.SitesKeep b.program P) (m : NativeMachine)
    (history : Effect4.Run.ControlHistory b compileFuel m) : HeapSites.HeapOk P m.state.refs :=
  heap_history_at b (atomic_built_fragment b built) compileFuel P sites m history

end Test.Dogfood.Scenario.SourceFragment
