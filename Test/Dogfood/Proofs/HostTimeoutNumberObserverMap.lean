import Test.Dogfood.Proofs.HostTimeoutNumberQueueInterrupt

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: observer-only metadata edits retain the joined numeric assertions.
Consumer: actual observe and token-drop branches of the shared contextual message producer.
Reach: one observer-field map over the existing fiber table, retaining all other machine fields.
Limit: source callback execution and native role advancement remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberObserverMap
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration HostTimeoutNumberConfigurationTransport
open HostTimeoutNumberQueueInterrupt

/-- Both actual observer edits map only the existing records' observer field. -/
def mapped (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) : Effect4.Program.NativeMachine :=
  {machine with fibers := machine.fibers.map fun fiber => {fiber with observers := observers fiber}}

/-- The actual lookup maps the same found row and retains its identity. -/
theorem lookup (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (id : FiberId) :
    (mapped machine observers).fiber? id =
      (machine.fiber? id).map (fun fiber => {fiber with observers := observers fiber}) := by
  unfold mapped RunMachine.fiber?
  rw [List.find?_map]
  rfl

/-- Observer-only maps retain the exact ordered completed-exit view. -/
theorem view (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) :
    (mapped machine observers).completedExits = machine.completedExits := by
  unfold mapped RunMachine.completedExits
  rw [List.filterMap_map]
  rfl

/-- Observer-only maps retain the base driver's unique fiber identifiers. -/
theorem ids (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) :
    ((mapped machine observers).fibers.map (·.id)) = machine.fibers.map (·.id) := by
  unfold mapped
  rw [List.map_map]
  rfl

/-- The actual live-token reply retains the same current code, mask, and saved suffix. -/
theorem reply (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (id : FiberId) (token : Nat) (code : NCode)
    (held : ReplyAt world machine id token code) : ReplyAt world (mapped machine observers) id token code := by
  intro fiber found live parked role assigned
  rw [lookup] at found
  cases original : machine.fiber? id with
  | none => simp only [original, Option.map_none] at found; cases found
  | some old =>
      simp only [original, Option.map_some] at found
      cases found
      exact frame_machine machine _ role _ rfl (view machine observers) (held old original live parked role assigned)

/-- An observer-field change retains each actual numeric fiber permission. -/
theorem fiber_observers (machine : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (observers : List Observer)
    (held : FiberAt machine role fiber) : FiberAt machine role {fiber with observers} := by
  constructor
  · exact held.frame
  · exact held.exit
  · exact held.retired
  · exact held.recorded
  · exact held.immediate
  · exact held.pendingRunning

/-- Observer-only maps retain the complete numeric machine assertion and stored reply tasks. -/
theorem configuration (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (held : Configuration world machine) :
    Configuration world (mapped machine observers) := by
  constructor
  · exact held.heap
  · intro fiber member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    obtain ⟨role, assigned, good⟩ := held.roles old present
    exact ⟨role, assigned, fiber_machine machine _ role _ rfl (view machine observers)
      (fiber_observers machine role old (observers old) good)⟩
  · exact held.unique
  · intro fiber member bucket stored
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal] at stored
    exact snapshot_replies world machine _ bucket.tasks
      (fun id token code good => reply world machine observers id token code good)
      (held.dispatchers old present bucket stored)

/-- A queued loop reads exactly the same execution and mask fields after an observer-only map. -/
theorem loop (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (id : FiberId) (yielding : Bool)
    (held : CommandAt world machine (.loop id yielding)) :
    CommandAt world (mapped machine observers) (.loop id yielding) := by
  intro count assigned heap fiber found installed
  rw [lookup] at found
  cases original : machine.fiber? id with
  | none => simp only [original, Option.map_none] at found; cases found
  | some old =>
      simp only [original, Option.map_some] at found
      cases found
      exact held count assigned heap old original installed

/-- The observer map retains the actual target existence and exit facts used by cancellation. -/
theorem target (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (id : FiberId) :
    ((∃ old, machine.fiber? id = some old) → ∃ fiber, (mapped machine observers).fiber? id = some fiber) ∧
    (∀ fiber, (mapped machine observers).fiber? id = some fiber →
      ∃ old, machine.fiber? id = some old ∧ fiber.exit = old.exit) := by
  constructor
  · rintro ⟨old, original⟩
    exact ⟨_, by rw [lookup, original]; rfl⟩
  · intro fiber found
    rw [lookup] at found
    cases original : machine.fiber? id with
    | none => simp only [original, Option.map_none] at found; cases found
    | some old =>
        simp only [original, Option.map_some] at found
        cases found
        exact ⟨old, rfl, rfl⟩

/-- Cancellation's cleanup barrier retains its actual target exits through the observer map. -/
theorem cleanup_await (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (targets : List FiberId)
    (held : CleanupAwait machine targets) : CleanupAwait (mapped machine observers) targets := by
  rcases held with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl ready
  · refine Or.inr ⟨attempt, member, (target machine observers attempt).1 present, ?_⟩
    intro fiber found published
    obtain ⟨old, original, same⟩ := (target machine observers attempt).2 fiber found
    exact complete old original (same ▸ published)

/-- The earlier cleanup-image barrier reads the same retained target exits. -/
theorem await (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (targets : List FiberId)
    (image : HostTimeoutNumberFlow.Image) (own : image.count = image.cleanups.length + 1)
    (held : HostTimeoutNumberWait.AwaitAt image own machine targets) :
    HostTimeoutNumberWait.AwaitAt image own (mapped machine observers) targets := by
  rcases held with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl ready
  · refine Or.inr ⟨attempt, member, (target machine observers attempt).1 present, ?_⟩
    intro fiber found published
    obtain ⟨old, original, same⟩ := (target machine observers attempt).2 fiber found
    exact complete old original (same ▸ published)

/-- Observer-only edits retain actual drained-stack permission for a pending finish. -/
theorem terminal (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (id : FiberId)
    (held : TerminalStack machine id) : TerminalStack (mapped machine observers) id := by
  intro fiber found
  rw [lookup] at found
  cases original : machine.fiber? id with
  | none => simp only [original, Option.map_none] at found; cases found
  | some old =>
      simp only [original, Option.map_some] at found
      cases found
      exact held old original

/-- Every pending numeric command shares the existing single assertion transport. -/
theorem commands (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (pending : List Guard.NCmd)
    (held : Commands world machine pending) : Commands world (mapped machine observers) pending := by
  intro command member
  exact command_transport world machine _ pending command member (held command member)
    (reply world machine observers)
    (fun id yielding queued good => loop world machine observers id yielding good)
    (fun id selected good => ⟨terminal machine observers id good.1,
      fun role assigned => exit_machine machine _ role selected rfl (view machine observers) (good.2 role assigned)⟩)
    (by
      intro host yielding kind member good
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
          exact ⟨fun image own suffix assigned => await machine observers targets image own (good.1 image own suffix assigned),
            fun suffix assigned => cleanup_await machine observers targets (good.2 suffix assigned)⟩)
    (by
      intro race host yielding remaining visited member good
      exact ⟨fun image own suffix assigned => await machine observers (remaining ++ visited) image own (good.1 image own suffix assigned),
        fun suffix assigned => cleanup_await machine observers (remaining ++ visited) (good.2 suffix assigned)⟩)

/-- Protected queued prefixes retain their actual lookup and installed finalizer. -/
theorem protects (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer) (pending : List Guard.NCmd)
    (held : Protects context world machine pending) : Protects context world (mapped machine observers) pending := by
  intro id count yielding fiber assigned heap found installed queued
  rw [lookup] at found
  cases original : machine.fiber? id with
  | none => simp only [original, Option.map_none] at found; cases found
  | some old =>
      simp only [original, Option.map_some] at found
      cases found
      exact held id count yielding old assigned heap original installed queued


/-- Actual observer registration is the same observer-field map at the uniquely addressed row. -/
theorem observe_mapped (machine : Effect4.Program.NativeMachine) (target : FiberId) (observer : Observer)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (found : machine.fiber? target = some fiber)
    (unique : (machine.fibers.map (·.id)).Nodup) :
    machine.observe target observer = mapped machine
      (fun old => if old.id = target then old.observers ++ [observer] else old.observers) := by
  simp only [RunMachine.observe, RunMachine.modify, found]
  unfold RunMachine.update mapped
  congr 1
  apply List.map_congr_left
  intro old member
  change (if old.id = fiber.id then {fiber with observers := fiber.observers ++ [observer]} else old) =
    {old with observers := if old.id = target then old.observers ++ [observer] else old.observers}
  have key := RunMachine.id_of_fiber? found
  split
  · rename_i same
    have oldKey : old.id = target := same.trans key
    have lookup := Effect4.Machine.fiber_lookup_of_mem_nodup machine unique old member
    rw [oldKey, found] at lookup
    have equal : fiber = old := Option.some.inj lookup
    rw [← equal, if_pos key]
  · rename_i other
    have different : old.id ≠ target := by intro equal; exact other (equal.trans key.symm)
    rw [if_neg different]

/-- The actual token removal is an observer-field map, including on duplicate raw rows. -/
theorem drop_mapped (machine : Effect4.Program.NativeMachine) (token : Nat) :
    machine.dropToken token = mapped machine (fun fiber => fiber.observers.filter fun
      | .resumeAwait _ guarded _ => guarded ≠ token
      | .countdown _ guarded => guarded ≠ token
      | _ => true) := rfl

end Test.Dogfood.Proofs.HostTimeoutNumberObserverMap
