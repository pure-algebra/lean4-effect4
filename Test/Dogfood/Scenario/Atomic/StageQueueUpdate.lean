import Test.Dogfood.Scenario.Atomic.StageReplies
import Test.Dogfood.Scenario.Atomic.StageNativeWords

/-!
Concept: reactive-scheduling R11.
Consumer: Atomic's actual fixed-command and native queue postconditions.
The existing command owner certificate excludes the overwritten actor from the pending suffix.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageConfiguration
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- Actor installation retains every certified row at another actual owner. -/
theorem owner_update (machine : NativeMachine) (actor : SourceScope.SourceFiber) (id : FiberId)
    (different : id ≠ actor.id) (P : SourceScope.SourceFiber → Prop)
    (held : ∀ row ∈ machine.fibers, row.id = id → P row) :
    ∀ row ∈ (machine.update actor).fibers, row.id = id → P row := by
  intro row member identity
  obtain ⟨old, inside, same⟩ := List.mem_map.mp member
  rw [← same] at identity ⊢
  by_cases changed : old.id = actor.id
  · rw [if_pos changed] at identity
    exact False.elim (different identity.symm)
  · rw [if_neg changed] at identity ⊢
    exact held old inside identity

/-- An installed unparked actor cannot consume an old matching-token reply. -/
theorem ReplyPermission.update_unparked (machine : NativeMachine) (actor : SourceScope.SourceFiber)
    (unparked : actor.parked = .notParked) (id : FiberId) (token : Nat) (code : NCode)
    (held : ReplyPermission machine id token code) : ReplyPermission (machine.update actor) id token code :=
  held.update_origin machine actor (fun token parked => by rw [unparked] at parked; cases parked) id token code

/-- Actual pending owners retain all their certificates when another actor is overwritten. -/
theorem QueueAt.update_other (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (actor : SourceScope.SourceFiber) (commands : List Guard.NCmd)
    (held : QueueAt root table world machine commands)
    (away : ∀ id ∈ commands.filterMap (Guard.commandOwner machine), id ≠ actor.id)
    (reply : ∀ id token code, .resume id token code ∈ commands →
      ReplyPermission machine id token code → ReplyPermission (machine.update actor) id token code) :
    QueueAt root table world (machine.update actor) commands := by
  apply held.transport root table world world (order.refl world) machine (machine.update actor) commands
  · intro id member live
    exact owner_update machine actor id (away id member) _ live
  · intro id member empty
    exact owner_update machine actor id (away id member) _ empty
  · exact reply
  · intro id kind member receiving
    exact owner_update machine actor id (away id member) _ receiving

/-- Updating one actual row transports a reader using its actual replacement certificate. -/
theorem owner_update_with (machine : NativeMachine) (first last : SourceScope.SourceFiber)
    (same : last.id = first.id) (id : FiberId) (P : SourceScope.SourceFiber → Prop)
    (held : ∀ row ∈ machine.fibers, row.id = id → P row)
    (changed : first.id = id → P last) :
    ∀ row ∈ (machine.update last).fibers, row.id = id → P row := by
  intro row member identity
  obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
  rw [← equal] at identity ⊢
  by_cases replaced : old.id = last.id
  · rw [if_pos replaced] at identity ⊢
    exact changed (same.symm.trans identity)
  · rw [if_neg replaced] at identity ⊢
    exact held old inside identity

/-- Retaining each actual row's identity, frame and park retains all queued readers. -/
theorem QueueAt.row_origin (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (first last : NativeMachine) (commands : List Guard.NCmd)
    (origin : ∀ row ∈ last.fibers, ∃ old ∈ first.fibers,
      row.id = old.id ∧ row.frame = old.frame ∧ row.parked = old.parked)
    (held : QueueAt root table world first commands) : QueueAt root table world last commands := by
  apply held.transport root table world world (order.refl world) first last commands
  · intro id pending live row member identity
    obtain ⟨old, inside, sameId, sameFrame, samePark⟩ := origin row member
    rw [sameId, sameFrame]
    exact live old inside (sameId.symm.trans identity)
  · intro id pending empty row member identity
    obtain ⟨old, inside, sameId, sameFrame, samePark⟩ := origin row member
    rw [sameFrame]
    exact empty old inside (sameId.symm.trans identity)
  · intro id token code pending reply row member identity parked
    obtain ⟨old, inside, sameId, sameFrame, samePark⟩ := origin row member
    exact reply old inside (sameId.symm.trans identity) (samePark.symm.trans parked)
  · intro id kind pending receiving row member identity
    obtain ⟨old, inside, sameId, sameFrame, samePark⟩ := origin row member
    rw [sameFrame]
    exact receiving old inside (sameId.symm.trans identity)

/-- Actual observer installation preserves every waiting reader. -/
theorem QueueAt.observe (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (target : FiberId) (observer : Observer)
    (commands : List Guard.NCmd) (held : QueueAt root table world machine commands) :
    QueueAt root table world (machine.observe target observer) commands := by
  apply held.row_origin root table world machine _ commands
  unfold RunMachine.observe RunMachine.modify
  split
  · intro row member
    exact ⟨row, member, rfl, rfl, rfl⟩
  · intro row member
    obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
    rw [← equal]
    split
    · rename_i fiber found same
      exact ⟨fiber, RunMachine.mem_of_fiber? found, rfl, rfl, rfl⟩
    · exact ⟨old, inside, rfl, rfl, rfl⟩

/-- Actual observer removal preserves every waiting reader. -/
theorem QueueAt.drop (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (token : Nat) (commands : List Guard.NCmd)
    (held : QueueAt root table world machine commands) :
    QueueAt root table world (machine.dropToken token) commands := by
  apply held.row_origin root table world machine _ commands
  intro row member
  obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact ⟨old, inside, rfl, rfl, rfl⟩

/-- Actual admitted interruption retains every waiting command's existing reader. -/
theorem QueueAt.interruption (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (member : fiber ∈ machine.fibers)
    (cause : CauseV) (commands : List Guard.NCmd)
    (configuration : Configuration root table world machine)
    (untyped : ∀ reason ∈ cause.reasons, reason.tag ≠ .fail) (marked : MarkedCause cause)
    (held : QueueAt root table world machine commands) :
    QueueAt root table world (machine.update (interruptWithCause cause fiber).1) commands := by
  have fields := interruption_fields fiber cause
  apply held.transport root table world world (order.refl world) machine _ commands
  · intro id pending live
    apply owner_update_with machine fiber _ fields.1 id _ live
    intro identity
    exact live_interruption root table world fiber cause (live fiber member identity)
      (configuration.metadata fiber member).recorded untyped marked
  · intro id pending empty
    apply owner_update_with machine fiber _ fields.1 id _ empty
    intro identity
    exact (interruption_stack fiber cause).trans (empty fiber member identity)
  · intro id token code pending reply
    exact reply.interruption machine fiber member cause id token code
  · intro id kind pending receiving
    apply owner_update_with machine fiber _ fields.1 id _ receiving
    intro identity
    have original := receiving fiber member identity
    constructor
    · intro rootId
      exact RootGraph.AfterAt.stack root table world kind fiber.frame _ (interruption_stack fiber cause)
        (original.1 rootId)
    · intro daemonId
      exact DaemonGraph.interruption_frame root table world fiber cause (original.2 daemonId)

/-- Outcome bookkeeping retains every queued reader of the installed actor's unchanged frame. -/
theorem QueueAt.installed_fields (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (first last : SourceScope.SourceFiber) (commands : List Guard.NCmd)
    (sameId : last.id = first.id) (sameFrame : last.frame = first.frame)
    (park : ∀ token, last.parked = .withGuard token → first.parked = .withGuard token)
    (held : QueueAt root table world (machine.update first) commands) :
    QueueAt root table world (machine.update last) commands := by
  have origin : ∀ row ∈ (machine.update last).fibers,
      ∃ old ∈ (machine.update first).fibers, row.id = old.id ∧ row.frame = old.frame ∧
        (∀ token, row.parked = .withGuard token → old.parked = .withGuard token) := by
    intro row member
    obtain ⟨old, inside, equal⟩ := List.mem_map.mp member
    rw [← equal]
    by_cases changed : old.id = last.id
    · rw [if_pos changed]
      refine ⟨first, List.mem_map.mpr ⟨old, inside, ?_⟩, sameId, sameFrame, park⟩
      exact if_pos (changed.trans sameId)
    · rw [if_neg changed]
      refine ⟨old, List.mem_map.mpr ⟨old, inside, ?_⟩, rfl, rfl, fun _ actual => actual⟩
      exact if_neg (fun identity => changed (identity.trans sameId.symm))
  apply held.transport root table world world (order.refl world) _ _ commands
  · intro id pending live row member identity
    obtain ⟨old, inside, equalId, equalFrame, samePark⟩ := origin row member
    rw [equalId, equalFrame]
    exact live old inside (equalId.symm.trans identity)
  · intro id pending empty row member identity
    obtain ⟨old, inside, equalId, equalFrame, samePark⟩ := origin row member
    rw [equalFrame]
    exact empty old inside (equalId.symm.trans identity)
  · intro id token code pending reply row member identity parked
    obtain ⟨old, inside, equalId, equalFrame, samePark⟩ := origin row member
    exact reply old inside (equalId.symm.trans identity) (samePark token parked)
  · intro id kind pending receiving row member identity
    obtain ⟨old, inside, equalId, equalFrame, samePark⟩ := origin row member
    rw [equalFrame]
    exact receiving old inside (equalId.symm.trans identity)

/-- Actual admitted messages retain queued readers and classify their emitted evaluation request. -/
theorem QueueAt.edit (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (machine : NativeMachine) (commands : List Guard.NCmd) (message : FiberEdit Err Defect FiberId Ann)
    (configuration : Configuration root table world machine) (admitted : MessageAt message)
    (held : QueueAt root table world machine commands) :
    QueueAt root table world (applyFiberEdit message machine).1
      (commands ++ (applyFiberEdit message machine).2) := by
  cases message with
  | observe target observer =>
    simpa only [applyFiberEdit, List.append_nil] using held.observe root table world machine target observer commands
  | dropToken token =>
    simpa only [applyFiberEdit, List.append_nil] using held.drop root table world machine token commands
  | interrupt target cause =>
    cases found : machine.fiber? target with
    | none => simpa only [applyFiberEdit, found, List.append_nil] using held
    | some fiber =>
      have retained := held.interruption root table world machine fiber (RunMachine.mem_of_fiber? found)
        cause commands configuration admitted.1 admitted.2
      intro command member
      simp only [applyFiberEdit, found, List.mem_append] at member ⊢
      rcases member with prior | added
      · exact retained command prior
      · split at added
        · cases List.mem_singleton.mp added
          exact .evaluate target
        · cases added

end Test.Dogfood.Scenario.Atomic.StageConfiguration
