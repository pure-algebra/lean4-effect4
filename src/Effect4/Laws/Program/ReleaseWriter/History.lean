import Effect4.Laws.Program.ReleaseWriter.Iteration
import Effect4.Laws.Program.PlaceFunding.FlowGuarded
import Effect4.Laws.Program.NativeHeapReplies

/-!
Concept: scope-lifetime-finalization R11.
Question: both crews use one local writer contract and one funded-history reading.
Reach: direct programs with sequential scopes and no races, under their actual-write invariant.
Consumers: CrewLogHistory and the two application log goals.
The application still owes value flow and closure of its carried invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
universe w

/-- The store hooks leave the reference heap, so they leave the writer's heap count. -/
theorem stores (target : Target) (root : NativeEff) (table : RowTable) :
    PlaceFunding.StoreHooks (ledger target) (interpOf root table) where
  link := by
    intro mode scope owner before after key found
    exact state_le_of_refs target before after (scope_link_refs root table mode scope owner before after key found)
  drop := by
    intro scope key before after found
    exact state_le_of_refs target before after (drop_refs root table scope key before after found)
  due := fun _ => Nat.le_refl _
  wake := by
    intro list phase before
    change (ledger target).state (Stores.wakeList list phase before) ≤ (ledger target).state before
    unfold Stores.wakeList
    split <;> exact Nat.le_refl _

/-- A wait's native answer carries no note reservation. -/
theorem await_code_zero (target : Target) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (kind : ParkKind) : Free target (awaitCode (interpOf root table) m kind) := by
  unfold awaitCode
  split
  · split
    · rename_i owner mode _ exit _
      cases mode
      · rfl
      · cases exit <;> rfl
    · rfl
  · rfl

/-- The administrative codes and frames of the native interpreter carry no note reservation. -/
theorem administration (target : Target) (root : NativeEff) (table : RowTable) :
    PlaceFunding.Administration (ledger target) (Free target) (interpOf root table) where
  race := fun race cleanup exit => terminal_zero target _ (race_settle_reply root table race cleanup exit)
  await := by
    intro m kind
    change current target (awaitCode (interpOf root table) m kind) + 0 = 0
    rw [await_code_zero target root table m kind, Nat.add_zero]
  children := fun _ _ => rfl
  park := fun _ => rfl
  cancel := by
    intro fiber race token
    change current target fiber.frame.current +
        (0 + (fiber.frame.stack.map (saved target)).sum) ≤ frame target fiber.frame
    simp only [Nat.zero_add, frame, FrameWeights.frame, model, Nat.le_refl]
  iterator := by
    intro fiber
    change current target fiber.frame.current +
        (0 + (fiber.frame.stack.map (saved target)).sum) ≤ frame target fiber.frame
    simp only [Nat.zero_add, frame, FrameWeights.frame, model, Nat.le_refl]

/-- The code a command imports is free: a reply is a native reply, and a race-free source
stores no race. -/
theorem inputs (target : Target) (root : NativeEff) (m : NativeMachine) (command : SourceCommand)
    (raceFree : RaceFreeSource root) (owned : ConfigurationAt root m)
    (head : CommandAt root command) : PlaceFunding.Inputs (Free target) m command where
  reply := by
    intro owner token code selected
    subst command
    exact terminal_zero target code head.2
  entrant := by
    intro raceId race code rest selected found programs
    have empty := Opportunities.races_nil root m raceFree owned
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found

/-- One writer instance supplies all command funding facts from actual initialized writes. -/
theorem local_facts {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (Q : NativeMachine → Prop)
    (writes : ∀ m fiber, Q m → m.fiber? fiber.id = some fiber → SyncBound target root table m fiber.frame.current)
    (carry : ∀ m owner token answer, Q m →
      Q {m with state := (prepareAsyncAnswer (interpOf root table) m owner token answer).1}) :
    PlaceFunding.LocalOn (ledger target) (Free target) root table Q where
  control := control target
  quiet := no_queue target
  events := events target
  stores := stores target root table
  admin := administration target root table
  evaluation := evaluation source table sequential raceFree Q writes
  inputs := fun m command owned _ head => inputs target root m command raceFree owned head
  clock := fun _ _ => Nat.le_refl _
  prepare := fun m owner token answer => state_le_of_refs target m.state _
    (prepare_reply_refs root table m owner token answer)
  carry := carry

/-- The shared ledger reads committed identities and pending writes against recorded releases. -/
theorem funded_reading (target : Target) (cap : Nat) (m : NativeMachine) :
    (ledger target).Funded cap m [] [] ↔
      (log target m.state).count target.value + (m.fibers.map fun fiber => frame target fiber.frame).sum ≤
        issued target m + cap := by
  simp only [PlaceLedger.Funded, PlaceLedger.spent, PlaceLedger.held, PlaceLedger.issued, ledger,
    PlaceLedger.zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    FinalizerCredits.indicator_sum, FiberSum.total, issued]

/-- The root cannot itself be a selected acquisition's release child. -/
theorem leaf_root (target : Target) : leaf target [] = 0 := by
  unfold leaf
  split
  · rename_i equal
    have lengths := congrArg List.length equal
    simp only [List.length_nil, List.length_append, List.length_cons] at lengths
    omega
  · rfl

/-- Initial loading has no committed log identity and no pending release write. -/
theorem load_funded {target : Target} {root : NativeEff} (source : Source target root) (compileFuel : Nat) :
    (ledger target).Funded 0 (Api.load root compileFuel) [] [] := by
  apply (funded_reading target 0 (Api.load root compileFuel)).mpr
  have compiled := source.compile_bound root (rootPoint compileFuel) rfl
  change current target (compileEff root (rootPoint compileFuel)) ≤ leaf target [] at compiled
  rw [leaf_root] at compiled
  have heap : (log target (Api.load root compileFuel).state).count target.value = 0 := rfl
  have starts : issued target (Api.load root compileFuel) = 0 := rfl
  have rows : ((Api.load root compileFuel).fibers.map fun fiber => frame target fiber.frame).sum =
      current target (compileEff root (rootPoint compileFuel)) := rfl
  rw [heap, starts, rows, Nat.zero_add, Nat.add_zero]
  exact compiled

/-- A funded writer ledger bounds each committed log identity by its recorded releases. -/
theorem committed_le (target : Target) (m : NativeMachine) (funded : (ledger target).Funded 0 m [] []) :
    (log target m.state).count target.value ≤ issued target m := by
  have bound := (funded_reading target 0 m).mp funded
  omega

/-- The shared writer follows a guarded driver through every admitted history.
The queue and detached-task assertions remain those of the supplied driver. -/
theorem history_funded {W : Type w} {target : Target} (b : Api.Built)
    (source : Source target b.program) (sequential : SequentialSource b.program)
    (raceFree : RaceFreeSource b.program) (Q : NativeMachine → Prop)
    (writes : ∀ m fiber, Q m → m.fiber? fiber.id = some fiber →
      SyncBound target b.program b.table m fiber.frame.current)
    (carry : ∀ m owner token answer, Q m →
      Q {m with state := (prepareAsyncAnswer (interpOf b.program b.table) m owner token answer).1})
    (order : Effect4.Laws.Effects.WorldOrder W)
    (I : W → NativeMachine → List SourceCommand → Prop)
    (O : W → NativeMachine → List SourceTask → Prop)
    (A : W → NativeMachine → NativeDecision → Prop)
    (commands : ∀ world m queue, I world m queue → CommandsAt b.program queue)
    (carried : letI := evaluatorFor b.program b.table
      Lift.DecisionLift order (interpOf b.program b.table)
        (fun _ m => ConfigurationAt b.program m ∧ Q m) I O A)
    (admission : ∀ world m d, ConfigurationAt b.program m → Q m →
      Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m d → A world m d)
    (compileFuel : Nat) (load : ∃ _world : W, Q (Api.load b.program compileFuel))
    (m : NativeMachine) (reached : Run.HistoryOf b compileFuel m) :
    (ledger target).Funded 0 m [] [] := by
  obtain ⟨initial, loaded⟩ := load
  have facts := local_facts source b.table sequential raceFree Q writes carry
  have kept := Run.history_keeps b compileFuel
    (fun m => ∃ world : W, (ConfigurationAt b.program m ∧ Q m) ∧ PlaceFunding.Holds (ledger target) 0 m)
    ⟨initial, ⟨load_at b.program source.fragment compileFuel, loaded⟩,
      ForkLedger.Invariant.load_ok b.program compileFuel, load_funded source compileFuel⟩
    (fun before row held accepted => ?_) m reached
  · obtain ⟨_, _, funded⟩ := kept
    exact funded.2
  · letI := evaluatorFor b.program b.table
    obtain ⟨world, invariant, funded⟩ := held
    obtain ⟨later, _, after⟩ := Lift.stepDecisionState_lift
      (facts.guarded_decision_lift 0 order I O A commands carried)
      row.1 world before row.2 ⟨invariant, funded⟩
      (admission world before row.2 invariant.1 invariant.2 accepted)
    exact ⟨later, after⟩

end Effect4.Program.ReleaseWriter
