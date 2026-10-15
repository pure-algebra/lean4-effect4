import Effect4.Laws.Program.FinalizerConfigurationNative
import Effect4.Laws.Program.CodeClosure.ConfigurationAdministration
import Effect4.Laws.Program.CodeClosure.ConfigurationHistory

/-!
Concept: scope-lifetime-finalization R11.
Question: full source locations serve FinalizerRun.once_placed_outside_census.
Consumer: the source ledger over every raw native decision history.
The full annotation supplies local facts to the existing configuration transport.
This invariant establishes source ownership, not release custody or a registration bound.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Actual observer replies are terminal; scope removal retains the captured templates. -/
theorem configuration_observers (root : NativeEff) (q : List Nat) (table : RowTable) :
    CodeClosure.Configuration.ObserverFacts (configurationModel q) root table where
  failure := fun _ => ⟨trivial, trivial, trivial⟩
  exitValue := fun exit mode => terminal_template q _ (SourceScope.exit_value_reply root [] table exit mode)
  countdown := fun resume exits held => terminal_template q _
    (SourceScope.countdown_program_reply root [] table resume exits held)
  raceSettle := fun race cleanup exit _ => terminal_template q _ (SourceScope.race_settle_reply root table race cleanup exit)
  drop := (ScopeFields.command_hooks (scopeModel q) (fun _ _ => True.intro) root [] table).drop

/-- A due completion carries only its actual terminal reply program. -/
theorem configuration_due (root : NativeEff) (q : List Nat) (table : RowTable)
    (state : Stores) (held : ScopesAt q state.scopes) :
    ScopesAt q ((interpOf root table).dueResumes state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).dueResumes state).1,
        TemplateAt q owed.code ∧ SourceScope.TerminalReply owed.code := by
  refine ⟨held, ?_⟩
  intro owed member
  obtain ⟨completion, _, same⟩ := List.mem_map.mp member
  rw [← same]
  have reply := SourceScope.completion_reply completion.code
  exact ⟨terminal_template q _ reply, reply⟩

/-- Actual administrative waits restore their original result without a source callback. -/
theorem configuration_await (root : NativeEff) (q : List Nat) (table : RowTable)
    (machine : NativeMachine) (kind : ParkKind) :
    TemplateAt q (asVoidCode (interpOf root table) (awaitCode (interpOf root table) machine kind)) := by
  have awaited := await_template root q table machine kind
  change TemplateAt q (.onSuccess (awaitCode (interpOf root table) machine kind) (.restore (.success .unit)))
  aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt,
    CodeClosure.RegistrationBody, NameAt, OrdinaryNameAt, CodeClosure.Slots.NameAt,
    CodeClosure.Qualified.NameAt])

/-- Exit cleanup introduces only its actual child-interruption program and result restore. -/
theorem configuration_children (root : NativeEff) (q : List Nat) (table : RowTable)
    (fiber : SourceScope.SourceFiber) (exit : ExitV) :
    TemplateAt q (.onSuccess ((interpOf root table).interruptAllCode fiber.children)
      ((interpOf root table).restoreName exit)) := by
  change TemplateAt q (.onSuccess
    (.withFiber (.store (.act (.interruptAll fiber.children none)))) (.restore exit))
  aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt,
    CodeClosure.RegistrationBody, NameAt, OrdinaryNameAt, ThunkAt,
    CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt,
    CodeClosure.Qualified.ThunkAt, CodeClosure.Qualified.StoreThunkAt,
    CodeClosure.Qualified.StoreActionAt])

/-- Full source annotations instantiate the shared command proof at every code location. -/
theorem configuration_commands (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.Configuration.CommandFacts (configurationModel q) root table where
  iteration := iteration_configuration root q table placed
  native := native_configuration root q table placed
  settle := CodeClosure.Configuration.settle_at (configurationModel q) root (fun _ => ⟨trivial, trivial, trivial⟩)
  observer := CodeClosure.Configuration.observer_at (configurationModel q) root table
    (configuration_observers root q table)
  due := configuration_due root q table
  drain := CodeClosure.Configuration.drain_at (configurationModel q)
  raceSettle := fun race cleanup exit _ => terminal_template q _ (SourceScope.race_settle_reply root table race cleanup exit)
  cancel := by intros; trivial
  interruption := CodeClosure.Configuration.interrupt_cause_at (configurationModel q) (fun _ => ⟨trivial, trivial, trivial⟩)
  awaitRestore := configuration_await root q table
  park := by intros; trivial
  closeDone := by trivial
  link := CodeClosure.Configuration.link_at (configurationModel q) root [] table
    (fun _ => ⟨trivial, trivial, trivial⟩)
    (ScopeFields.command_hooks (scopeModel q) (fun _ _ => True.intro) root [] table).link
  exit := CodeClosure.Configuration.exit_fiber_at (configurationModel q) root table
    (configuration_children root q table)

/-- Clock completions carry the same terminal permission as due completions. -/
theorem configuration_clock (root : NativeEff) (q : List Nat) (table : RowTable)
    (millis : ClockMillis) (state : Stores) (held : ScopesAt q state.scopes) :
    ScopesAt q ((interpOf root table).clockStep millis state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).clockStep millis state).1,
        TemplateAt q owed.code ∧ SourceScope.TerminalReply owed.code := by
  refine ⟨held, ?_⟩
  intro owed member
  rw [Option.mem_def] at member
  obtain ⟨completion, _, same⟩ := Option.map_eq_some_iff.mp member
  rw [← same]
  have reply := SourceScope.completion_reply completion.code
  exact ⟨terminal_template q _ reply, reply⟩

/-- Every raw decision retains the full source configuration, including prepared host replies. -/
theorem configuration_lift (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ machine => CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
      (fun _ _ commands => CodeClosure.Configuration.CommandsAt (configurationModel q) commands)
      (fun _ _ tasks => CodeClosure.Configuration.TasksAt (configurationModel q) tasks)
      (fun _ _ _ => True) := by
  apply CodeClosure.Configuration.decision_lift (configurationModel q) root table
    (configuration_commands root q table placed) (fun _ => True) (configuration_clock root q table)
  intro machine id token answer owned _
  have prepared := SourceScope.prepare_reply_at root table machine id token answer
  refine ⟨⟨owned.fibers, owned.races, ?_⟩, terminal_template q _ prepared.2.2, prepared.2.2⟩
  rw [prepared.1]
  exact owned.scopes

/-- Initial load has only the compiled source root and no saved metadata. -/
theorem configuration_load (root : NativeEff) (q : List Nat) (compileFuel : Nat) :
    CodeClosure.Configuration.ConfigurationAt (configurationModel q) (Api.load root compileFuel) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fiber member
    rw [List.mem_singleton.mp member]
    apply CodeClosure.Configuration.fiber_make_at
    exact resolve_at root q (rootPoint compileFuel) (by intro point member; cases member)
  · intro race member; cases member
  · intro scope member; cases member

/-- The full source configuration follows every raw native history at every explicit budget. -/
theorem configuration_reachable (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (compileFuel : Nat) (machine : NativeMachine)
    (reached : Guard.Reachable root table compileFuel machine) :
    CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine := by
  apply Guard.reachable_lift_pure root table compileFuel
    (CodeClosure.Configuration.ConfigurationAt (configurationModel q))
    (configuration_load root q compileFuel) ?_ machine reached
  intro before fuel decision held
  letI := evaluatorFor root table
  obtain ⟨_, _, kept⟩ := Lift.stepDecisionState_lift (configuration_lift root q table placed)
    fuel () before decision held trivial
  exact kept

end Effect4.Program.FinalizerSource
