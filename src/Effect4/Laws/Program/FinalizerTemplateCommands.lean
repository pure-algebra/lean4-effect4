import Effect4.Laws.Program.FinalizerSourceCommands
import Effect4.Laws.Machine.AnswerFlowRun

/-!
Concept: scope-lifetime-finalization, R11.
Question: the full source annotation serves once_placed_outside_census.
Consumer: the full source configuration through the existing decision lift.
The common answer-flow command theorem carries current and saved templates.
Race programs, scope captures and terminal replies remain explicit premises.
This local theorem establishes no history bound or release custody.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- The existing command producer reads annotations at actual race and reply slots. -/
def CommandReady (q : List Nat) (machine : NativeMachine) (command : SourceScope.SourceCommand) : Prop :=
  ScopesAt q machine.state.scopes ∧
    (∀ race ∈ machine.races, ∀ code ∈ race.programs, TemplateAt q code) ∧
    (∀ owner token code, command = .resume owner token code → SourceScope.TerminalReply code)

/-- The native wait exposes a terminal exit or a represented park. -/
theorem await_template (root : NativeEff) (q : List Nat) (table : RowTable)
    (machine : NativeMachine) (kind : ParkKind) :
    TemplateAt q (awaitCode (interpOf root table) machine kind) := by
  apply awaitCode_closed (interpOf root table) (TemplateAt q)
  · intro exit mode
    cases exit <;> cases mode <;> trivial
  · intro kind
    trivial

/-- Full templates instantiate the existing command census once. -/
theorem template_commands (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    letI := evaluatorFor root table
    AnswerFlow.Commands (interpOf root table) (CommandReady q)
      (fun (_ : Unit) _ frame => TemplateFrame q frame) (fun _ _ => ()) := by
  letI := evaluatorFor root table
  refine {
    iteration := ?_, deliver := ?_, interruption := ?_, resume := ?_, entrant := ?_,
    settleRace := ?_, parkRace := ?_, afterInterrupt := ?_, closePar := ?_, exitChildren := ?_,
    publish := ?_, cleared := ?_, link := ?_, drop := ?_, due := ?_, wake := ?_ }
  · intro machine fiber yielding ready rows found
    have kept := iteration_frames root q table placed machine fiber yielding
      (rows fiber (RunMachine.mem_of_fiber? found)) ready.1 rows
    have stored : AnswerFlow.Flows (fun (_ : Unit) _ frame => TemplateFrame q frame)
        (fun _ _ => ()) (Machine.iteration (interpOf root table) machine fiber yielding).machine := kept.2
    exact ⟨stored.update _ kept.1, kept.1⟩
  · intro machine fiber yielding ready rows found
    have frame := rows fiber (RunMachine.mem_of_fiber? found)
    have stored : AnswerFlow.Flows (fun (_ : Unit) _ frame => TemplateFrame q frame)
        (fun _ _ => ()) (evaluateNative root machine fiber yielding table).machine :=
      native_rows root q table machine fiber yielding frame rows
    have acting := native_frame root q table placed machine fiber yielding frame ready.1
    exact ⟨stored.update _ acting, acting⟩
  · intro state cause fiber held
    unfold interruptWithCause
    dsimp only
    repeat' split
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateFrame, CodeClosure.PredicateFamily.Frame, TemplateAt])
  · intro machine owner token code fiber ready rows found parked
    exact ⟨terminal_template q code (ready.2.2 owner token code rfl), (rows.found found).2⟩
  · intro machine raceId race code more host ready rows found programs hostFound
    refine ⟨ready.2.1 race (List.mem_of_find?_eq_some found) code ?_, ?_⟩
    · rw [programs]; exact .head _
    · intro saved member; cases member
  · intro machine raceId yielding race fiber exit ready rows found hostFound accepted
    exact ⟨terminal_template q _ (SourceScope.race_settle_reply root table raceId _ exit),
      (rows.found hostFound).2⟩
  · intro machine raceId yielding race fiber ready rows found hostFound
    refine ⟨(rows.found hostFound).1, ?_⟩
    intro code member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; trivial
    · exact (rows.found hostFound).2 code later
  · intro machine host yielding kind fiber ready rows found
    refine ⟨?_, (rows.found found).2⟩
    have awaited := await_template root q table machine kind
    change TemplateAt q (.onSuccess (awaitCode (interpOf root table) machine kind) (.restore (.success .unit)))
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt,
      CodeClosure.RegistrationBody, NameAt, OrdinaryNameAt, CodeClosure.Slots.NameAt,
      CodeClosure.Qualified.NameAt])
  · intro machine host yielding fibers fiber ready rows found
    refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
    intro code member
    rcases List.mem_cons.mp member with same | later
    · rw [same]; trivial
    · exact (rows.found found).2 code later
  · intro machine owner exit fiber ready rows found children
    refine ⟨?_, (rows.found found).2⟩
    change TemplateAt q (.onSuccess
      (.withFiber (.store (.act (.interruptAll fiber.children none)))) (.restore exit))
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt,
      CodeClosure.RegistrationBody, NameAt, OrdinaryNameAt, ThunkAt,
      CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt,
      CodeClosure.Qualified.ThunkAt, CodeClosure.Qualified.StoreThunkAt,
      CodeClosure.Qualified.StoreActionAt])
  · intro state fiber held
    exact held
  · intro state fiber held
    exact ⟨held.1, by intro code member; cases member⟩
  · intro machine mode scope target state key found fiber member held
    exact held
  · intro machine scope key state found fiber member held
    exact held
  · intro machine fiber member held
    exact held
  · intro machine list phase fiber member held
    exact held

/-- One actual command retains full current and saved templates through the common producer. -/
theorem command_templates (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (ready : CommandReady q machine command)
    (rows : ∀ fiber ∈ machine.fibers, TemplateFrame q fiber.frame) :
    letI := evaluatorFor root table
    ∀ fiber ∈ (driveStep (interpOf root table) machine command rest).1.fibers,
      TemplateFrame q fiber.frame := by
  letI := evaluatorFor root table
  exact (template_commands root q table placed).step machine command rest ready rows

end Effect4.Program.FinalizerSource
