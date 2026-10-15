import Effect4.Laws.Program.AnswerSlots.InitializedAdmin
import Effect4.Laws.Program.AnswerSlots.InitializedWaits
import Effect4.Laws.Program.SourceOpportunityPrimitive
import Effect4.Laws.Machine.AwaitCode

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual command cuts retain the initialized source and protected acquired values.
Reach: direct programs without races, actual parked replies and reserved administrative suffixes.
Limit: the coupled driver supplies the command demands; this connector supplies no progress.
Consumer: the two crew log histories through the shared answer-flow command producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The joint driver supplies only the source, capture and actual command permissions it carries. -/
structure CommandPremises (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) : Prop where
  scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes
  parked : ParkedShape.Configuration machine
  source : SourceScope.ConfigurationAt spec.root machine
  code : SourceScope.CommandAt spec.root command
  sites : Guard.commandRaceSites command = []
  admin : AdminDemand spec machine command
  terminal : TerminalDemand spec machine command

/-- Native waiting returns an administrative broad answer at each actual join mode. -/
theorem typed_await (spec : Spec) (machine : NativeMachine) (kind : ParkKind) :
    Typed.CodeAt spec.toSpec .root (awaitCode (interpOf spec.root spec.table) machine kind) := by
  apply awaitCode_closed (interpOf spec.root spec.table)
  · intro exit mode
    cases mode <;> cases exit <;> trivial
  · intro kind
    exact ⟨rfl, trivial, trivial, trivial⟩

/-- The root suffix admits the actual interruption wait and its answer-discarding callback. -/
theorem RootPath.afterInterrupt (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (kind : ParkKind) (held : RootPath spec ⟨fiber.id, machine.state⟩ fiber.frame) :
    FrameAt spec ⟨fiber.id, machine.state⟩
      {fiber.frame with
        current := asVoidCode (interpOf spec.root spec.table) (awaitCode (interpOf spec.root spec.table) machine kind)} := by
  obtain ⟨ready, output, saved⟩ := held
  refine ⟨.stable .root, output, .stable ready ?_, saved⟩
  exact ⟨.root, typed_await spec machine kind, trivial, trivial, trivial⟩

/-- A parallel close keeps the same broad suffix under its existing iterator edge. -/
theorem RootPath.closePar (spec : Spec) (world : World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (fibers : List FiberId) (held : RootPath spec world frame) :
    FrameAt spec world {frame with
      current := (interpOf spec.root spec.table).parkCode (.awaitAll fibers)
      stack := .iterator (interpOf spec.root spec.table).closeDoneName (interpOf spec.root spec.table).voidValue :: frame.stack} := by
  obtain ⟨ready, output, saved⟩ := held
  exact ⟨.stable .root, output, .stable ready ⟨rfl, trivial, trivial, trivial⟩,
    .cons (.mapped ready (.iterator _ ⟨trivial, trivial, trivial⟩)) saved⟩

/-- Finishing children starts from the actual drained stack and the source's ready phase. -/
theorem terminal_children (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (exit : ExitV) (empty : fiber.frame.stack = []) (ready : Ready spec ⟨fiber.id, machine.state⟩) :
    FrameAt spec ⟨fiber.id, machine.state⟩ {fiber.frame with
      deferredInterrupt := false
      current := .onSuccess ((interpOf spec.root spec.table).interruptAllCode fiber.children)
        ((interpOf spec.root spec.table).restoreName exit)} := by
  refine ⟨.stable .root, .stable .root, .stable ready ?_, ?_⟩
  · exact ⟨.root, ⟨rfl, trivial, trivial, trivial⟩, trivial, trivial, trivial⟩
  · rw [empty]
    exact .nil _

/-- Exact allocation counts transport old frames through native administrative store hooks. -/
theorem FrameAt.counts (spec : Spec) (state next : Stores) (owner : FiberId)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : FrameAt spec ⟨owner, state⟩ frame)
    (counts : Counts state.refs.length state.deferreds.cells.length next) :
    FrameAt spec ⟨owner, next⟩ frame :=
  FrameAt.rebase spec _ _ frame held
    ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩ counts.1.symm counts.2.symm

/-- The existing command producer consumes the actual initialized frame and queue permissions. -/
theorem command_facts (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) :
    letI := evaluatorFor spec.root spec.table
    AnswerFlow.Commands (interpOf spec.root spec.table) (CommandPremises spec)
      (fun world _ => FrameAt spec world) (fun state id => ⟨id, state⟩) := by
  letI := evaluatorFor spec.root spec.table
  refine {
    iteration := ?_, deliver := ?_, interruption := ?_, resume := ?_,
    entrant := ?_, settleRace := ?_, parkRace := ?_, afterInterrupt := ?_, closePar := ?_,
    exitChildren := ?_, publish := ?_, cleared := ?_, link := ?_, drop := ?_, due := ?_, wake := ?_ }
  · intro machine fiber yielding permission held found
    exact iteration_iterflows spec fragment machine fiber yielding held (held.found found) permission.scopes
  · intro machine fiber yielding permission held found
    exact native_iterflows spec fragment machine fiber yielding held (held.found found) permission.scopes
  · intro state cause fiber held
    exact FrameAt.interruption spec ⟨fiber.id, state⟩ fiber cause held
  · intro machine id token code fiber permission held found parked
    obtain ⟨input, output, owned, saved⟩ := held.found found
    have waits := Waits.of_frame spec fragment machine.state fiber input output owned saved
      (permission.parked fiber (RunMachine.mem_of_fiber? found))
    obtain ⟨result, incoming, actual, path⟩ := Waits.resume spec raceFree machine.state fiber code waits
      (by rw [parked]; intro wrong; cases wrong) permission.code.1 permission.code.2
    exact ⟨incoming, result, actual, path⟩
  · intro machine raceId race program more host permission held found programs hostFound
    have empty := SourceScope.Opportunities.races_nil spec.root machine raceFree permission.source
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found
  · intro machine raceId yielding race fiber exit permission held found fiberFound accepted
    have empty := SourceScope.Opportunities.races_nil spec.root machine raceFree permission.source
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found
  · intro machine raceId yielding race fiber permission held found fiberFound
    have empty := SourceScope.Opportunities.races_nil spec.root machine raceFree permission.source
    unfold RunMachine.race? at found
    rw [empty] at found
    cases found
  · intro machine host yielding kind fiber permission held found
    have same := RunMachine.id_of_fiber? found
    subst host
    cases kind
    case join target mode => exact RootPath.afterInterrupt spec machine fiber _ (permission.admin fiber.id rfl fiber found)
    case awaitAll targets => exact RootPath.afterInterrupt spec machine fiber _ (permission.admin fiber.id rfl fiber found)
    case race id => cases permission.sites
  · intro machine host yielding fibers fiber permission held found
    have same := RunMachine.id_of_fiber? found
    subst host
    exact RootPath.closePar spec ⟨fiber.id, machine.state⟩ fiber.frame fibers (permission.admin fiber.id rfl fiber found)
  · intro machine id exit fiber permission held found runs
    obtain ⟨empty, ready⟩ := permission.terminal fiber found
    have children : fiber.children ≠ [] := by
      intro absent
      rw [absent] at runs
      simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true] at runs
    exact terminal_children spec machine fiber exit empty (ready children)
  · intro state fiber held
    exact held.fields rfl rfl
  · intro state fiber held
    exact held.cleared spec ⟨fiber.id, state⟩ fiber.frame
  · intro machine mode scope target state key actual fiber member held
    exact FrameAt.counts spec machine.state state fiber.id fiber.frame held
      ((count_hooks spec [] _ _).link mode scope target machine.state state key ⟨rfl, rfl⟩ actual)
  · intro machine scope key state actual fiber member held
    exact FrameAt.counts spec machine.state state fiber.id fiber.frame held
      ((count_hooks spec [] _ _).drop scope key machine.state state ⟨rfl, rfl⟩ actual)
  · intro machine fiber member held
    exact FrameAt.counts spec machine.state _ fiber.id fiber.frame held
      ((count_hooks spec [] _ _).due machine.state ⟨rfl, rfl⟩)
  · intro machine list phase fiber member held
    exact FrameAt.counts spec machine.state _ fiber.id fiber.frame held
      ((count_hooks spec [] _ _).wake list phase machine.state ⟨rfl, rfl⟩)
end Effect4.Program.AnswerSlots.Initialized

namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Actual host reply preparation changes no allocation count. -/
theorem prepare_counts (spec : Spec) (machine : NativeMachine) (id : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    Counts machine.state.refs.length machine.state.deferreds.cells.length
      (prepareAsyncAnswer (interpOf spec.root spec.table) machine id token answer).1 := by
  unfold prepareAsyncAnswer
  split
  · exact ⟨rfl, rfl⟩
  · change Counts _ _ (prepareExternalAnswer spec.table _ answer machine.state).1
    unfold prepareExternalAnswer
    repeat' split
    all_goals exact ⟨rfl, rfl⟩

/-- Clock changes and prepared replies retain the initialized frame classes. -/
theorem outside_facts (spec : Spec) :
    AnswerFlow.OutsideEdits (interpOf spec.root spec.table)
      (fun world _ => FrameAt spec world) (fun state id => ⟨id, state⟩) where
  clock := fun machine _ _ fiber _ held =>
    FrameAt.counts spec machine.state _ fiber.id fiber.frame held ⟨rfl, rfl⟩
  prepare := fun machine id token answer fiber _ held =>
    FrameAt.counts spec machine.state _ fiber.id fiber.frame held (prepare_counts spec machine id token answer)

/-- Scope captures and current frames advance together, using the same actual synchronous permission. -/
theorem command_scoped_frames (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (raceFree : SourceScope.RaceFreeSource spec.root) (machine : NativeMachine)
    (command : Guard.NCmd) (rest : List Guard.NCmd) (permission : CommandPremises spec machine command)
    (held : FramesAt spec machine) :
    let result := driveStep (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine command rest
    FramesAt spec result.1 ∧ Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) result.1.state.scopes := by
  letI := evaluatorFor spec.root spec.table
  refine ⟨(command_facts spec fragment raceFree).step machine command rest permission held, ?_⟩
  apply Effect4.Program.ScopeFields.command_scopes (Typed.scopeModel spec.toSpec)
    (fun _ _ => trivial) spec.root spec.table machine command rest permission.scopes
  intro id yielding fiber found selected
  obtain ⟨input, output, owned, saved⟩ := held.found found
  exact current_fields spec ⟨fiber.id, machine.state⟩ input fiber.frame.current owned
end Effect4.Program.AnswerSlots.Initialized
