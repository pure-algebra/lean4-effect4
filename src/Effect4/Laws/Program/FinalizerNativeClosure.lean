import Effect4.Laws.Program.FinalizerScopes
import Effect4.Laws.Program.FinalizerFunding
import Effect4.Laws.Program.NativeActionRows
import Effect4.Laws.Program.NativeFrameRows
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.CodeClosure.PrimitiveClosure

/-!
Concept: scope-lifetime-finalization R11.
Question: actual primitive source closure serves once_placed_outside_census.
Consumer: the full source configuration through the existing command lift.
The same template annotates actual current code, saved frames and child programs.
These annotations establish neither source funding nor complete histories.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

abbrev TemplateFrame (q : List Nat) := CodeClosure.PredicateFamily.Frame (TemplateAt q)

/-- The full template retains the source slots consumed by frame accounting. -/
theorem template_frame_at (q : List Nat) (frame : SourceFrame) (held : TemplateFrame q frame) :
    FrameAt q frame := ⟨held.1.1, fun code member => (held.2 code member).1⟩

/-- Actual terminal replies carry no source-bearing callback. -/
theorem terminal_template (q : List Nat) (code : NCode) (reply : SourceScope.TerminalReply code) :
    TemplateAt q code := by
  cases reply
  case raceCleanup =>
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt,
      CodeClosure.RegistrationBody, NameAt, OrdinaryNameAt, ThunkAt,
      CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt, CodeClosure.Slots.ThunkAt,
      CodeClosure.Qualified.ThunkAt, CodeClosure.Slots.StoreNameAt, CodeClosure.Qualified.StoreNameAt,
      CodeClosure.Slots.StoreThunkAt, CodeClosure.Qualified.StoreThunkAt,
      CodeClosure.Qualified.StoreActionAt, CodeClosure.Qualified.ProgAt])
  all_goals trivial

/-- Waiter wrapping retains the actual full callback annotation. -/
theorem waiter_at (q : List Nat) (callback : EffName) (owner : FiberId) (token : Nat)
    (held : OrdinaryNameAt q callback) :
    TemplateAt q (.asyncFinalizer (.withWaiter callback owner token)) :=
  ⟨ordinary_name q callback held, trivial, trivial⟩

/-- Native administrative action replies use the existing unit saved family. -/
theorem actionFlowFacts (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    SourceScope.ActionFlowFacts
      ((CodeClosure.PredicateFamily.spec root table (TemplateAt q) (templateRules root q table placed)).model view)
      (CodeClosure.PredicateFamily.edge (TemplateAt q)) root view table () () := by
  constructor <;> intros <;> trivial

/-- The actual parent action path retains every full source template. -/
theorem action_frame (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (suspended : EffThunk) (action : NAction)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes)
    (selected : fiber.frame.current = .withFiber suspended)
    (found : (interpAt root view table).withFiberOf suspended = some action) :
    TemplateFrame q (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action).fiber.frame := by
  have owned := held.1.1
  rw [selected] at owned
  have programs := interp_action_at root q view table suspended action owned found
  have parent : SourceScope.ParentProgramsWith True True (TemplateAt q) action :=
    SourceScope.ActionProgramsWith.mono action programs (fun _ => trivial) (fun _ => trivial)
      (by intro role code owned; cases role <;> trivial)
  have result := SourceScope.with_fiber_parent_path
    ((CodeClosure.PredicateFamily.spec root table (TemplateAt q) (templateRules root q table placed)).model view)
    (CodeClosure.PredicateFamily.edge (TemplateAt q)) root view table () () () machine fiber yielding action
    (actionFlowFacts root q view table placed) held.1
    (CodeClosure.PredicateFamily.path (TemplateAt q) fiber.frame.stack held.2) parent
    (fun scope exit state program closed =>
      (close_native_at root q view table scope exit fiber.frame.interruptible fiber.id
        machine.state state (some program) scopes closed).2 program rfl)
  exact ⟨result.1, CodeClosure.PredicateFamily.path_owned (TemplateAt q) result.2⟩

/-- The actual countdown answer is terminal and its cancellation frame is administrative. -/
theorem countdown_frame (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (targets : List FiberId)
    (held : TemplateFrame q fiber.frame) :
    TemplateFrame q (countdownParkEdits (interpAt root view table) machine fiber targets .exitsValue false).2.1.frame := by
  unfold countdownParkEdits
  dsimp only
  split
  · exact ⟨⟨trivial, trivial, trivial⟩, held.2⟩
  · refine ⟨held.1, ?_⟩
    intro code member
    rcases List.mem_cons.mp member with same | present
    · rw [same]; trivial
    · exact held.2 code present

/-- Full native templates instantiate the shared actual primitive producer. -/
theorem primitive_frame (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes) :
    TemplateFrame q (evaluatePrim (interpAt root view table) machine fiber yielding).fiber.frame := by
  apply CodeClosure.PredicateFamily.primitive_frame root table (TemplateAt q)
    (templateRules root q table placed) view machine fiber yielding held
  refine {
    action := fun suspended action selected found =>
      action_frame root q view table placed machine fiber yielding suspended action held scopes selected found,
    reply := ?_, cancel := ?_, joinCancel := by trivial,
    countdown := fun targets => countdown_frame root q view table machine fiber targets held }
  · intro register signal cancel state code _ registered
    exact terminal_template q code (SourceScope.register_reply root view table register fiber.id
      machine.nextToken machine.state code (congrArg Prod.snd registered))
  · intro register signal cancel selected
    have names := held.1.1
    rw [selected] at names
    cases cancel with
    | none => trivial
    | some callback => exact waiter_at q callback fiber.id machine.nextToken (names.2 callback rfl)

/-- Existing stored rows and actual child births retain their own complete templates. -/
theorem primitive_rows (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame)
    (rows : ∀ row ∈ machine.fibers, TemplateFrame q row.frame) :
    ∀ row ∈ (evaluatePrim (interpAt root view table) machine fiber yielding).machine.fibers,
      TemplateFrame q row.frame := by
  apply NativeFrameRows.primitive_rows (interpAt root view table) machine fiber yielding _
    (Moves.evaluatePrim_producer (interpAt root view table) machine fiber yielding)
    (fun _ frame => TemplateFrame q frame) rows
  intro suspended action selected _ found
  have owned := held.1.1
  rw [selected] at owned
  have programs := interp_action_at root q view table suspended action owned found
  apply SourceScope.with_fiber_frame_rows_at (races := True) (parallel := True)
    root view table (TemplateAt q) (fun _ frame => TemplateFrame q frame)
    machine fiber yielding action 0 (Nat.zero_le _) rows
    (SourceScope.ActionProgramsWith.mono action programs (fun _ => trivial) (fun _ => trivial)
      (by intro role code owned; cases role <;> trivial))
  intro id _ frame current empty
  exact ⟨current, by rw [empty]; intro code member; cases member⟩

end Effect4.Program.FinalizerSource
