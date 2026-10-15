import Effect4.Laws.Program.NativeFrameScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: code-location predicates and their native command transports.
Native replies use the existing completion language and administrative race cleanup.
These permissions establish no history closure or host admission.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program
abbrev SourceFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev SourceRace := Race EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceTask := Task EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceCommand := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceDispatcher := Dispatcher EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceBucket := Bucket EffName EffThunk Val Err Defect FiberId Ann

/-- Actual native resume producers return exits, represented reference reads or race cleanup.
Consumer: resume source ownership and source-use command accounting. -/
inductive TerminalReply : NCode → Prop
  | success (value : Val) : TerminalReply (.success value)
  | failure (cause : CauseV) : TerminalReply (.failure cause)
  | refGet (cell : RefKey) : TerminalReply (.sync (.store (.op (.refGet cell))))
  | raceCleanup (race : Nat) (exit : ExitV) : TerminalReply
      (.onSuccess (.withFiber (.store (.act (.setInterruptible (.cancelRace race) false))))
        (.store (.restore exit)))

/-- Represented completions produce only native resume payloads.
Consumer: due drains, clock answers and host reply preparation. -/
theorem completion_reply (answer : Completion Val Err Defect FiberId Ann) :
    TerminalReply (embed (completionPrim answer)) := by
  cases answer with
  | ofExit exit => cases exit <;> constructor
  | ofRefGet cell => exact .refGet cell

/-- Actual immediate asynchronous replies use the same native terminal payloads.
Consumer: source-opportunity and Atomic writer primitive debit under R11. -/
theorem register_reply (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (callback : EffName) (owner : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (produced : ((interpAt root view table).registerAsync callback owner token state).2 = some code) :
    TerminalReply code := by
  cases callback
  case registerAwait cell =>
    obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
    rw [← result]
    exact completion_reply answer
  case store callback =>
    cases callback
    case registerAwait cell =>
      obtain ⟨answer, _, result⟩ := Option.map_eq_some_iff.mp produced
      rw [← result]
      exact completion_reply answer
    all_goals cases produced
  all_goals cases produced

/-- Race callbacks return a fixed administrative cleanup or the accepted exit.
Consumer: the race observer's actual queued resume. -/
theorem race_settle_reply (root : NativeEff) (table : RowTable) (race : Nat)
    (cleanup : Bool) (exit : ExitV) :
    TerminalReply ((interpOf root table).raceSettle race cleanup exit) := by
  change TerminalReply (embed (raceSettleProgram race cleanup exit))
  unfold raceSettleProgram
  split
  · exact .raceCleanup race exit
  · cases exit <;> constructor

end Effect4.Program.SourceScope
