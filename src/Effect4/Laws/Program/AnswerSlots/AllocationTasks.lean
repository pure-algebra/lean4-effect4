import Effect4.Laws.Program.AnswerSlots.AllocationWaits
import Effect4.Laws.Program.PrimitiveDispatcher

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the common pending allocation driver and its actual detached snapshot.
Pending dispatchers carry ordinary terminal replies through actual task production.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Before application entry a stored resume carries an ordinary terminal completion. -/
def ReplyTask : SourceScope.SourceTask → Prop
  | .resume _ _ code => SourceScope.TerminalReply code ∧ NoRaceReply code
  | _ => True

abbrev Replies (dispatcher : SourceScope.SourceDispatcher) : Prop := DispatcherPredicate.All ReplyTask dispatcher

def ReplyRows (machine : NativeMachine) : Prop := ∀ fiber ∈ machine.fibers, Replies fiber.dispatcher

/-- The actual yield reply supplies its ordinary successful completion. -/
theorem reply_success (owner : FiberId) (token : Nat) (value : Val) : ReplyTask (.resume owner token (.success value)) := by
  refine ⟨.success value, ?_⟩
  intro race exit same
  cases same

/-- Every represented completion supplies the same pending task assertion. -/
theorem reply_completion (owner : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    ReplyTask (.resume owner token (embed (completionPrim answer))) :=
  ⟨SourceScope.completion_reply answer, completion_noRace answer⟩

/-- The actual due list maps represented completions before any task is posted. -/
theorem due_replies (root : NativeEff) (table : RowTable) (state : Stores) :
    ∀ owed ∈ ((interpOf root table).dueResumes state).1,
      ReplyTask (.resume owed.waiter owed.token owed.code) := by
  intro owed member
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  rw [← same]
  exact reply_completion original.waiter original.token original.code
/-- Clock replies also map a represented completion before posting any task. -/
theorem clock_replies (root : NativeEff) (table : RowTable) (state : Stores) (millis : ClockMillis) (owed : Owed NCode)
    (produced : ((interpOf root table).clockStep millis state).1 = some owed) :
    ReplyTask (.resume owed.waiter owed.token owed.code) := by
  obtain ⟨original, present, same⟩ := Option.map_eq_some_iff.mp produced
  rw [← same]
  exact reply_completion original.waiter original.token original.code

/-- External preparation produces an ordinary completion or a successful allocated handle value. -/
theorem external_reply_task (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) (owner : FiberId) (token : Nat) :
    ReplyTask (.resume owner token (prepareExternalAnswer table current answer state).2) := by
  unfold prepareExternalAnswer
  repeat' split
  all_goals aesop (add safe apply [reply_completion, reply_success])

/-- Actual guarded host reply selection retains ordinary terminal admission. -/
theorem prepared_reply_task (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (owner : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    ReplyTask (.resume owner token (prepareAsyncAnswer (interpOf root table) machine owner token answer).2) := by
  unfold prepareAsyncAnswer
  split
  · exact reply_completion owner token answer
  · exact external_reply_task table _ answer machine.state owner token

end Effect4.Program.AnswerSlots.AllocationAdapter
