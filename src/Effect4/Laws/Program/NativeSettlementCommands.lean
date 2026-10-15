import Effect4.Laws.Program.Guard.ReturnCommands

/-!
Concept: reactive-scheduling R11.
Question: initialized pending-command facts follow the actual settlement word.
Reach: actual native outcomes and addressed message emissions; the old command tail stays explicit.
Limit: command permission and frame facts are supplied by their existing producers.
Consumer: initialized QueueAt settlement and the two crew log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.NativeSettlementCommands
open Effect4 Effect4.Machine Effect4.Program

/-- Settlement either retains an emitted command or introduces one of its actual disposition commands. -/
def Introduced (id : FiberId) (next : Moves.NIteration) (command : Guard.NCmd) : Prop :=
  command ∈ next.nested ∨ (∃ target, command = .evaluate target) ∨
  command = .loop id next.yielding ∨ command = .deliver id next.yielding ∨
  ∃ exit, next.outcome = .finished exit ∧ command = .finish id exit

/-- Actual outcome disposition adds only its loop, deliver or finish command. -/
theorem outcome_member (id : FiberId) (rest : List Guard.NCmd) (next : Moves.NIteration)
    (command : Guard.NCmd) (member : command ∈ (settleOutcome id rest next).2) :
    command ∈ rest ∨ Introduced id next command := by
  cases outcome : next.outcome <;> simp only [settleOutcome, outcome] at member
  case parked =>
    split at member
    all_goals simp only [List.mem_append, List.mem_singleton] at member
    all_goals aesop (add norm unfold [Introduced])
  all_goals simp only [List.mem_append, List.mem_singleton, List.not_mem_nil] at member
  all_goals aesop (add norm unfold [Introduced])

/-- The message prefix contributes only evaluations; actual settlement retains the old nested word. -/
theorem member (id : FiberId) (rest : List Guard.NCmd) (next : Moves.NIteration)
    (command : Guard.NCmd) (present : command ∈ (settle id rest next).2) :
    command ∈ rest ∨ Introduced id next command := by
  cases edits : next.edits with
  | nil =>
    simp only [settle, edits] at present
    exact outcome_member id rest next command present
  | cons edit tail =>
    simp only [settle, edits] at present
    split at present
    · exact (List.not_mem_nil present).elim
    · rename_i owner found
      have shape := outcome_member id rest _ command present
      rcases shape with prior | created
      · exact .inl prior
      · rcases created with nested | evaluation | looping | delivering | finishing
        · rcases List.mem_append.mp nested with message | original
          · obtain ⟨target, same⟩ := (RunMachine.applyFiberEdits_shape (edit :: tail) (next.machine.update next.fiber)).2 command message
            exact .inr (.inr (.inl ⟨target, same⟩))
          · exact .inr (.inl original)
        · exact .inr (.inr (.inl evaluation))
        · exact .inr (.inr (.inr (.inl looping)))
        · exact .inr (.inr (.inr (.inr (.inl delivering))))
        · exact .inr (.inr (.inr (.inr (.inr finishing))))
end Effect4.Program.NativeSettlementCommands
