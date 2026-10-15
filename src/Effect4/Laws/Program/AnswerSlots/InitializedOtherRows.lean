import Effect4.Laws.Program.AnswerSlots.InitializedIteration

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: a native operation retains every nonacting stored fiber's initialized answer path.
Reach: two actual distinct owner identities, the existing phase certificate and monotone allocation counts.
Limit: native action births and the acting frame use their separate actual producers.
Consumer: the coupled crew primitive and command flow invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Two distinct initialized owners cannot coexist before the stable store phase. -/
theorem distinct_ready (spec : Spec) (state : Stores) (first last : FiberId)
    (firstKind lastKind : Kind) (firstCode lastCode : NCode)
    (firstOwned : CodeAt spec ⟨first, state⟩ firstKind firstCode)
    (lastOwned : CodeAt spec ⟨last, state⟩ lastKind lastCode) (different : first ≠ last) :
    Ready spec ⟨last, state⟩ := by
  rcases code_phase spec ⟨first, state⟩ firstKind firstCode firstOwned with owner | ready
  · rcases code_phase spec ⟨last, state⟩ lastKind lastCode lastOwned with other | ready
    · exact (different (owner.trans other.symm)).elim
    · exact ready
  · exact ready

/-- Every nonacting current code transports through the operation's actual growing stores. -/
theorem other_code (spec : Spec) (state next : Stores) (actor owner : FiberId)
    (actorKind input : Kind) (actorCode program : NCode)
    (acting : CodeAt spec ⟨actor, state⟩ actorKind actorCode)
    (owned : CodeAt spec ⟨owner, state⟩ input program) (different : actor ≠ owner)
    (refs : state.refs.length ≤ next.refs.length)
    (deferred : state.deferreds.cells.length ≤ next.deferreds.cells.length) :
    CodeAt spec ⟨owner, next⟩ input program :=
  code_future_ready spec ⟨owner, state⟩ input program owned ⟨owner, next⟩ ⟨rfl, refs, deferred⟩
    (distinct_ready spec state actor owner actorKind input actorCode program acting owned different)

/-- The actual nonacting frame retains both its current class and its ordered saved suffix. -/
theorem other_frame (spec : Spec) (view : List (FiberId × ExitV)) (state next : Stores)
    (actor owner : FiberId) (actorKind input output : Kind) (actorCode : NCode)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (acting : CodeAt spec ⟨actor, state⟩ actorKind actorCode)
    (owned : CodeAt spec ⟨owner, state⟩ input frame.current)
    (saved : Effect4.Contracts.Path (Edge spec view ⟨owner, state⟩) input output frame.stack)
    (different : actor ≠ owner) (refs : state.refs.length ≤ next.refs.length)
    (deferred : state.deferreds.cells.length ≤ next.deferreds.cells.length) :
    AnswerFlow.FamilyResult (model spec view) (Edge spec view) ⟨owner, next⟩ output frame.current frame.stack :=
  ⟨input, other_code spec state next actor owner actorKind input actorCode frame.current acting owned different refs deferred,
    path_future spec view ⟨owner, state⟩ ⟨owner, next⟩ ⟨rfl, refs, deferred⟩ input output frame.stack saved⟩
end Effect4.Program.AnswerSlots.Initialized
