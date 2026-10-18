import Effect4.Tool.Actions

/-!
# Tool.Replay — a tool state as its accepted actions

A tool state persists as its accepted actions, never as a derived state. `State` keeps the
transcript beside the raw state it replays to, with the proof that the uncached replay reaches it
(`State.replayed`). A load replays the transcript and refuses the first failed action by its index.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4.Program.Check
namespace Internal

/-- **One replay step**: a refused prefix stays refused; otherwise the interpreter runs once. -/
def replayStep (current : Except (Nat × Refusal) (Nat × Raw)) (a : Action) :
    Except (Nat × Refusal) (Nat × Raw) :=
  match current with
  | .error why => .error why
  | .ok (index,raw) =>
    match (action Oracle.uncached raw a).value with
    | .error why => .error (index,why)
    | .ok (next,_) => .ok (index+1,next)

/-- **Replay actions** from a raw state, counting the accepted ones. -/
def replayCursor (initial : Raw) (actions : List Action) :
    Except (Nat × Refusal) (Nat × Raw) :=
  actions.foldl replayStep (.ok (0,initial))

/-- Helper of transcript_replays; replay extends the same action fold. -/
theorem replayCursor_snoc (initial : Raw) (actions : List Action) (a : Action) :
    replayCursor initial (actions ++ [a]) = replayStep (replayCursor initial actions) a := by
  unfold replayCursor
  rw [List.foldl_append]
  rfl
end Internal

/-- **Replay a transcript**: the raw state, or the first refused action's index and refusal. -/
def replayAccepted (initial : Internal.Raw) (actions : List Action) :
    Except (Nat × Refusal) Internal.Raw :=
  (Internal.replayCursor initial actions).map Prod.snd

/-- Accepted actions and the raw state reached by their sole validating interpreter. -/
structure State where
  private mk ::
  transcript : List Action
  raw : Internal.Raw
  replayed : Internal.replayCursor {} transcript = .ok (transcript.length,raw)

/-- The empty state: no action accepted. -/
def empty : State := ⟨[],{},rfl⟩

/-- Helper of serve_appends and transcript_replays; an accepted action extends the retained fold. -/
def State.accept (s : State) (a : Action) (next : Internal.Raw) (answer : ActionAnswer)
    (h : (Internal.action Oracle.uncached s.raw a).value = .ok (next,answer)) : State :=
  ⟨s.transcript ++ [a],next,by
    rw [Internal.replayCursor_snoc, s.replayed]
    simp only [Internal.replayStep, h, List.length_append, List.length_singleton]⟩

end Effect4.Tool
