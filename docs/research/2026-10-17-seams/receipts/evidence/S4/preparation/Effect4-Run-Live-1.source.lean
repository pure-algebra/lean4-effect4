import Effect4.Run.Event

/-!
# Live — an admitted run reached from an open

`Api.Built.ofSketch` checks full program admission before `Live.open` constructs a run.
`Live.feed` and `Live.feedAll` feed ordered commands through that run.
The proof field connects every `Live` to `Run.open` and `Run.play`.
`Live.reached` in `src/Effect4/Laws/Api/Live.lean` supplies the existing reached-run predicate.
`LiveRecord.restore` repeats admission and feeds the stored journal.
This file stays outside the module form because it imports the specialization sites.
-/

set_option autoImplicit false

namespace Effect4

open Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Header)
open Effect4.Api.Runner (Command)

/-- **A live run**: a run, with the proof that an open of a built program and run commands reach
it. -/
structure Live where
  /-- The run: the checked session, the journal and the verdicts. -/
  run : Run
  /-- An open of a built program and run commands reach the run. -/
  opened : ∃ (b : Api.Built) (id : String) (budget : Api.Budget) (binding : String)
    (commands : List Command), (Run.open b id budget binding).play commands = run

namespace Live

/-- **Open a built program under a name.** Nothing here can refuse: the certificate is in the
`Built` (`Run.open`). -/
def «open» (b : Api.Built) (id : String) (budget : Api.Budget := {}) (binding : String := "") :
    Live :=
  ⟨Run.open b id budget binding, b, id, budget, binding, [], rfl⟩

/-- Step of `feed`: the run that one event reaches from a live run is reached from an open too.

Placement: concept `host-session-protocol`; a step of `Live.feed`, the face of row 326 (1). Reach:
every live run and every event. It says nothing of the event's verdict. -/
theorem opened_feed (l : Live) (event : Run.Event) :
    ∃ (b : Api.Built) (id : String) (budget : Api.Budget) (binding : String)
      (commands : List Command),
      (Run.open b id budget binding).play commands = (l.run.feed event).1 := by
  obtain ⟨b, id, budget, binding, commands, h⟩ := l.opened
  refine ⟨b, id, budget, binding, commands ++ event.rows l.run, ?_⟩
  rw [Run.feed_fst, ← h]
  simp only [Run.play, List.foldl_append]

/-- **Feed one event**: play its run commands through the run, and answer the verdict. An
unresolved selector plays nothing (`Run.feed`). -/
def feed (l : Live) (event : Run.Event) : Live × Run.Verdict :=
  let fed := l.run.feed event
  (⟨fed.1, opened_feed l event⟩, fed.2)

/-- **Feed events in order**, each through `feed`. The verdicts are not kept: the run keeps the
phase of every run command that it played. -/
def feedAll (l : Live) (events : List Run.Event) : Live :=
  events.foldl (fun l event => (l.feed event).1) l

end Live

end Effect4
