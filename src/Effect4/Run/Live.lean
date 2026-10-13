import Effect4.Run.Event

/-!
# Run.Live — the host session's face: a run reached from an open

The deep module that decisions row 326 (1) rules: `Live.open`, `Live.start`, `Live.feed` and
`Live.view`, slice DM2 of the session note (`docs/research/2026-10-07-session-api-design.md` §3.1).
The view is slice DM3. A `Live` is the existing `Run` with one more field, the proof that an open
and run commands reach it. So it holds no second representation of a session (`AGENTS.md`,
"Representation rules"): the session, the journal and the verdicts are the run's.

* **Reached by construction.** `Run` and `Session` take any machine, and a battery can write a run
  literal. A `Live` is built only with its proof, so a law of a reached run holds of every `Live`
  with no premise (`Live.reached`, `src/Effect4/Laws/Api/Live.lean`).
* **Opening cannot refuse.** `Live.open` takes a `Built`, as `Run.open` does.
* **Starting refuses as the session does.** `Live.start` takes a program, a table and a header,
  and it reruns program admission (`Api.HostSession.start`). A holder that cannot carry a
  certificate starts here: a lowered session (row 326 (2)).
* **Feeding is the run's.** `Live.feed` plays one event through `Run.feed` and answers its verdict.

The proof field is an equation over `Run.open` and `Run.play`, not a predicate of its own. The law
graph's `Run.Reached` (`src/Effect4/Laws/Run.lean`) stays the one named predicate of a reached run,
and `Live.reached` connects the two.

This file is no `module` file: it imports `Effect4.Run.Basic`, an importer of the specialization
sites of decisions row 202.
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

/-- **Start a program from an explicit header, or refuse as the session does.** It reruns
program admission at the header's table (`Api.HostSession.start`), so it refuses each header and
each program that the session refuses, with the session's reason. On success it opens the program
with the certificate that admission answered, under the header's name. -/
def start (program : Api.Program) (table : RowTable) (binding : String) (header : Header)
    (budget : Api.Budget := {}) : Except Api.HostSession.Refusal Live :=
  match Api.HostSession.start program table binding header budget.compileFuel with
  | .error why => .error why
  | .ok session =>
    .ok (Live.open { table, program, admitted := session.admitted } header.session budget binding)

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

end Live

end Effect4
