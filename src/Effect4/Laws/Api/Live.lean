import Effect4.Run.Live
import Effect4.Run.View
import Effect4.Laws.Api.SessionRef

/-!
# Api.Live — the laws of a run at the face, with no premise of reachability

Slice DM2 of the session note (`docs/research/2026-10-07-session-api-design.md` §4): with `Live`,
the theorems that take `Run.Reached` lose that premise. A `Live` carries the proof that an open and
run commands reach its run (`src/Effect4/Run/Live.lean`), so each law of a reached run holds of
it.

* **A live run is reached** (`reached`): the connector to the law graph's `Run.Reached`.
* **A live run replays from its own journal** (`journal_replays`): `Run.journal_replays` at `Live`.
* **A live session's reading is the reference's replay of its tape** (`session_eq_ref`):
  `Run.session_eq_ref` at `Live`. Its one premise is that the run is funded.
* **Starting is the session's start** (`start_error`, `start_ok`): `Live.start` refuses exactly
  where `Api.HostSession.start` refuses, with its reason, and opens the admitted program
  otherwise.
* **The view projects the waits** (`view_awaits`, slice DM3): the view's calls are the machine's
  awaited calls, in the machine's order (HC-1's connector to `Await`).
* **The view names each call's checked instance** (`view_checked`): the instance at the call's
  address in the run's program, as the checker types it.

What they do not establish: that a run is funded (`embedded-budget-sufficient`, an open part of
R12), reply admission, the session's ledger, a host's conformance, host progress, or anything of a
lowered session. The host boundary stays where `docs/core/host-boundary.md` puts it.
-/

set_option autoImplicit false

namespace Effect4.Live

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Api.HostSession (Header)

/-- **A live run is reached.** An open of a built program and run commands reach the run of a
`Live`, so every law of the law graph that takes `Run.Reached` holds of it.

Placement: concept `host-session-protocol`. It is the connector that slice DM2 owes
(the session note, §4), a step of `journal_replays` and `session_eq_ref` below. Reach: every
`Live`. It does not establish that the run is funded or at rest. -/
theorem reached (l : Live) : Run.Reached l.run := by
  obtain ⟨b, id, budget, binding, commands, h⟩ := l.opened
  rw [← h]
  exact Run.Reached.play _ commands (Run.Reached.opened b id budget binding)

/-- **A live run replays from its own journal.** Opening the same built program under the same
name, budget and binding, and playing the run's journal, reaches the run, phases and ledger
included. It is `Run.journal_replays` at `Live`, with no premise.

Placement: concept `host-session-protocol`, requirement R13 (a run is data because its journal is).
Consumer: a holder that keeps a session as its journal and restores it, and DM7's lowered holder.
Reach: every `Live`. It does not establish that another host chooses the same commands, and it says
nothing of a lowered run. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem journal_replays (l : Live) :
    (Run.open l.run.built l.run.id l.run.budget l.run.profile).play l.run.journal = l.run :=
  Run.journal_replays l.run (reached l)

/-- **A live session's reading is the reference machine's replay of its tape** (DI-57). For a
funded `Live`, the session's class and observation are the class and observation of the reference
machine's replay of the run's own tape, at the run's row table and budgets. It is
`Run.session_eq_ref` at `Live`: the premise `Run.Reached` is gone, and `funded` stays.

Placement: concept `translation-simulation`, claim `session-eq-ref`, requirement R6. Consumer: the
typed session (decisions row 99), and a caller that reads the premise off the view (slices DM3 and
DM4, `view-funded`). Reach: every `Live` whose run is funded. It does not establish that a run is
funded, the session's ledger, reply admission or a host's conformance. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem session_eq_ref (l : Live) (h : Run.funded l.run = true) :
    l.run.inspect.outcome =
        classify (replayR l.run.built.program l.run.budget.fuel (Run.tapeOf l.run)
          l.run.budget.compileFuel l.run.built.table) ∧
      obs l.run.machine =
        obsR (replayR l.run.built.program l.run.budget.fuel (Run.tapeOf l.run)
          l.run.budget.compileFuel l.run.built.table).machine :=
  Run.session_eq_ref l.run (reached l) h

/-- **Starting refuses where the session refuses**, with the session's reason (decisions row 326
(1)).

Placement: concept `host-session-protocol`. Consumer: a holder that cannot carry a certificate,
DM7's lowered session (row 326 (2)). Reach: every program, table, binding, header and budget. It
does not establish which programs admission admits. -/
theorem start_error (program : Api.Program) (table : RowTable) (binding : String)
    (header : Header) (budget : Api.Budget) (why : Api.HostSession.Refusal) :
    Live.start program table binding header budget = .error why ↔
      Api.HostSession.start program table binding header budget.compileFuel = .error why := by
  unfold Live.start
  cases Api.HostSession.start program table binding header budget.compileFuel with
  | error reason =>
    dsimp only
    constructor
    · intro h
      cases h
      rfl
    · intro h
      cases h
      rfl
  | ok session =>
    dsimp only
    constructor
    · intro h
      cases h
    · intro h
      cases h

/-- **Starting opens the admitted program.** Where the session's start answers a session, the
face opens the program with that session's certificate, under the header's name and binding.

Placement: concept `host-session-protocol`; the accepted half of `start_error`, with the same
consumer. Reach: every accepted start. It does not establish that the opened session is the one
that the start answered; `Run.open_total` gives that for a header built from the `Built`. -/
theorem start_ok (program : Api.Program) (table : RowTable) (binding : String) (header : Header)
    (budget : Api.Budget) (session : Api.HostSession.Session program table)
    (h : Api.HostSession.start program table binding header budget.compileFuel = .ok session) :
    Live.start program table binding header budget =
      .ok (Live.open { table, program, admitted := session.admitted } header.session budget
        binding) := by
  unfold Live.start
  rw [h]

/-- **The view projects the waits.** The calls of a live run's view are the calls the machine
waits on, in the machine's order: the view adds the checked source and the session's record to
each, and drops none (HC-1, decisions row 373 (12)).

Placement: concept `host-session-protocol`; HC-1's connector to `Await`, a step of the live call
view that row 373 (12) folds into DM3. Consumer: a run view driven by a host (row 373 (1)), which
offers a reply for each entry. Reach: every `Live`. It does not establish host progress, or a
history of every call. -/
theorem view_awaits (l : Live) : l.view.awaiting.map (·.await) = awaits l.run.machine := by
  show ((awaits l.run.machine).map l.run.callView).map (·.await) = _
  rw [List.map_map]
  exact List.map_id _

/-- **The view names each call's checked instance.** For each call that a live run's view lists,
the checked instance is the checker's instance at the call's address in the run's program
(`Api.HostSession.instanceAt`): the type that a reply must meet. The session's call table, made
once at the open, answers it (`reached_callInstance`).

Placement: concept `host-session-protocol`; a step of the claim `reply-at-call-instance`
(decisions row 323, an open part of R6). Consumer: a host adapter that picks its decoder from the
view (the session note §3.3 and §3.6, finding 5), and MCP's run tools. Reach: every `Live` and every
call that its view lists. It does not establish that the session admits a reply at that instance,
or that the expansion keeps the call at its address (`expansion-keeps-call`). -/
theorem view_checked (l : Live) (c : CallView) (h : c ∈ l.view.awaiting) :
    c.checked =
      c.origin.bind (Api.HostSession.instanceAt l.run.built.program l.run.built.table) := by
  obtain ⟨call, _, rfl⟩ := List.mem_map.mp h
  show (originOf l.run.machine call.fiber call.token).bind l.run.session.callInstance = _
  rw [Run.reached_callInstance l.run (reached l)]
  rfl

end Effect4.Live
