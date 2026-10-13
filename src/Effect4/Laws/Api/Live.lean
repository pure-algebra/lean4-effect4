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
* **The view places every live fiber** (`view_classifies`): runnable, on a host call, on a timer,
  or in an internal wait (decisions row 333 (3)).
* **The view's flag is `funded`** (`view_funded`, slice DM4): the session's bit and the journal's
  verdicts give `Run.funded` with no replay.

What they do not establish: that a run is funded (`embedded-budget-sufficient`, an open part of
R12), reply admission, the session's ledger, a host's conformance, host progress, or anything of a
lowered session. The host boundary stays where `docs/core/host-boundary.md` puts it.
-/

set_option autoImplicit false

namespace Effect4.Live

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Api.HostSession (Header Phase)
open Effect4.Api.Runner (Command)

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

/-- **The view places every live fiber** (decisions row 333 (3)). Each fiber of a live run's
machine that has not exited stands in one of four places of the view: runnable, parked on a host
call, asleep on a timer, or in an internal wait.

Placement: concept `reactive-scheduling`; a step of the proposed claim `view-names-waits`, which row
333 (3) puts in slice DM3 (R12's classification of a live run). Consumer: an agent that reads a
deadlock off the view (`emptyFrontier`, with each wait named), and the run view driven by a host.
Reach: every `Live` and every fiber of its machine with no exit. It does not establish which fiber
can end a wait, progress or liveness, or an internal wait's program address, which the machine does
not keep. -/
theorem view_classifies (l : Live) :
    ∀ f ∈ l.run.machine.fibers, f.exit = none →
      f.id ∈ l.view.runnable ∨ f.id ∈ l.view.awaiting.map (·.await.fiber) ∨
        f.id ∈ l.view.timers.map (·.1) ∨ f.id ∈ l.view.waits.map (·.fiber) := by
  intro f hf live
  cases hp : f.parked with
  | notParked =>
    left
    show f.id ∈ Api.runnableFibers l.run.machine
    refine List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hf, ?_⟩, rfl⟩
    simp only [Api.isRunnable, live, hp, Option.isNone_none, Bool.true_and, beq_self_eq_true]
  | withGuard token =>
    cases hreq : requestOf l.run.machine f.id token with
    | some call =>
      cases call with
      | mk op request =>
        right
        left
        show f.id ∈ ((awaits l.run.machine).map l.run.callView).map (·.await.fiber)
        rw [List.map_map]
        refine List.mem_map.mpr ⟨⟨f.id, token, op, request⟩,
          List.mem_filterMap.mpr ⟨f, hf, ?_⟩, rfl⟩
        simp only [hp, hreq, Option.map_some]
    | none =>
      cases hw : l.run.machine.state.timers.wake.waiters.any (·.fiber == f.id) with
      | true =>
        right
        right
        left
        obtain ⟨w, hwmem, hweq⟩ := List.any_eq_true.mp hw
        show f.id ∈ (l.run.machine.state.timers.wake.waiters.map
          fun w => (w.fiber, w.payload)).map (·.1)
        rw [List.map_map]
        exact List.mem_map.mpr ⟨w, hwmem, beq_iff_eq.mp hweq⟩
      | false =>
        right
        right
        right
        show f.id ∈ (Run.internalWaits l.run.machine).map (·.fiber)
        refine List.mem_map.mpr ⟨⟨f.id, token, Run.registrationOf f⟩,
          List.mem_filterMap.mpr ⟨f, hf, ?_⟩, rfl⟩
        simp only [live, hp, hreq, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-! ## The view's `funded` (slice DM4)

The steps of `view_funded`. `rowReads` is the tape's test of one run command: the decision that the
command gives the machine reads on (`Run.readsOn`), or it gives none. -/

/-- The tape's test of one run command: whether the decision it gives the machine reads on. A
command that gives no decision passes. -/
def rowReads (r : Run) (c : Command) : Bool :=
  match Run.decisionOf r c (Api.Runner.result r.runner c).phase with
  | some d => Run.readsOn r d
  | none => true

/-- Step of `view_funded`: one run command conjoins the session's bit with the tape's test of the
command. A reply application keeps its step's fuel in the bit (`applyReply_funded_applied`); a
control that progressed reads on (`advance_progressed`); every other command keeps the bit. -/
theorem step_funded (r : Run) (c : Command) :
    (r.step c).session.funded = (r.session.funded && rowReads r c) := by
  cases c with
  | bind call token =>
    show (Api.HostSession.bindCall r.session call token).session.funded =
      (r.session.funded && true)
    rw [Api.HostSession.bindCall_funded, Bool.and_true]
  | submit reply =>
    show (Api.HostSession.submit r.session reply).session.funded = (r.session.funded && true)
    rw [Api.HostSession.submit_funded, Bool.and_true]
  | apply key =>
    show (Api.HostSession.applyReply r.session key r.budget.fuel).session.funded =
      (r.session.funded &&
        match Run.decisionOf r (.apply key)
            (Api.HostSession.applyReply r.session key r.budget.fuel).phase with
        | some d => Run.readsOn r d
        | none => true)
    cases hph : (Api.HostSession.applyReply r.session key r.budget.fuel).phase with
    | applied =>
      obtain ⟨reply, decision, hread, hpre, hfund⟩ :=
        Api.HostSession.applyReply_funded_applied r.session key r.budget.fuel hph
      have same := Run.preflight_replyDecision r.session reply decision hpre
      rw [hfund]
      show _ = (r.session.funded &&
        match (Api.HostSession.readReply r.session.pending key).map Run.replyDecision with
        | some d => Run.readsOn r d
        | none => true)
      rw [hread, same]
      rfl
    | bound =>
      rw [(Api.HostSession.applyReply_funded_or r.session key r.budget.fuel).resolve_right
        (by rw [hph]; exact fun h => nomatch h)]
      exact (Bool.and_true _).symm
    | preflight =>
      rw [(Api.HostSession.applyReply_funded_or r.session key r.budget.fuel).resolve_right
        (by rw [hph]; exact fun h => nomatch h)]
      exact (Bool.and_true _).symm
    | progressed =>
      rw [(Api.HostSession.applyReply_funded_or r.session key r.budget.fuel).resolve_right
        (by rw [hph]; exact fun h => nomatch h)]
      exact (Bool.and_true _).symm
    | frontier =>
      rw [(Api.HostSession.applyReply_funded_or r.session key r.budget.fuel).resolve_right
        (by rw [hph]; exact fun h => nomatch h)]
      exact (Bool.and_true _).symm
    | refused why =>
      rw [(Api.HostSession.applyReply_funded_or r.session key r.budget.fuel).resolve_right
        (by rw [hph]; exact fun h => nomatch h)]
      exact (Bool.and_true _).symm
  | control d =>
    show (Api.HostSession.advance r.session r.budget.fuel d).session.funded =
      (r.session.funded &&
        match Run.decisionOf r (.control d)
            (Api.HostSession.advance r.session r.budget.fuel d).phase with
        | some d => Run.readsOn r d
        | none => true)
    rw [Api.HostSession.advance_funded]
    cases hph : (Api.HostSession.advance r.session r.budget.fuel d).phase with
    | progressed =>
      obtain ⟨live, enough⟩ := Api.HostSession.advance_progressed r.session r.budget.fuel d hph
      show r.session.funded = (r.session.funded && (r.session.machine.stuck.isNone &&
        Run.enoughFor r.built.program r.built.table r.budget.fuel r.session.machine d))
      rw [live]
      show r.session.funded = (r.session.funded && (true && _))
      rw [show Run.enoughFor r.built.program r.built.table r.budget.fuel r.session.machine d = true
        from enough, Bool.and_true, Bool.and_true]
    | bound => exact (Bool.and_true _).symm
    | preflight => exact (Bool.and_true _).symm
    | applied => exact (Bool.and_true _).symm
    | frontier => exact (Bool.and_true _).symm
    | refused why => exact (Bool.and_true _).symm

/-- Step of `view_funded`: the tape reads past one run command when the command ends at no
frontier, its decision reads on, and the tape reads past the rest. -/
theorem tapeFrom_cons_isEmpty (r : Run) (c : Command) (rest : List Command) :
    (Run.tapeFrom r (c :: rest)).2.isEmpty =
      (!((Api.Runner.result r.runner c).phase == Phase.frontier) && rowReads r c &&
        (Run.tapeFrom (r.step c) rest).2.isEmpty) := by
  cases hfront : ((Api.Runner.result r.runner c).phase == Phase.frontier) with
  | true =>
    rw [Run.tapeFrom_frontier r c rest hfront]
    rfl
  | false =>
    cases hdec : Run.decisionOf r c (Api.Runner.result r.runner c).phase with
    | none =>
      rw [Run.tapeFrom_skip r c rest hfront hdec]
      show _ = (true && (match Run.decisionOf r c (Api.Runner.result r.runner c).phase with
        | some d => Run.readsOn r d
        | none => true) && _)
      rw [hdec]
      rfl
    | some d =>
      cases hreads : Run.readsOn r d with
      | false =>
        rw [Run.tapeFrom_stop r c rest d hfront hdec hreads]
        show false = (true && (match Run.decisionOf r c (Api.Runner.result r.runner c).phase with
          | some d => Run.readsOn r d
          | none => true) && _)
        rw [hdec]
        show false = (true && Run.readsOn r d && _)
        rw [hreads]
        rfl
      | true =>
        rw [Run.tapeFrom_take r c rest d hfront hdec hreads]
        show _ = (true && (match Run.decisionOf r c (Api.Runner.result r.runner c).phase with
          | some d => Run.readsOn r d
          | none => true) && _)
        rw [hdec]
        show _ = (true && Run.readsOn r d && _)
        rw [hreads]
        rfl

/-- The Boolean identity of one run command in `funded_play`. -/
theorem funded_step_bool (F b P q T : Bool) :
    ((F && b) && !(P || (q || false)) && T) = (F && !P && (!q && b && T)) := by
  cases F <;> cases b <;> cases P <;> cases q <;> cases T <;> rfl

/-- Step of `view_funded`: playing run commands keeps the view's test in step with the tape. The
session's bit and the absence of a frontier verdict, after the commands, are their values before
the commands and the tape's reading past every command. -/
theorem funded_play (r : Run) (cs : List Command) :
    ((r.play cs).session.funded && !(r.play cs).phases.any (· == Phase.frontier)) =
      (r.session.funded && !r.phases.any (· == Phase.frontier) &&
        (Run.tapeFrom r cs).2.isEmpty) := by
  induction cs generalizing r with
  | nil => exact (Bool.and_true _).symm
  | cons c rest ih =>
    rw [Run.play_cons, ih (r.step c), step_funded, Run.step_phases, List.any_append,
      List.any_cons, List.any_nil, tapeFrom_cons_isEmpty]
    exact funded_step_bool _ _ _ _ _

/-- **The view's flag is `funded`** (the session note's slice DM4). The view reads the session's
bit and the journal's verdicts, with no replay; `Run.funded` reads the tape of the run's own
journal from its fresh open. They agree on every live run.

Placement: concept `translation-simulation`; the proposed claim `view-funded`, a connector.
Consumer: `session_eq_ref` at `Live`, whose one premise a caller reads off the view. Reach: every
`Live`. It does not establish that a run is funded (`embedded-budget-sufficient`, an open part of
R12), or anything of a host's budget or of a lowered session. Unlocks: R6. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem view_funded (l : Live) : l.view.funded = Run.funded l.run := by
  have key := funded_play (Run.openedOf l.run) l.run.journal
  rw [show (Run.openedOf l.run).play l.run.journal = l.run from journal_replays l] at key
  show (l.run.session.funded && !l.run.phases.any (· == Phase.frontier)) =
    (Run.tapeFrom (Run.openedOf l.run) l.run.journal).2.isEmpty
  rw [key]
  rfl

end Effect4.Live
