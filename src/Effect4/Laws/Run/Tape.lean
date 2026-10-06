import Effect4.Run.Tape
import Effect4.Laws.Run
import Effect4.Laws.Run.Rows
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Run.Tape — the machine's tape of a journal, and its laws

`play_controls_eq_replay` (`src/Effect4/Laws/Run.lean`) says that control rows leave the raw
replay's machine. This module extends it to a journal that holds reply applications. The
declarations came from the scenario support (`Test/Dogfood/Scenario.lean`), each with its
statement and its proof unchanged (decisions row 284, point 5).

* **The tape.** `tapeFrom` reads the decisions that moved the machine off a journal: each
  control that progressed and each reply application. It stops at the first row that ends at
  a frontier, and at the first decision that the raw replay does not read past (`readsOn`).
  `tapeOf` is the tape of a run's own journal, read from the run's fresh open.
* **A journal's machine is the raw replay of its tape** (`tape_replays`, the pointer of the
  registry claim `run-tape-replay`), when the tape reads every row.
* **The journal's cut.** A journal whose tape stops has a completed prefix. That prefix and
  each position of the tape replay raw too (`tapeFrom_append`, `tapeFrom_cut`,
  `tapeFrom_cut_replays`, and `tapeFrom_position_replays`, the pointer of
  `journal-position-replay`).
* **A funded run.** `funded` is the budget premise of a statement over runs: the tape of the
  run's own journal leaves no row unread. `funded_replays` says what the premise gives (the
  pointer of `funded-run-replay`).

These four definitions are executable, and they stand in the law graph: `readsOn` calls
`Run.enoughFor` (`src/Effect4/Laws/Run.lean`), `tapeFrom` calls `readsOn`, and `tapeOf` and
`funded` call `tapeFrom`. The readings that need no such function are definitions of the core
(`src/Effect4/Run/Tape.lean`): the machine's view, a position, the decision of a row, the fresh
open and rest.

Placement. The concept is `translation-simulation`. `tape_replays` and `funded_replays` are
nodes of R8, and the four laws of the journal's cut are nodes of R13, each by its tag. Each
docstring gives its law's reach and what the law does not establish. No law here states the
machine after a stopped row, equal session ledgers, a continuation after a stop (decisions row
226), or anything of a generated engine. That a run is funded is the open claim
`embedded-budget-sufficient`.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Key Call Reply Phase BoundCall Session)
open Effect4.Api.Runner (Command)

/-! ## The tape -/

/-- Whether the raw replay takes this decision and reads on: the machine is live, and the step
has enough command fuel (`Run.enoughFor`, `src/Effect4/Laws/Run.lean`). -/
def readsOn (s : Run) (decision : Api.Decision) : Bool :=
  s.machine.stuck.isNone &&
    Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision

/-- The machine tape of rows played from a run: the positions, and the rows left unread. The
tape stops at the first row that ends at a frontier, and at the first decision the raw replay
does not read past. A frontier is never turned into a reply application: its rows stay unread. -/
def tapeFrom (s : Run) : List Command → List Position × List Command
  | [] => ([], [])
  | c :: rest =>
    let phase := (Api.Runner.result s.runner c).phase
    if phase == .frontier then ([], c :: rest)
    else
      match decisionOf s c phase with
      | none =>
        let tail := tapeFrom (s.step c) rest
        (tail.1, tail.2)
      | some decision =>
        if readsOn s decision then
          let tail := tapeFrom (s.step c) rest
          (⟨decision, s.step c⟩ :: tail.1, tail.2)
        else ([], c :: rest)

/-- The proposition of `tape_replays`. -/
def TapeReplays : Prop :=
  ∀ (s : Run) (rows : List Command), (tapeFrom s rows).2 = [] →
    (s.play rows).machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        ((tapeFrom s rows).1.map (·.decision)) s.machine)

/-! ## The proof of `tape_replays`

Each lemma below is a step of `tape_replays`, and that theorem is its one consumer. The first
three are facts of any session. The others read one row of a journal. -/

/-- Step of `tape_replays`: a successful preflight returns the reply's own answer decision. -/
theorem preflight_replyDecision {program : Api.Program} {table : RowTable}
    (s : Session program table) (reply : Reply) (decision : NativeDecision)
    (h : Api.HostSession.preflight s reply = .ok decision) : decision = replyDecision reply := by
  obtain ⟨bound, found, _, _, shape⟩ := Api.HostSession.preflight_envelope s reply decision h
  have test := List.find?_some found
  have same : bound.key = reply.key := of_decide_eq_true test
  rw [shape]
  show RunDecision.answerAsync bound.key.fiber bound.key.token reply.completion = _
  rw [same]
  rfl

/-- Step of `tape_replays`: an applied reply was stored at the key, and the machine it leaves is
the raw stepper's on that reply's answer decision. Retiring calls does not touch the machine. -/
theorem applyReply_applied_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (Api.HostSession.applyReply s key fuel).phase = .applied) :
    ∃ reply, Api.HostSession.readReply s.pending key = some reply ∧
      (Api.HostSession.applyReply s key fuel).session.machine =
        steppedBy program fuel table s.machine (replyDecision reply) := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases hactive : s.active.find? (fun b => b.key == key) with
    | none =>
      simp only [Api.HostSession.applyReply, hactive] at h
      cases h
    | some selected =>
      cases hreply : Api.HostSession.readReply s.pending key with
      | none =>
        simp only [Api.HostSession.applyReply, hactive, hreply] at h
        cases h
      | some reply =>
        cases hpre : Api.HostSession.preflight s reply with
        | error why =>
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre] at h
          cases h
        | ok decision =>
          have shape := preflight_replyDecision s reply decision hpre
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre] at h ⊢
          split at h
          · cases h
          · rename_i allowed
            split at h
            · rename_i removed
              refine ⟨reply, rfl, ?_⟩
              rw [if_neg allowed, if_pos removed, ← shape]
              rfl
            · cases h

/-- Step of `tape_replays`: a reply application ends at a frontier, applied or refused. -/
theorem applyReply_ends {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).phase = .frontier ∨
      (Api.HostSession.applyReply s key fuel).phase = .applied ∨
      ∃ why, (Api.HostSession.applyReply s key fuel).phase = .refused why := by
  cases fuel with
  | zero => exact Or.inl rfl
  | succ fuel =>
    cases hactive : s.active.find? (fun b => b.key == key) with
    | none =>
      exact Or.inr (Or.inr ⟨.noCall, by simp only [Api.HostSession.applyReply, hactive]⟩)
    | some selected =>
      cases hreply : Api.HostSession.readReply s.pending key with
      | none =>
        exact Or.inr (Or.inr ⟨.noCall, by
          simp only [Api.HostSession.applyReply, hactive, hreply]⟩)
      | some reply =>
        cases hpre : Api.HostSession.preflight s reply with
        | error why =>
          exact Or.inr (Or.inr ⟨why, by
            simp only [Api.HostSession.applyReply, hactive, hreply, hpre]⟩)
        | ok decision =>
          simp only [Api.HostSession.applyReply, hactive, hreply, hpre]
          split
          · exact Or.inr (Or.inr ⟨.protocol, rfl⟩)
          · split
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl

/-- Step of `tape_replays`: a row that ends at no frontier and gives no decision leaves the
machine as it was. -/
theorem step_keeps_machine (s : Run) (c : Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = none) :
    (s.step c).machine = s.machine := by
  cases c with
  | bind call token =>
    exact (congrArg Session.machine (Run.step_session_bind s call token)).trans
      (bindCall_inert s.session call token).1
  | submit reply =>
    exact (congrArg Session.machine (Run.step_session_submit s reply)).trans
      (submit_inert s.session reply).1
  | apply key =>
    change ((Api.HostSession.applyReply s.session key s.budget.fuel).phase == Phase.frontier) =
      false at hfront
    change decisionOf s (.apply key)
      (Api.HostSession.applyReply s.session key s.budget.fuel).phase = none at hdec
    rcases applyReply_ends s.session key s.budget.fuel with hph | hph | ⟨why, hph⟩
    · rw [hph] at hfront
      cases hfront
    · obtain ⟨reply, hread, _⟩ := applyReply_applied_machine s.session key s.budget.fuel hph
      rw [hph] at hdec
      simp only [decisionOf, hread, Option.map_some] at hdec
      cases hdec
    · exact (congrArg Session.machine (Run.step_session_apply s key)).trans
        (congrArg Session.machine
          (Api.Runner.applyReply_refused s.session key s.budget.fuel why hph))
  | control decision =>
    change ((Api.HostSession.advance s.session s.budget.fuel decision).phase == Phase.frontier) =
      false at hfront
    change decisionOf s (.control decision)
      (Api.HostSession.advance s.session s.budget.fuel decision).phase = none at hdec
    rcases Run.advance_step s.session s.budget.fuel decision with ⟨why, refused⟩ | ⟨_, stepped⟩
    · exact (congrArg Session.machine (Run.step_session_control s decision)).trans
        (congrArg (fun r => r.session.machine) refused)
    · rw [stepped] at hfront hdec
      cases henough : Run.enoughFor s.built.program s.built.table s.budget.fuel s.session.machine
          decision with
      | true =>
        rw [henough] at hdec
        cases hdec
      | false =>
        rw [henough] at hfront
        cases hfront

/-- Step of `tape_replays`: a row that gives a decision leaves the machine that the raw stepper
leaves on that decision. -/
theorem step_takes_decision (s : Run) (c : Command) (decision : Api.Decision)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision) :
    (s.step c).machine =
      steppedBy s.built.program s.budget.fuel s.built.table s.machine decision := by
  cases c with
  | bind call token =>
    generalize (Api.Runner.result s.runner (.bind call token)).phase = phase at hdec
    cases phase <;> cases hdec
  | submit reply =>
    generalize (Api.Runner.result s.runner (.submit reply)).phase = phase at hdec
    cases phase <;> cases hdec
  | apply key =>
    change decisionOf s (.apply key)
      (Api.HostSession.applyReply s.session key s.budget.fuel).phase = some decision at hdec
    generalize hph : (Api.HostSession.applyReply s.session key s.budget.fuel).phase = phase at hdec
    cases phase with
    | applied =>
      obtain ⟨reply, hread, hmachine⟩ :=
        applyReply_applied_machine s.session key s.budget.fuel hph
      simp only [decisionOf, hread, Option.map_some, Option.some.injEq] at hdec
      rw [← hdec]
      exact (congrArg Session.machine (Run.step_session_apply s key)).trans hmachine
    | bound => cases hdec
    | preflight => cases hdec
    | progressed => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec
  | control d =>
    change decisionOf s (.control d)
      (Api.HostSession.advance s.session s.budget.fuel d).phase = some decision at hdec
    generalize hph : (Api.HostSession.advance s.session s.budget.fuel d).phase = phase at hdec
    cases phase with
    | progressed =>
      obtain ⟨_, _, hmachine⟩ := Run.advance_progressed s.session s.budget.fuel d hph
      simp only [decisionOf, Option.some.injEq] at hdec
      rw [← hdec]
      exact (congrArg Session.machine (Run.step_session_control s d)).trans hmachine
    | bound => cases hdec
    | preflight => cases hdec
    | applied => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec

/-- Step of `tape_replays`: the tape stops at a row that ends at a frontier. -/
theorem tapeFrom_frontier (s : Run) (c : Command) (rest : List Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = true) :
    tapeFrom s (c :: rest) = ([], c :: rest) := by
  rw [tapeFrom]
  exact if_pos hfront

/-- Step of `tape_replays`: the tape passes a row that gives no decision. -/
theorem tapeFrom_skip (s : Run) (c : Command) (rest : List Command)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = none) :
    tapeFrom s (c :: rest) = tapeFrom (s.step c) rest := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec]

/-- Step of `tape_replays`: the tape takes a decision that the raw replay reads past. -/
theorem tapeFrom_take (s : Run) (c : Command) (rest : List Command) (decision : Api.Decision)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision)
    (hreads : readsOn s decision = true) :
    tapeFrom s (c :: rest) =
      (⟨decision, s.step c⟩ :: (tapeFrom (s.step c) rest).1, (tapeFrom (s.step c) rest).2) := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec, hreads, if_true]

/-- Step of `tape_replays`: the tape stops at a decision that the raw replay does not read
past. -/
theorem tapeFrom_stop (s : Run) (c : Command) (rest : List Command) (decision : Api.Decision)
    (hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) = false)
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some decision)
    (hreads : readsOn s decision = false) :
    tapeFrom s (c :: rest) = ([], c :: rest) := by
  rw [tapeFrom]
  simp only [hfront, Bool.false_eq_true, if_false, hdec, hreads]

/-- **A journal's machine is the raw replay of its tape.** When the tape reads every row, the
machine that the journal leaves is the machine that the raw frame replay leaves on the tape's
decisions, at the same table and budgets. It is the machine clause of a lowered run: a replay of
the machine alone needs the tape, not the session. Reach: any run, any rows whose tape reads to
the end: no row at a frontier, and every decision taken at a live machine with enough fuel. It
needs no premise on the session, because the tape holds the decision that the session hands the
machine: a reply's own answer decision (`replyDecision`). It does not establish equal session
ledgers: the raw replay has none. It does not reach a journal that stops at a frontier, and it
says nothing of a lowered engine: that link is the finite comparison of
`ocaml/engine/test/scenarios/test_scenarios.ml`. It extends `play_controls_eq_replay`
(`src/Effect4/Laws/Run.lean`) from control rows to reply applications. Concept
`translation-simulation`, R8. Consumer: the lowered runs of `Test/Dogfood/Scenario/Lowered.lean`,
whose finite runs check it at every position of every fixture. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem tape_replays : TapeReplays := by
  intro s rows h
  induction rows generalizing s with
  | nil => exact (Run.machineOf_nil _ _ _ _).symm
  | cons c rest ih =>
    rw [Run.play_cons]
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at h
      cases h
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at h ⊢
        rw [ih (s.step c) h, Run.step_built, Run.step_budget, step_keeps_machine s c hfront hdec]
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at h
          cases h
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at h ⊢
          have live : s.machine.stuck.isNone = true ∧
              Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision =
                true :=
            Bool.and_eq_true_iff.mp hreads
          rw [ih (s.step c) h, Run.step_built, Run.step_budget,
            step_takes_decision s c decision hdec, List.map_cons,
            Run.replayFrom_cons _ _ _ _ _ _ (Option.isNone_iff_eq_none.mp live.1) live.2]

/-! ## The journal's cut, and its positions

`tape_replays` reads a journal whose tape reads every row. The four laws below say what a
prefix of any journal gives. `tapeFrom` splits a journal into a completed prefix and the rows
that it leaves unread. That split is the journal's cut, and it is no cut of the semantics
registry.

* **A stopped row** is the first unread row. It ends at a frontier (`tapeFrom_frontier`), or
  it gives a decision that the raw replay does not read past (`tapeFrom_stop`). A control that
  progressed always reads on (`Run.advance_progressed`), so a row of the second kind is a reply
  application that the session applied. The record `cuts` holds one: the command budget did not
  cover its step.
* **The completed prefix** ends before the stopped row. It may end with rows that give no
  decision, after its last position.

Each law holds for every run and every list of rows: no premise asks for a recorded run, a
typed program or a tape that reads to its end. The stop conditions are `tapeFrom`'s own. A
stopped row may change the machine before it reports its frontier. No law here says what that
machine is, and a second run command on it is no continuation of the first (decisions row
226). Concept `translation-simulation`. The laws stand at R13, beside `journal_replays`
(`src/Effect4/Laws/Run.lean`): the rows of a journal's prefix give the raw replay's machine.
They serve R8's replay view, the views of a lowered run (`shown_views_opened`,
`Test/Dogfood/Scenario/Tape.lean`). Their controls are the record `cuts` of that module. -/

/-- **The tape of a journal in two parts.** When the tape of the first part reads every row,
the tape of `a ++ b` is the positions of `a`, then the tape of `b` from the run after `a`. When
the tape of `a` stops, the tape of `a ++ b` holds the same positions, and the rows of `b` join
the unread rows: no row of `b` is read. Reach: any run and any two lists of rows. It does not
establish what the machine is after a stopped row, and it reads no row after one. Concept
`translation-simulation`, R13: a journal's tape splits where `Run.play_append` splits its run.
Consumer: no theorem of this module uses it. It is the law of a driver that plays a script in
parts, and the record `cuts` (`Test/Dogfood/Scenario/Tape.lean`) holds its controls. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_append (s : Run) (a b : List Command) :
    tapeFrom s (a ++ b) =
      if (tapeFrom s a).2 = [] then
        ((tapeFrom s a).1 ++ (tapeFrom (s.play a) b).1,
          (tapeFrom (s.play a) b).2)
      else ((tapeFrom s a).1, (tapeFrom s a).2 ++ b) := by
  induction a generalizing s with
  | nil => rfl
  | cons c rest ih =>
    rw [List.cons_append, Run.play_cons]
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c (rest ++ b) hfront, tapeFrom_frontier s c rest hfront]
      exact (if_neg (List.cons_ne_nil c rest)).symm
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c (rest ++ b) hfront hdec, tapeFrom_skip s c rest hfront hdec]
        exact ih (s.step c)
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c (rest ++ b) decision hfront hdec hreads,
            tapeFrom_stop s c rest decision hfront hdec hreads]
          exact (if_neg (List.cons_ne_nil c rest)).symm
        | true =>
          rw [tapeFrom_take s c (rest ++ b) decision hfront hdec hreads,
            tapeFrom_take s c rest decision hfront hdec hreads, ih (s.step c)]
          split
          · rfl
          · rfl

/-- **The journal's cut.** A journal is a completed prefix, then the rows that its tape leaves
unread. The tape of the prefix alone holds the same positions, and it leaves no row unread. So
the positions of a journal are read from the completed prefix, and a stopped row is the first
row after it. Reach: any run and any rows. A journal whose tape reads every row is its own
completed prefix. It does not establish the machine after the prefix: `tapeFrom_cut_replays`
adds that clause. Concept `translation-simulation`, R13. Consumer: `tapeFrom_cut_replays`. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_cut (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, []) := by
  induction rows generalizing s with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c rest ih =>
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront]
      exact ⟨[], rfl, rfl⟩
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        obtain ⟨done, hrows, htape⟩ := ih (s.step c)
        rw [tapeFrom_skip s c rest hfront hdec]
        refine ⟨c :: done, congrArg (List.cons c) hrows, ?_⟩
        rw [tapeFrom_skip s c done hfront hdec]
        exact htape
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads]
          exact ⟨[], rfl, rfl⟩
        | true =>
          obtain ⟨done, hrows, htape⟩ := ih (s.step c)
          rw [tapeFrom_take s c rest decision hfront hdec hreads]
          refine ⟨c :: done, congrArg (List.cons c) hrows, ?_⟩
          rw [tapeFrom_take s c done decision hfront hdec hreads, htape]

/-- **The machine after the completed prefix is the raw replay of its tape.** A journal is a
completed prefix, then its unread rows (`tapeFrom_cut`). The machine that the prefix leaves is
the machine that the raw frame replay leaves on the decisions of the journal's positions, from
the run's own machine, at the same table and budgets. Reach: any run and any rows: the tape may
stop. It does not establish the machine after a stopped row. That row may change the machine
before it reports its frontier, and the completed prefix ends before it. It does not establish
equal session ledgers, since the raw replay has none. It says nothing of resumable ownership
(R12, decisions row 226) or of a generated engine. Concept `translation-simulation`, R13: it is
`tape_replays` on the completed prefix. Consumer: the controls of the record `cuts`
(`Test/Dogfood/Scenario/Tape.lean`), and later the laws of the scenario driver. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_cut_replays (s : Run) (rows : List Command) :
    ∃ done, rows = done ++ (tapeFrom s rows).2 ∧
      tapeFrom s done = ((tapeFrom s rows).1, []) ∧
      (s.play done).machine =
        Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
          ((tapeFrom s rows).1.map (·.decision)) s.machine) := by
  obtain ⟨done, hrows, htape⟩ := tapeFrom_cut s rows
  have replayed := tape_replays s done (congrArg Prod.snd htape)
  rw [htape] at replayed
  exact ⟨done, hrows, htape, replayed⟩

/-- Step of `tapeFrom_position_replays`: a prefix of the journal ends at the row of position
`i`. Playing that prefix reaches the position's own run, with every row of the prefix in its
journal: the rows that gave no decision are played too. The tape of the prefix alone is the
first `i + 1` positions, with no row unread. So `tape_replays` reads the machine off that
prefix, and the position law needs no second induction over replies. -/
theorem tapeFrom_position_prefix (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (found : (tapeFrom s rows).1[i]? = some position) :
    ∃ done tail, rows = done ++ tail ∧
      s.play done = position.after ∧
      tapeFrom s done = ((tapeFrom s rows).1.take (i + 1), []) := by
  induction rows generalizing s i with
  | nil => cases found
  | cons c rest ih =>
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at found
      cases found
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at found ⊢
        obtain ⟨done, tail, hrows, hafter, htape⟩ := ih (s.step c) i found
        refine ⟨c :: done, tail, congrArg (List.cons c) hrows, ?_, ?_⟩
        · rw [Run.play_cons]
          exact hafter
        · rw [tapeFrom_skip s c done hfront hdec]
          exact htape
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at found
          cases found
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at found ⊢
          cases i with
          | zero =>
            cases found
            refine ⟨[c], rest, rfl, rfl, ?_⟩
            rw [tapeFrom_take s c [] decision hfront hdec hreads]
            rfl
          | succ j =>
            obtain ⟨done, tail, hrows, hafter, htape⟩ := ih (s.step c) j found
            refine ⟨c :: done, tail, congrArg (List.cons c) hrows, ?_, ?_⟩
            · rw [Run.play_cons]
              exact hafter
            · rw [tapeFrom_take s c done decision hfront hdec hreads, htape]
              rfl

/-- **The machine after a position is the raw replay of the decisions up to it.** At position
`i` of a journal's tape, the machine of the run after the position's row is the machine that the
raw frame replay leaves on the first `i + 1` decisions. The replay starts at the machine of the
run that the tape was read from, at the same table and budgets. Reach: any run, any rows and any
position of the tape. The tape need not read every row: a later stopped row adds no position.
It does not establish the machine after a stopped row, equal session ledgers, or anything of a
generated engine. It replays from the run's own machine: a replay from a new load needs a fresh
open, which the consumer states. Concept `translation-simulation`, R13: it is `tape_replays` on
the prefix that ends at the position's row. Consumer: `shown_views_opened`
(`Test/Dogfood/Scenario/Tape.lean`), the views of a lowered run. -/
@[semantics "translation-simulation" (requirement := R13)]
theorem tapeFrom_position_replays (s : Run) (rows : List Command)
    (i : Nat) (position : Position)
    (found : (tapeFrom s rows).1[i]? = some position) :
    position.after.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel
        (((tapeFrom s rows).1.take (i + 1)).map (·.decision)) s.machine) := by
  obtain ⟨done, tail, _, hafter, htape⟩ := tapeFrom_position_prefix s rows i position found
  have replayed := tape_replays s done (congrArg Prod.snd htape)
  rw [htape, hafter] at replayed
  exact replayed

/-! ## A funded run

A statement over a scenario's runs takes its budget as a premise. This section gives that
premise one name, `funded`, and ties it to a proved law of the tape. The fresh open that the
tape is read from is `openedOf`, a definition of the core (`src/Effect4/Run/Tape.lean`). -/

/-- The decisions of a run's tape: the decisions that moved the machine, read off the run's own
journal from its fresh open. -/
def tapeOf (s : Run) : List Api.Decision := (tapeFrom (openedOf s) s.journal).1.map (·.decision)

/-- **A funded run: no task of the run was cut by its budget.** The tape of the run's own
journal, read from the run's fresh open, leaves no row unread. So the journal holds no stopped
row: no row ends at a frontier, and each decision is taken at a live machine with enough command
fuel (`tapeFrom`, `readsOn`).

The journal's verdicts alone do not decide it. A reply application has the verdict `applied` as
soon as its call's guard is gone, whatever fuel its step had left (`applyReply`,
`src/Effect4/Api/HostSession.lean`). Only a control reports its sufficiency, as `progressed` or
`frontier` (`advance`, in the same file). The tape asks `Run.enoughFor` of each decision, so it
stops at an applied reply application that the budget cut (`tapeFrom_stop`).

It is the budget premise of a law of a whole run. Decisions row 226 excludes a cut inside an
owned operation from the first profile. The proposed claim `embedded-budget-sufficient` (an open
part of R12) is to supply the premise from a program's own bound. Until then a statement over
runs takes it by this one name. `funded_replays` says what the premise gives. -/
def funded (s : Run) : Bool := (tapeFrom (openedOf s) s.journal).2.isEmpty

/-- **The machine of a funded run is the raw replay of its tape's decisions.** For a recorded
run whose journal holds no stopped row, the machine is the machine that the raw frame replay
leaves on the decisions of the run's tape, from the program's own load, at the run's table and
budgets. Reach: any run that was opened and then played (`Run.Reached`), under `funded`. It is
one application of `tape_replays` at the run's fresh open, with `Run.journal_replays`. It does
not establish that a run is funded: that is the open claim `embedded-budget-sufficient`. It does
not establish equal session ledgers, and it says nothing of a run with a stopped row. Concept
`translation-simulation`, R8. Consumer: each statement over runs that takes `funded` as its
budget premise, the planned goals of `Test/Dogfood/Scenario/QueueWorkers.lean` first. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem funded_replays (s : Run) (recorded : Run.Reached s) (h : funded s = true) :
    s.machine =
      Run.machineOf (Run.replayFrom s.built.program s.built.table s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel)) := by
  have read : (tapeFrom (openedOf s) s.journal).2 = [] := List.isEmpty_iff.mp h
  have replayed := tape_replays (openedOf s) s.journal read
  rw [show (openedOf s).play s.journal = s from Run.journal_replays s recorded,
    show (openedOf s).machine = Api.load s.built.program s.budget.compileFuel from
      Run.open_machine s.built s.id s.budget s.profile] at replayed
  exact replayed

end Effect4.Run
