import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Run.Tape
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Program.Agreement.Hosted

/-!
# Api.SessionMeaning — the meaning under a run's reply tape is the run's observation (DI-69)

Slice H7 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). The session's
side of DI-69: a run's reply tape (`appliedExits`), the premise that a host drives it
(`hostDriven`), and the theorem `denoteRows_eq_session` on the fragment `StraightRows`, which
admits `catchIf` (the owner, row 310). Its proof is the packet's slice H8, in three layers:

* the local run with calls goes where the meaning goes (`localRunC_compile`,
  `Laws/Program/Agreement/Calls.lean`);
* each host decision keeps the machine in a settled form whose position the local run reaches,
  reading one reply for each answer (`holds_evaluate`, `holds_flush`, `holds_answer`,
  `Laws/Program/Agreement/Hosted.lean`);
* the session applies a reply only at a guard the machine waits on, on a host row of the table
  (`tapeFrom_answered`, here), so a recorded run's tape is a tape of such decisions.

The local run with calls asks a host, a comodel of the row signature (`Effects.Comodel`); the
reply tape is one host (`tapeHost`). So the same layers give **H9**, `denoteRows_eq_session_host`:
for a finished run, under any host whose answers are the run's (`HostAnswered`), the run of the
call tree under that host is the run's observation. H8 is the instance at the reply host.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Api.HostSession (Key Reply Phase Session)
open Effect4.Api.Runner (Command)

/-- A decision that a host hands a one-fiber run: the root's evaluation, a flush, or an answer
that holds an exit. An interruption, a clock step and a delayed cell read are not. -/
def hostDecision : Api.Decision → Bool
  | .answerAsync _ _ (.ofExit _) => true
  | decision => decision == Api.evaluate || decision == Api.flush

/-- The reply tape of a decision tape: the exits of its answer decisions, in order. -/
def exitsOf (tape : List Api.Decision) : ReplyTape :=
  tape.filterMap fun
    | .answerAsync _ _ (.ofExit ex) => some ex
    | _ => none

/-- The reply tape of a run: the exits of the replies that the session applied, in order. -/
def appliedExits (s : Run) : ReplyTape := exitsOf (tapeOf s)

/-- A run that a host drives: each decision of its tape is a host's (`hostDecision`). The
premise reads the tape, as both sides of the statement do: a row that the session refuses, and
a reply that it never applies, hand the machine nothing. -/
def hostDriven (s : Run) : Bool := (tapeOf s).all hostDecision

/-- The proposition of `denoteRows_eq_session`, on the fragment `frag`. -/
def DenoteRowsEqSession (frag : RowTable → NativeEff → Bool) : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    frag s.built.table s.built.program = true →
    meaningRows s.built.table s.built.program [] Stores.empty (appliedExits s) =
      s.exit.map fun ex => ((ex, s.machine.state), [])

/-! ## A reply the session applies is at a guard the machine waits on -/

/-- Step of `denoteRows_eq_session`: a reply that passes the session's preflight is at a guard the
machine waits on, on a host row the table registers (`admitted_row`, `acceptAtInstance_sound`). -/
theorem preflight_row {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) (decision : NativeDecision)
    (h : Api.HostSession.preflight s reply = .ok decision) :
    ∃ i v row, Program.requestOf s.machine reply.key.fiber reply.key.token = some (.external i, v) ∧
      externalRow table i = some row := by
  unfold Api.HostSession.preflight at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i bound hbound
        have hb := List.find?_some hbound
        have same : bound.key = reply.key := beq_iff_eq.mp hb
        rw [← same]
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · next d hacc =>
              have henv := acceptReply_envelope table s.machine (bound.record reply) d hacc
              obtain ⟨i, v, row, hreq, hrow, -⟩ :=
                admitted_row table s.machine _ _ _ henv.2.2
              exact ⟨i, v, row, hreq, hrow⟩
            · split at h
              · next d hinst =>
                obtain ⟨⟨-, hreq, i, row, -, -, hop, hrow, -⟩, -⟩ :=
                  acceptAtInstance_sound table _ s.machine (bound.record reply) d hinst
                refine ⟨i, (bound.record reply).request, row, ?_, hrow⟩
                rw [← hop]
                exact hreq
              · cases h

/-- Step of `denoteRows_eq_session`: an applied reply passed the preflight. -/
theorem applyReply_applied_preflight {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat)
    (h : (Api.HostSession.applyReply s key fuel).phase = .applied) :
    ∃ reply decision, Api.HostSession.readReply s.pending key = some reply ∧
      Api.HostSession.preflight s reply = .ok decision := by
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
        | ok decision => exact ⟨reply, decision, rfl, hpre⟩

/-- Step of `denoteRows_eq_session`: the answer decision a row gives is at a guard the machine
waits on, on a host row the table registers. A reply application passed the preflight; a control never answers (`advance` refuses a
direct answer); a receipt row gives no decision. -/
theorem decisionOf_answer_row (s : Run) (c : Command) {f : FiberId} {t : Nat}
    {a : Completion Val Err Defect FiberId Ann}
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some (.answerAsync f t a)) :
    ∃ i v row, Program.requestOf s.machine f t = some (.external i, v) ∧
      externalRow s.built.table i = some row := by
  cases c with
  | bind call token =>
    generalize (Api.Runner.result s.runner (.bind call token)).phase = phase at hdec
    cases phase <;> cases hdec
  | submit reply =>
    generalize (Api.Runner.result s.runner (.submit reply)).phase = phase at hdec
    cases phase <;> cases hdec
  | apply key =>
    change decisionOf s (.apply key)
      (Api.HostSession.applyReply s.session key s.budget.fuel).phase = _ at hdec
    generalize hph : (Api.HostSession.applyReply s.session key s.budget.fuel).phase = phase at hdec
    cases phase with
    | applied =>
      obtain ⟨reply, d, hread, hpre⟩ :=
        applyReply_applied_preflight s.session key s.budget.fuel hph
      simp only [decisionOf, hread, Option.map_some, Option.some.injEq, replyDecision,
        RunDecision.answerAsync.injEq] at hdec
      obtain ⟨rfl, rfl, -⟩ := hdec
      exact preflight_row s.session reply d hpre
    | bound => cases hdec
    | preflight => cases hdec
    | progressed => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec
  | control d =>
    change decisionOf s (.control d)
      (Api.HostSession.advance s.session s.budget.fuel d).phase = _ at hdec
    generalize hph : (Api.HostSession.advance s.session s.budget.fuel d).phase = phase at hdec
    cases phase with
    | progressed =>
      simp only [decisionOf, Option.some.injEq] at hdec
      subst hdec
      simp only [Api.HostSession.advance] at hph
      cases hph
    | bound => cases hdec
    | preflight => cases hdec
    | applied => cases hdec
    | frontier => cases hdec
    | refused why => cases hdec

/-- Each decision of a tape is taken at a live machine with a true receipt, and each answer is at
a guard the machine waits on, on a host row the table registers. -/
def Answered (program : Api.Program) (table : RowTable) (fuel : Nat) :
    List Api.Decision → Api.Machine → Prop
  | [], _ => True
  | d :: T, m => m.stuck = none ∧ Run.enoughFor program table fuel m d = true ∧
      (∀ f t a, d = .answerAsync f t a → ∃ i v row,
        Program.requestOf m f t = some (.external i, v) ∧ externalRow table i = some row) ∧
      Answered program table fuel T (steppedBy program fuel table m d)

/-- **The tape of a journal is answered** (a step of `denoteRows_eq_session`). When the tape reads
every row, each of its decisions is taken at a live machine with a true receipt, and each answer
is at a guard the machine waits on. The induction is `tape_replays`'s. -/
theorem tapeFrom_answered (s : Run) (rows : List Command) (h : (tapeFrom s rows).2 = []) :
    Answered s.built.program s.built.table s.budget.fuel ((tapeFrom s rows).1.map (·.decision))
      s.machine := by
  induction rows generalizing s with
  | nil => trivial
  | cons c rest ih =>
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at h
      cases h
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at h ⊢
        have hrest := ih (s.step c) h
        rwa [Run.step_built, Run.step_budget, step_keeps_machine s c hfront hdec] at hrest
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at h
          cases h
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at h ⊢
          have live := Bool.and_eq_true_iff.mp hreads
          have hrest := ih (s.step c) h
          rw [Run.step_built, Run.step_budget, step_takes_decision s c decision hdec] at hrest
          refine ⟨Option.isNone_iff_eq_none.mp live.1, live.2, ?_, hrest⟩
          rintro f t a rfl
          exact decisionOf_answer_row s c hdec

/-! ## The tape of a host's decisions, through the machine -/

/-- **The answers of a tape are a host's**: at each answer decision, the host, at its state,
answers the machine's request with the decision's exit, and its state moves on; other decisions
leave the host's state alone. The host's state goes from `st` to `st'` along the tape. -/
def HostAnswered (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (program : Api.Program) (fuel : Nat) : List Api.Decision → Api.Machine → σ → σ → Prop
  | [], _, st, st' => st' = st
  | .answerAsync f t (.ofExit ex) :: T, m, st, st'' =>
    ∃ i v, ∃ (hi : i < table.length), ∃ st',
      Program.requestOf m f t = some (.external i, v) ∧ host.answer ⟨⟨i, hi⟩, v⟩ st = some (ex, st') ∧
      HostAnswered table host program fuel T
        (steppedBy program fuel table m (.answerAsync f t (.ofExit ex))) st' st''
  | d :: T, m, st, st'' => HostAnswered table host program fuel T (steppedBy program fuel table m d) st st''

/-- Two exits are one, as a test. -/
def exitEq (a b : ExitV) : Bool := decide (a = b)

theorem eq_of_exitEq {a b : ExitV} (h : exitEq a b = true) : a = b := of_decide_eq_true h

/-- **Check that a tape's answers are a host's**, by running the host along the tape: the host's
final state, or `none` where an answer decision's exit is not what the host gives the machine's
request. Sound for `HostAnswered` (`hostAnsweredCheck_sound`), so a finite evaluation that it
returns the run's host state brings a run under H9. -/
def hostAnsweredCheck (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (program : Api.Program) (fuel : Nat) : List Api.Decision → Api.Machine → σ → Option σ
  | [], _, st => some st
  | .answerAsync f t (.ofExit ex) :: T, m, st =>
    match Program.requestOf m f t with
    | some (.external i, v) =>
      if hi : i < table.length then
        match host.answer ⟨⟨i, hi⟩, v⟩ st with
        | some (ex', st') =>
          if exitEq ex' ex = true then
            hostAnsweredCheck table host program fuel T
              (steppedBy program fuel table m (.answerAsync f t (.ofExit ex))) st'
          else none
        | none => none
      else none
    | _ => none
  | d :: T, m, st => hostAnsweredCheck table host program fuel T (steppedBy program fuel table m d) st

/-- **The check is sound**: where it returns the host's final state, the tape's answers are the
host's. -/
theorem hostAnsweredCheck_sound (table : RowTable) {σ : Type}
    (host : Effects.Comodel (RowSig table) σ) (program : Api.Program) (fuel : Nat) :
    ∀ (T : List Api.Decision) (m : Api.Machine) (st st' : σ),
      hostAnsweredCheck table host program fuel T m st = some st' →
      HostAnswered table host program fuel T m st st'
  | [], _, st, st', h => by
    simp only [hostAnsweredCheck, Option.some.injEq] at h
    exact h.symm
  | .answerAsync f t (.ofExit ex) :: T, m, st, st'', h => by
    simp only [hostAnsweredCheck] at h
    split at h
    · next i v hreq =>
      split at h
      · next hi =>
        split at h
        · next ex' st' hans =>
          split at h
          · next hb =>
            have heq := eq_of_exitEq hb
            subst heq
            exact ⟨i, v, hi, st', hreq, hans,
              hostAnsweredCheck_sound table host program fuel T _ st' st'' h⟩
          · cases h
        · cases h
      · cases h
    · cases h
  | .answerAsync f t (.ofRefGet c) :: T, m, st, st', h =>
    hostAnsweredCheck_sound table host program fuel T _ st st' h
  | .fire _ :: T, m, st, st', h | .flush :: T, m, st, st', h | .evaluate _ :: T, m, st, st', h
  | .yieldVerdict _ _ :: T, m, st, st', h | .interruptFrom _ _ _ :: T, m, st, st', h
  | .installMiddleware :: T, m, st, st', h | .advance _ :: T, m, st, st', h =>
    hostAnsweredCheck_sound table host program fuel T _ st st' h

/-- **A driver's host as a comodel** of the row signature: the reactor answers a row's request
from its state; an answer that is no exit is no answer here. -/
def reactorHost (table : RowTable) {σ : Type} (r : Run.Reactor σ) : Effects.Comodel (RowSig table) σ where
  answer op st :=
    match externalRow table op.1.val with
    | none => none
    | some row =>
      match r row op.2 st with
      | some (.ofExit ex, next) => some (ex, next)
      | _ => none

/-- **A tape of a host's answered decisions keeps the machine's forms** (a step of
`denoteRows_eq_session` and of `denoteRows_eq_session_host`): from a machine in a form of
`Holds` at a position, the raw replay of the tape ends in such a form, and the local run with
calls under the host leads from the first position to the last, the host's state going from `st`
to `st'`. -/
theorem tape_holds_host (program : Api.Program) (table : RowTable) (fuel : Nat)
    (hroot : LoopedRows program = true) (cf : Nat) {σ : Type}
    (host : Effects.Comodel (RowSig table) σ) :
    ∀ (T : List Api.Decision) (m : Api.Machine) (p : Pos) (st st' : σ), Holds program cf m p →
      Answered program table fuel T m → T.all hostDecision = true →
      HostAnswered table host program fuel T m st st' →
      ∃ p', Holds program cf (Run.machineOf (Run.replayFrom program table fuel T m)) p' ∧
        Leads host program p st p' st'
  | [], m, p, st, st', hH, _, _, hA => by
    refine ⟨p, by rw [Run.machineOf_nil]; exact hH, ?_⟩
    rw [show st' = st from hA]
    exact Leads.refl p st
  | d :: T, m, p, st, st'', hH, ⟨hs, hen, _, hrest⟩, hall, hA => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    rw [Run.replayFrom_cons program table fuel d T m hs hen]
    have hd := hall.1
    cases d with
    | answerAsync f t a =>
      cases a with
      | ofExit ex =>
        obtain ⟨i, v, hi, st', hrq, hans, hA'⟩ := hA
        have hne : Program.requestOf m f t ≠ none := by
          rw [hrq]
          exact Option.some_ne_none _
        obtain ⟨p₁, hH₁, hL₁⟩ := holds_answer program hroot cf hH hne hen
        obtain ⟨p', hH', hL'⟩ :=
          tape_holds_host program table fuel hroot cf host T _ p₁ st' st'' hH₁ hrest hall.2 hA'
        exact ⟨p', hH', (hL₁ host st st' ((hH.hostAnswer_eq hrq hi st).trans hans)).trans hL'⟩
      | ofRefGet _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
          reduceCtorEq, or_self] at hd
    | evaluate id =>
      simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
        RunDecision.evaluate.injEq, reduceCtorEq, or_false] at hd
      subst hd
      obtain ⟨p₁, hH₁, hL₁⟩ := holds_evaluate program hroot cf hH hen
      obtain ⟨p', hH', hL'⟩ :=
        tape_holds_host program table fuel hroot cf host T _ p₁ st st'' hH₁ hrest hall.2 hA
      exact ⟨p', hH', (hL₁ host st).trans hL'⟩
    | flush =>
      obtain ⟨p₁, hH₁, hL₁⟩ := holds_flush program hroot cf hH hen
      obtain ⟨p', hH', hL'⟩ :=
        tape_holds_host program table fuel hroot cf host T _ p₁ st st'' hH₁ hrest hall.2 hA
      exact ⟨p', hH', (hL₁ host st).trans hL'⟩
    | _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
        reduceCtorEq, or_self] at hd

/-- **The tape's own exits are the reply host's answers** along an answered tape. -/
theorem answered_hostAnswered (program : Api.Program) (table : RowTable) (fuel : Nat) :
    ∀ (T : List Api.Decision) (m : Api.Machine), Answered program table fuel T m →
      T.all hostDecision = true → ∀ r,
      HostAnswered table (tapeHost table) program fuel T m (exitsOf T ++ r) r
  | [], _, _, _, _ => rfl
  | d :: T, m, ⟨_, _, hreq, hrest⟩, hall, r => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    have hd := hall.1
    cases d with
    | answerAsync f t a =>
      cases a with
      | ofExit ex =>
        obtain ⟨i, v, row, hrq, hrow⟩ := hreq f t _ rfl
        exact ⟨i, v, lt_of_externalRow hrow, exitsOf T ++ r, hrq, rfl,
          answered_hostAnswered program table fuel T _ hrest hall.2 r⟩
      | ofRefGet _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
          reduceCtorEq, or_self] at hd
    | evaluate id => exact answered_hostAnswered program table fuel T _ hrest hall.2 r
    | flush => exact answered_hostAnswered program table fuel T _ hrest hall.2 r
    | _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
        reduceCtorEq, or_self] at hd

/-- **A tape of a host's answered decisions keeps the machine's forms, reading the tape's own
exits to the end** (a step of `denoteRows_eq_session`): `tape_holds_host` at the reply host. -/
theorem tape_holds (program : Api.Program) (table : RowTable) (fuel : Nat)
    (hroot : LoopedRows program = true) (cf : Nat) (T : List Api.Decision) (m : Api.Machine)
    (p : Pos) (hH : Holds program cf m p) (hans : Answered program table fuel T m)
    (hall : T.all hostDecision = true) :
    ∃ p', Holds program cf (Run.machineOf (Run.replayFrom program table fuel T m)) p' ∧
      Leads (tapeHost table) program p (exitsOf T) p' [] := by
  have hA := answered_hostAnswered program table fuel T m hans hall []
  rw [List.append_nil] at hA
  exact tape_holds_host program table fuel hroot cf (tapeHost table) T m p (exitsOf T) [] hH hans
    hall hA

/-- A session's reading holds the session's machine. -/
theorem inspect_keeps_machine {program : Api.Program} {table : RowTable}
    (s : Session program table) : (Api.HostSession.inspect s).machine = s.machine := by
  have h := Run.machineOf_nil program table 0 s.machine
  unfold Run.replayFrom at h
  unfold Api.HostSession.inspect
  split
  · next m hr =>
    rw [hr] at h
    exact h
  · next why m hr =>
    rw [hr] at h
    exact h
  · next why m hr =>
    rw [hr] at h
    exact h

/-- **The meaning under a run's reply tape is the run's observation** (DI-69). For a recorded
run of a program of the fragment, the meaning of the program under the run's reply tape is the
root's exit with the stores, and the reply tape is read to its end. Where the root has no exit,
the meaning is the frontier. Reach: `StraightRows`, one fiber, every compile budget; a run that
is funded, at rest and driven by a host: its controls evaluate the root or flush, and each reply
holds an exit. It does not establish the same for a run with an interruption, a clock step, a
delayed cell read or a handle row: each has a red control. It says nothing of a fiber, a scope or
a loop. Concept `translation-simulation`, claim `rows-denotation-session`, role simulation;
requirement R6. Consumer: a fact of a program's call tree, read on a run.

The proof (slice H8): the session's tape is answered (`tapeFrom_answered`); each decision keeps
the machine in a settled form whose position the local run with calls reaches (`tape_holds`); a
machine at rest is exited or waits on a call; and there the meaning is what the local run says
(`meaning_settled`), the compile's frontier being a divergence that rest excludes. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteRows_eq_session : DenoteRowsEqSession StraightRows := by
  intro s hreach hfund hrest hhost hfrag
  have hroot := LoopedRows.of_straightRows s.built.program hfrag
  have hmach := funded_replays s hreach hfund
  have hans : Answered s.built.program s.built.table s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) := by
    have read : (tapeFrom (openedOf s) s.journal).2 = [] := List.isEmpty_iff.mp hfund
    have h := tapeFrom_answered (openedOf s) s.journal read
    rw [show (openedOf s).machine = Api.load s.built.program s.budget.compileFuel from
      Run.open_machine s.built s.id s.budget s.profile] at h
    exact h
  obtain ⟨p, hH, hL⟩ := tape_holds s.built.program s.built.table s.budget.fuel hroot
    s.budget.compileFuel (tapeOf s) _ _ (Or.inl ⟨rfl, rfl⟩) hans hhost
  rw [← hmach] at hH
  simp only [atRest, Bool.and_eq_true] at hrest
  have hexit : s.exit = (s.machine.fiber? Api.root).bind RunFiber.exit := by
    show ((Api.HostSession.inspect s.session).machine.fiber? Api.root).bind RunFiber.exit = _
    rw [inspect_keeps_machine]
    rfl
  rw [hexit]
  rcases hH with ⟨hm, -⟩ | hS
  · -- the loaded root is runnable: a run at rest has evaluated it
    have hrun := hrest.1
    rw [show s.work.runnable = Api.runnableFibers s.machine from rfl, hm] at hrun
    cases hrun
  · exact meaning_settled_tape s.built.program hfrag s.budget.compileFuel (appliedExits s) hS
      (List.isEmpty_iff.mp hrest.2) hL

/-- The proposition of `denoteRows_eq_session_host` (H9), on the fragment `frag`: for a recorded
run whose root exited, under any host that gave the run's answers, the run of the program's call
tree under the host is the root's exit with the stores, the host ending where the answers left
it. -/
def DenoteRowsEqSessionHost (frag : RowTable → NativeEff → Bool) : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    frag s.built.table s.built.program = true →
    ∀ {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ),
      HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel) st st' →
      ∀ ex, s.exit = some ex →
        hostRun host s.built.program [] Stores.empty st = some (ex, (s.machine.state, st'))

/-- **H9: the host as a handler.** For a recorded run of a program of the fragment that is
funded, at rest, driven by a host, and whose root exited: under any host whose answers are the
run's (`HostAnswered`), the run of the program's call tree under that host is the root's exit
with the stores, and the host ends at the state the run's answers left it in. The reply host is
one host: H8. Reach: `StraightRows`, one fiber, every compile budget, finished runs. It does not
establish that a host's drive finishes (progress), nor anything of a run that stopped at a call,
an interruption, a clock step or a handle row. Concept `translation-simulation`, role
simulation; requirement R6. Consumer: host utilities composed with `Effects.Comodel`'s
constructions (`docs/research/2026-10-09-host-coalgebra.md`, slice CO-5). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteRows_eq_session_host : DenoteRowsEqSessionHost StraightRows := by
  intro s hreach hfund hrest hhost hfrag σ host st st' hA ex hex
  have hroot := LoopedRows.of_straightRows s.built.program hfrag
  have hmach := funded_replays s hreach hfund
  have hans : Answered s.built.program s.built.table s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) := by
    have read : (tapeFrom (openedOf s) s.journal).2 = [] := List.isEmpty_iff.mp hfund
    have h := tapeFrom_answered (openedOf s) s.journal read
    rw [show (openedOf s).machine = Api.load s.built.program s.budget.compileFuel from
      Run.open_machine s.built s.id s.budget s.profile] at h
    exact h
  obtain ⟨p, hH, hL⟩ := tape_holds_host s.built.program s.built.table s.budget.fuel hroot
    s.budget.compileFuel host (tapeOf s) _ _ st st' (Or.inl ⟨rfl, rfl⟩) hans hhost hA
  rw [← hmach] at hH
  simp only [atRest, Bool.and_eq_true] at hrest
  have hexit : s.exit = (s.machine.fiber? Api.root).bind RunFiber.exit := by
    show ((Api.HostSession.inspect s.session).machine.fiber? Api.root).bind RunFiber.exit = _
    rw [inspect_keeps_machine]
    rfl
  rcases hH with ⟨hm, -⟩ | hS
  · -- the loaded root is runnable: a run at rest has evaluated it
    have hrun := hrest.1
    rw [show s.work.runnable = Api.runnableFibers s.machine from rfl, hm] at hrun
    cases hrun
  · -- an exited root is the exit form, where the host is asked nothing
    have hstop : p.hostAnswer host st' = none := by
      rcases hS with ⟨cur, K, i, s', k, tr, t, hm, -, -⟩ | ⟨cur, K, i, s', k, tr, t, hm, -, -⟩ |
        ⟨ex', fr, s', k, tr, nt, hm, rfl, -⟩
      · rw [hexit, hm, Myield_fiber?] at hex
        cases hex
      · rw [hexit, hm, Mcall_fiber?] at hex
        cases hex
      · rfl
    rw [meaning_settled host s.built.program hfrag s.budget.compileFuel st st' hS
      (List.isEmpty_iff.mp hrest.2) hL hstop, ← hexit, hex]
    rfl

end Effect4.Run
