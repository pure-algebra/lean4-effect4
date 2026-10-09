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
* the session applies a reply only at a guard the machine waits on (`tapeFrom_answered`, here),
  so a recorded run's tape is a tape of such decisions.
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

/-- Step of `denoteRows_eq_session`: a reply that passes the session's preflight is at a guard
the machine waits on. -/
theorem preflight_requested {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) (decision : NativeDecision)
    (h : Api.HostSession.preflight s reply = .ok decision) :
    Program.requestOf s.machine reply.key.fiber reply.key.token ≠ none := by
  unfold Api.HostSession.preflight at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i bound hbound
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i hreq
            have hb := List.find?_some hbound
            have same : bound.key = reply.key := beq_iff_eq.mp hb
            rw [← same]
            exact hreq

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
waits on. A reply application passed the preflight; a control never answers (`advance` refuses a
direct answer); a receipt row gives no decision. -/
theorem decisionOf_answer_requested (s : Run) (c : Command) {f : FiberId} {t : Nat}
    {a : Completion Val Err Defect FiberId Ann}
    (hdec : decisionOf s c (Api.Runner.result s.runner c).phase = some (.answerAsync f t a)) :
    Program.requestOf s.machine f t ≠ none := by
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
      exact preflight_requested s.session reply d hpre
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
a guard the machine waits on. -/
def Answered (program : Api.Program) (table : RowTable) (fuel : Nat) :
    List Api.Decision → Api.Machine → Prop
  | [], _ => True
  | d :: T, m => m.stuck = none ∧ Run.enoughFor program table fuel m d = true ∧
      (∀ f t a, d = .answerAsync f t a → Program.requestOf m f t ≠ none) ∧
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
          exact decisionOf_answer_requested s c hdec

/-! ## The tape of a host's decisions, through the machine -/

/-- **A tape of a host's answered decisions keeps the machine's forms** (a step of
`denoteRows_eq_session`): from a machine in a form of `Holds` at a position, the raw replay of
the tape ends in such a form, and the local run with calls leads from the first position to the
last, reading the tape's replies (`exitsOf`) in order. -/
theorem tape_holds (program : Api.Program) (table : RowTable) (fuel : Nat)
    (hroot : LoopedRows program = true) (cf : Nat) :
    ∀ (T : List Api.Decision) (m : Api.Machine) (p : Pos), Holds program cf m p →
      Answered program table fuel T m → T.all hostDecision = true →
      ∃ p', Holds program cf (Run.machineOf (Run.replayFrom program table fuel T m)) p' ∧
        ∀ r, Leads table program p (exitsOf T ++ r) p' r
  | [], m, p, hH, _, _ => ⟨p, by rw [Run.machineOf_nil]; exact hH, fun r => Leads.refl p r⟩
  | d :: T, m, p, hH, ⟨hs, hen, hreq, hrest⟩, hall => by
    rw [List.all_cons, Bool.and_eq_true] at hall
    rw [Run.replayFrom_cons program table fuel d T m hs hen]
    obtain ⟨p₁, hH₁, hL₁⟩ : ∃ p₁, Holds program cf (steppedBy program fuel table m d) p₁ ∧
        ∀ r, Leads table program p (exitsOf [d] ++ r) p₁ r := by
      have hd := hall.1
      cases d with
      | answerAsync f t a =>
        cases a with
        | ofExit ex => exact holds_answer program hroot cf hH (hreq f t _ rfl) hen
        | ofRefGet _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
            reduceCtorEq, or_self] at hd
      | evaluate id =>
        simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
          RunDecision.evaluate.injEq, reduceCtorEq, or_false] at hd
        subst hd
        exact holds_evaluate program hroot cf hH hen
      | flush => exact holds_flush program hroot cf hH hen
      | _ => simp only [hostDecision, Api.evaluate, Api.flush, Bool.or_eq_true, beq_iff_eq,
          reduceCtorEq, or_self] at hd
    obtain ⟨p', hH', hL'⟩ := tape_holds program table fuel hroot cf T _ p₁ hH₁ hrest hall.2
    refine ⟨p', hH', fun r => ?_⟩
    have happ : exitsOf (d :: T) ++ r = exitsOf [d] ++ (exitsOf T ++ r) := by
      cases d with
      | answerAsync f t a => cases a <;> rfl
      | _ => rfl
    rw [happ]
    exact (hL₁ _).trans (hL' r)

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
  have hL₀ := hL []
  rw [List.append_nil] at hL₀
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
  · exact meaning_settled s.built.program hfrag s.budget.compileFuel (appliedExits s) hS
      (List.isEmpty_iff.mp hrest.2) hL₀

end Effect4.Run
