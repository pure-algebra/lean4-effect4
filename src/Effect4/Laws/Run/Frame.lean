import Effect4.Laws.Run.Tape
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Semantics

/-!
# Invariants of recorded runs

`Keeps` lifts an invariant through rows admitted by an explicit predicate.
`HistoryOf` records the machine decisions that session admission permits.
Both views use the existing run and machine, without another execution carrier.

Placement: host-session-protocol, R13, claim proposed as `run-history` in the goals plan.
Consumers: the session key ledger and the thirteen scenario goals over scripts.
Reach: arbitrary rows, budgets and built programs, including cuts and refused rows.
The funded specialization reads only rows whose tape has no remaining suffix.
These laws transfer supplied invariants. They establish no progress or host behavior.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)
open Effect4.Api.HostSession (Phase)

/-- Every permitted row keeps the supplied invariant. -/
def Keeps (allow : Run → Command → Prop) (I : Run → Prop) : Prop :=
  ∀ s c, allow s c → I s → I (s.step c)

/-- Permission follows the intermediate run at each row. -/
def Allowed (allow : Run → Command → Prop) : Run → List Command → Prop
  | _, [] => True
  | s, c :: cs => allow s c ∧ Allowed allow (s.step c) cs

/-- Row preservation lifts through precisely the permitted rows. -/
theorem Keeps.play {allow : Run → Command → Prop} {I : Run → Prop}
    (keeps : Keeps allow I) :
    ∀ rows s, Allowed allow s rows → I s → I (s.play rows)
  | [], _, _, hi => hi
  | c :: cs, s, ha, hi =>
    Keeps.play keeps cs (s.step c) ha.2 (keeps s c ha.1 hi)

/-- Universal row preservation lifts to every recorded run. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem Keeps.reached {I : Run → Prop} (keeps : Keeps (fun _ _ => True) I)
    (opened : ∀ b id budget profile, I (Run.open b id budget profile))
    (s : Run) (h : Reached s) : I s := by
  induction h with
  | opened b id budget profile => exact opened b id budget profile
  | step s c _ ih => exact keeps s c trivial ih

/-- Every row is allowed by the universal predicate. -/
theorem allowed_all : ∀ s rows, Allowed (fun _ _ => True) s rows
  | _, [] => trivial
  | s, c :: cs => ⟨trivial, allowed_all (s.step c) cs⟩

/-- Whether the tape reads one row at a run: the row ends at no frontier, and its decision, if
any, is taken at a live machine with enough command fuel. It is `tapeFrom`'s own test
(`src/Effect4/Run/Tape.lean`). -/
def rowReads (s : Run) (c : Command) : Bool :=
  !((Api.Runner.result s.runner c).phase == Phase.frontier) &&
    (Run.decisionOf s c (Api.Runner.result s.runner c).phase).all (Run.readsOn s)

/-- A tape that reads every row reads the first one, and the rest from the run after it. -/
theorem tapeFrom_read_cons (s : Run) (c : Command) (rest : List Command)
    (h : (Run.tapeFrom s (c :: rest)).2 = []) :
    rowReads s c = true ∧ (Run.tapeFrom (s.step c) rest).2 = [] := by
  cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
  | true =>
    rw [Run.tapeFrom_frontier s c rest hfront] at h
    exact absurd h (List.cons_ne_nil c rest)
  | false =>
    cases hdec : Run.decisionOf s c (Api.Runner.result s.runner c).phase with
    | none =>
      rw [Run.tapeFrom_skip s c rest hfront hdec] at h
      refine ⟨?_, h⟩
      unfold rowReads
      rw [hfront, hdec]
      rfl
    | some d =>
      cases hreads : Run.readsOn s d with
      | false =>
        rw [Run.tapeFrom_stop s c rest d hfront hdec hreads] at h
        exact absurd h (List.cons_ne_nil c rest)
      | true =>
        rw [Run.tapeFrom_take s c rest d hfront hdec hreads] at h
        refine ⟨?_, h⟩
        unfold rowReads
        rw [hfront, hdec]
        exact hreads

/-- A funded row list satisfies its row permission at each intermediate run. -/
theorem allowed_of_reads {allow : Command → Prop} :
    ∀ rows s, (∀ c ∈ rows, allow c) → (tapeFrom s rows).2 = [] →
      Allowed (fun s c => allow c ∧ rowReads s c = true) s rows
  | [], _, _, _ => trivial
  | c :: cs, s, ha, hr => by
    obtain ⟨hc, hcs⟩ := tapeFrom_read_cons s c cs hr
    exact ⟨⟨ha c List.mem_cons_self, hc⟩,
      allowed_of_reads cs (s.step c) (fun d hd => ha d (List.mem_cons_of_mem c hd)) hcs⟩

/-- Preservation over read rows lifts through a funded list. -/
theorem Keeps.play_reads {allow : Command → Prop} {I : Run → Prop}
    (keeps : Keeps (fun s c => allow c ∧ rowReads s c = true) I)
    (rows : List Command) (s : Run) (ha : ∀ c ∈ rows, allow c)
    (hr : (tapeFrom s rows).2 = []) (hi : I s) : I (s.play rows) :=
  keeps.play rows s (allowed_of_reads rows s ha hr) hi

/-- **A decision the session hands its machine.** A control is never an answer: `advance`
refuses `answerAsync`. An answer reaches the machine only through `applyReply`, whose preflight
returned it from `acceptReply` or `acceptAtInstance` at that machine. -/
def Accepted (app : SigApp) (calls : List (List Nat × CallInstance NativeOp))
    (m : NativeMachine) (d : NativeDecision) : Prop :=
  match d with
  | .answerAsync _ _ _ => ∃ r, acceptReply app m r = some d ∨
      acceptAtInstance app (fun origin => calls.lookup origin) m r = some d
  | _ => True

/-- A decision that preflight returns is accepted at the session's machine. -/
theorem preflight_accepted {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (reply : Api.HostSession.Reply)
    (d : NativeDecision) (h : Api.HostSession.preflight s reply = .ok d) :
    Accepted app s.calls s.machine d := by
  have found : ∃ r, acceptReply app s.machine r = some d ∨
      acceptAtInstance app (fun origin => s.calls.lookup origin) s.machine r = some d := by
    unfold Api.HostSession.preflight at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · rename_i decision hacc
                cases h
                exact ⟨_, Or.inl hacc⟩
              · split at h
                · rename_i decision hacc
                  cases h
                  exact ⟨_, Or.inr hacc⟩
                · cases h
  unfold Accepted
  split
  · exact found
  · trivial

/-- The session's calls table is the one `Run.open` made: no transition writes it. -/
theorem result_calls (p : Api.Runner.Runner) (c : Command) :
    (Api.Runner.result p c).session.calls = p.session.calls := by
  cases c with
  | bind call token =>
    show (Api.HostSession.bindCall p.session call token).session.calls = _
    unfold Api.HostSession.bindCall
    dsimp only
    repeat' split
    all_goals rfl
  | submit reply =>
    show (Api.HostSession.submit p.session reply).session.calls = _
    unfold Api.HostSession.submit
    repeat' split
    all_goals rfl
  | apply key =>
    show (Api.HostSession.applyReply p.session key p.fuel).session.calls = _
    cases p.fuel with
    | zero => rfl
    | succ fuel =>
      unfold Api.HostSession.applyReply
      dsimp only
      repeat' split
      all_goals rfl
  | control decision =>
    show (Api.HostSession.advance p.session p.fuel decision).session.calls = _
    unfold Api.HostSession.advance
    repeat' split
    all_goals rfl

/-- `applyReply` leaves the machine, or steps it at an accepted decision. -/
theorem applyReply_machine {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (key : Api.HostSession.Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).session.machine = s.machine ∨
      ∃ x : Nat × NativeDecision, Accepted app s.calls s.machine x.2 ∧
        (Api.HostSession.applyReply s key fuel).session.machine =
          steppedBy program x.1 app.rows s.machine x.2 := by
  unfold Api.HostSession.applyReply
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · rename_i decision hpre
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · exact Or.inr ⟨(_, decision), preflight_accepted s _ decision hpre, rfl⟩
          · exact Or.inr ⟨(_, decision), preflight_accepted s _ decision hpre, rfl⟩
    · exact Or.inl rfl

/-- A decision that is not an answer is accepted: `Accepted` asks nothing of a control. -/
theorem accepted_of_control (app : SigApp) (calls : List (List Nat × CallInstance NativeOp))
    (m : NativeMachine) (d : NativeDecision) (h : ∀ f t a, d ≠ .answerAsync f t a) :
    Accepted app calls m d := by
  cases d with
  | answerAsync f t a => exact absurd rfl (h f t a)
  | fire _ => trivial
  | flush => trivial
  | evaluate _ => trivial
  | yieldVerdict _ _ => trivial
  | interruptFrom _ _ _ => trivial
  | installMiddleware => trivial
  | advance _ => trivial

/-- `advance` leaves the machine, or steps it at a control. -/
theorem advance_machine {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (fuel : Nat) (d : NativeDecision) :
    (Api.HostSession.advance s fuel d).session.machine = s.machine ∨
      (Accepted app s.calls s.machine d ∧
        (Api.HostSession.advance s fuel d).session.machine = steppedBy program fuel app.rows s.machine d) := by
  unfold Api.HostSession.advance
  split
  · exact Or.inl rfl
  · rename_i notAnswer
    have accepted := accepted_of_control app s.calls s.machine d
      (fun f t a heq => notAnswer f t a heq)
    split
    · exact Or.inl rfl
    · split
      · rename_i machine enough hstep
        split
        · exact Or.inl rfl
        · refine Or.inr ⟨accepted, ?_⟩
          show machine = steppedBy program fuel app.rows s.machine d
          unfold steppedBy
          rw [hstep]

/-- **One row moves a run's machine by at most one accepted decision.** -/
theorem step_machine (s : Run) (c : Command) :
    (s.step c).machine = s.machine ∨
      ∃ x : Nat × NativeDecision, Accepted s.built.app s.session.calls s.machine x.2 ∧
        (s.step c).machine = steppedBy s.built.program x.1 s.built.table s.machine x.2 := by
  cases c with
  | bind call token =>
    exact Or.inl ((congrArg Api.HostSession.Session.machine (Run.step_session_bind s call token)).trans
      (Run.bindCall_inert s.session call token).1)
  | submit reply =>
    exact Or.inl ((congrArg Api.HostSession.Session.machine (Run.step_session_submit s reply)).trans
      (Run.submit_inert s.session reply).1)
  | apply key =>
    have hs := congrArg Api.HostSession.Session.machine (Run.step_session_apply s key)
    rcases applyReply_machine s.session key s.budget.fuel with same | ⟨x, hx, moved⟩
    · exact Or.inl (hs.trans same)
    · exact Or.inr ⟨x, hx, hs.trans moved⟩
  | control d =>
    have hs := congrArg Api.HostSession.Session.machine (Run.step_session_control s d)
    rcases advance_machine s.session s.budget.fuel d with same | ⟨hx, moved⟩
    · exact Or.inl (hs.trans same)
    · exact Or.inr ⟨(s.budget.fuel, d), hx, hs.trans moved⟩

/-- One step of a history: the session's machine step at a decision and its fuel. -/
def stepBy (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision) : NativeMachine :=
  steppedBy b.program x.1 b.table m x.2

/-- **The machine of a run**: its program's load, stepped by a history of decisions, each
accepted by the session at the machine it met. -/
def HistoryOf (b : Api.Built) (compileFuel : Nat) (m : NativeMachine) : Prop :=
  ∃ history : List (Nat × NativeDecision),
    Lift.Admitted (W := Unit) (fun _ _ => True)
      (fun _ m x => Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2)
      (stepBy b) (Api.load b.program compileFuel) history ∧
    m = history.foldl (stepBy b) (Api.load b.program compileFuel)

/-- An admitted history extended by one step admitted at its end. -/
theorem admitted_snoc {W M X : Type} (J : W → M → Prop) (A : W → M → X → Prop)
    (step : M → X → M) :
    ∀ (xs : List X) (m : M) (x : X), Lift.Admitted J A step m xs →
      (∀ w, J w (xs.foldl step m) → A w (xs.foldl step m) x) →
        Lift.Admitted J A step m (xs ++ [x])
  | [], _, _, _, hx => ⟨hx, trivial⟩
  | _ :: ys, _, x, ⟨hy, hys⟩, hx => ⟨hy, admitted_snoc J A step ys _ x hys hx⟩

/-- **Every reached run's machine is a history of its program.** Reach: every built program,
name, budget and profile, every row. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem reached_history (s : Run) (h : Run.Reached s) :
    s.session.calls = Api.HostSession.callTable s.built.program s.built.app ∧
      HistoryOf s.built s.budget.compileFuel s.machine := by
  induction h with
  | opened b id budget profile => exact ⟨rfl, [], trivial, rfl⟩
  | step s c _ ih =>
    obtain ⟨hcalls, history, adm, hm⟩ := ih
    have calls' : (s.step c).session.calls = s.session.calls := by
      show (Api.Runner.result s.runner c).session.calls = s.runner.session.calls
      exact result_calls s.runner c
    refine ⟨calls'.trans hcalls, ?_⟩
    show HistoryOf s.built s.budget.compileFuel (s.step c).machine
    rcases step_machine s c with same | ⟨x, hx, moved⟩
    · exact ⟨history, adm, same.trans hm⟩
    · refine ⟨history ++ [x], ?_, ?_⟩
      · refine admitted_snoc _ _ (stepBy s.built) history _ x adm fun _ _ => ?_
        rw [← hm, ← hcalls]
        exact hx
      · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hm]
        exact moved

/-- **The lift**: a machine fact true at the load and kept by every accepted step holds of every
history, by `Lift.foldl_lift` at the one-world order. -/
theorem history_keeps (b : Api.Built) (compileFuel : Nat) (J : NativeMachine → Prop)
    (load : J (Api.load b.program compileFuel))
    (step : ∀ m x, J m →
      Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2 → J (stepBy b m x)) :
    ∀ m, HistoryOf b compileFuel m → J m := by
  rintro m ⟨history, adm, rfl⟩
  have weaken : ∀ (xs : List (Nat × NativeDecision)) (m₀ : NativeMachine),
      Lift.Admitted (W := Unit) (fun _ _ => True)
        (fun _ m x => Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2)
        (stepBy b) m₀ xs →
      Lift.Admitted (W := Unit) (fun _ m => J m)
        (fun _ m x => Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2)
        (stepBy b) m₀ xs := by
    intro xs
    induction xs with
    | nil => intro _ _; trivial
    | cons x xs ih =>
      intro m₀ h
      exact ⟨fun w _ => h.1 w trivial, ih _ h.2⟩
  obtain ⟨_, _, hj⟩ := Lift.foldl_lift Lift.unitOrder (fun _ m => J m)
    (fun _ m x => Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2)
    (stepBy b) (fun _ m x hj ha => ⟨(), trivial, step m x hj ha⟩) history () _ load
    (weaken history _ adm)
  exact hj

/-- A decision that is no host answer. -/
def IsControl : NativeDecision → Prop
  | .answerAsync _ _ _ => False
  | _ => True

/-- **A control history**: the load stepped by controls only. -/
def ControlHistory (b : Api.Built) (compileFuel : Nat) (m : NativeMachine) : Prop :=
  ∃ history : List (Nat × NativeDecision), (∀ x ∈ history, IsControl x.2) ∧
    m = history.foldl (stepBy b) (Api.load b.program compileFuel)

/-- The empty table has no external row. -/
theorem externalRow_nil (i : Nat) : externalRow [] i = none := rfl

/-- With the empty row table `admit` refuses every answer. -/
theorem admit_nil_answer {app : SigApp} (hrows : app.rows = []) (m : NativeMachine) (f : FiberId)
    (t : Nat) (a : Completion Val Err Defect FiberId Ann) :
    Program.admit app m (.answerAsync f t a) ≠ none := by
  unfold Program.admit
  dsimp only
  split
  · exact Option.some_ne_none _
  · split
    · exact Option.some_ne_none _
    · split
      · exact Option.some_ne_none _
      · split
        · rw [hrows, externalRow_nil]
          exact Option.some_ne_none _
        · exact Option.some_ne_none _

/-- **With the empty row table every accepted decision is a control.** -/
theorem accepted_nil_control {app : SigApp} (hrows : app.rows = [])
    {calls : List (List Nat × CallInstance NativeOp)} {m : NativeMachine}
    {d : NativeDecision} (h : Accepted app calls m d) : IsControl d := by
  cases d with
  | answerAsync f t a =>
    obtain ⟨r, hr | hr⟩ := h
    · have henv := acceptReply_envelope app m r _ hr
      have hd := acceptReply_decision app m r _ hr
      cases hd
      exact absurd henv.2.2 (admit_nil_answer hrows m _ _ _)
    · unfold acceptAtInstance at hr
      split at hr
      · split at hr
        · rename_i i origin _ _
          rw [hrows, externalRow_nil] at hr
          cases hr
        · cases hr
      · cases hr
  | fire _ => trivial
  | flush => trivial
  | evaluate _ => trivial
  | yieldVerdict _ _ => trivial
  | interruptFrom _ _ _ => trivial
  | installMiddleware => trivial
  | advance _ => trivial

/-- **A program with no host row has control histories only.** -/
theorem history_control {b : Api.Built} {compileFuel : Nat} {m : NativeMachine}
    (htable : b.table = []) (h : HistoryOf b compileFuel m) : ControlHistory b compileFuel m := by
  obtain ⟨history, adm, rfl⟩ := h
  refine ⟨history, ?_, rfl⟩
  have go : ∀ (xs : List (Nat × NativeDecision)) (m₀ : NativeMachine),
      Lift.Admitted (W := Unit) (fun _ _ => True)
        (fun _ m x => Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2)
        (stepBy b) m₀ xs → ∀ x ∈ xs, IsControl x.2 := by
    intro xs
    induction xs with
    | nil => intro _ _ x hx; exact absurd hx List.not_mem_nil
    | cons y ys ih =>
      intro m₀ hadm x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact accepted_nil_control htable (hadm.1 () trivial)
      · exact ih _ hadm.2 x hx
  exact go history _ adm


/-- Accepted answers name a parked host call, including admission at a call instance. -/
theorem Accepted.host_request {app : SigApp}
    {calls : List (List Nat × CallInstance NativeOp)} {m : NativeMachine}
    {fiber : FiberId} {token : Nat} {answer : Completion Val Err Defect FiberId Ann}
    (h : Accepted app calls m (.answerAsync fiber token answer)) :
    (requestOf m fiber token).isSome = true := by
  obtain ⟨r, hr | hr⟩ := h
  · have hd := acceptReply_decision app m r _ hr
    have he := acceptReply_envelope app m r _ hr
    cases hd
    rw [he.2.1]
    rfl
  · obtain ⟨he, hd⟩ := acceptAtInstance_sound app (fun origin => calls.lookup origin) m r _ hr
    cases hd
    rw [he.2.1]
    rfl

/-- Admitted machine histories are raw reachable histories with their stronger admission retained. -/
theorem HistoryOf.reachable {b : Api.Built} {cf : Nat} {m : NativeMachine}
    (h : HistoryOf b cf m) : Guard.Reachable b.program b.table cf m :=
  history_keeps b cf (Guard.Reachable b.program b.table cf)
    (Guard.reachable_load b.program b.table cf)
    (fun _ x hm _ => Guard.reachable_step hm x.1 x.2) m h

/-- Playing rows appends those rows to the journal. -/
theorem journal_play : ∀ (s : Run) (rows : List Command), (s.play rows).journal = s.journal ++ rows
  | s, [] => by rw [Run.play_nil, List.append_nil]
  | s, c :: rest => by
    rw [Run.play_cons, journal_play (s.step c) rest, Run.step_journal, List.append_assoc]
    rfl

end Effect4.Run
