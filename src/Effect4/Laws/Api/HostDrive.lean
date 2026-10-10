import Effect4.Laws.Program.RowProtocol

/-!
# Api.HostDrive — the driver's run is answered by its reactor

`Run.runWith` opens a program, evaluates its root and then drives it with a reactor
(`Run.driveFrom`, `src/Effect4/Run/Basic.lean`): it answers each fresh call with the reactor's
completion and flushes between rounds. Read the reactor as a host (`reactorHost`). When the
reactor stays inside the envelope (`Reactor.Envelops`) and answers with exits only, every answer
the drive plays is one the host gives, at the machine's own request. So a funded run of the
driver meets H9's premises (`runWith_hostAnswered`), and H9 gives its meaning
(`runWith_denotes`): the reactor's run of the program's call tree is the root's exit with the
stores, and the reactor ends where the drive left it.

The envelope quantifies over machines. A reactor behind its rows' types (`Reactor.guardRows`)
meets it at every table (`guardRows_envelops`): it answers only exits that a row's columns
admit at every machine. So H9 holds at the driver for any reactor so guarded
(`runWith_guarded_denotes`).

Any host of the row signature drives a run too. A reactor finds its row by key and asks the host
at that row's position (`Reactor.ofHost`), since a table's keys are distinct. Read back behind
the rows' types, it is the host behind them (`reactorHost_ofHost`). So every construction of
`Effects.Comodel` drives a run under H9 (`runWith_host_denotes`).

Placement: concept `translation-simulation`, role simulation; claim `rows-denotation-driver`;
requirement R6, the part "the host as a relation between the machine's calls and its answers".
Reach: H9's reach (`StraightRows`, one fiber, finished runs), a reactor inside the envelope that
answers with exits, and a funded run at rest. It does not establish that a drive finishes or
that its rounds suffice (progress), that a run is funded (the open claim
`embedded-budget-sufficient`), or anything of a reactor outside the envelope, whose refused
answers move its state with no decision on the tape. Consumer: the run interface's hosts
composed by `Effects.Comodel` (`docs/research/2026-10-09-host-coalgebra.md`, slice CO-6).
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Api.HostSession (Key Call Reply Answer Phase BoundCall Session ReplySlot)
open Effect4.Api.Runner (Command)

/-- A reactor that answers each call with an exit, never with a read of a cell. -/
def Reactor.ExitsOnly {σ : Type} (r : Reactor σ) : Prop :=
  ∀ (row : Program.Row) (request : Val) (st : σ) (c : Answer) (next : σ),
    r row request st = some (c, next) → ∃ ex, c = .ofExit ex

/-- The machine that the raw stepper leaves on a tape of decisions. -/
def stepsBy (program : Api.Program) (fuel : Nat) (table : RowTable) (m : Api.Machine)
    (tape : List Api.Decision) : Api.Machine :=
  tape.foldl (steppedBy program fuel table) m

/-! ## Two tapes in a row -/

/-- Step of `drive_hostAnswered`: a host that answers two tapes in a row answers the two as one
tape. -/
theorem hostAnswered_append (table : RowTable) {σ : Type}
    (host : Effects.Comodel (RowSig table) σ) (program : Api.Program) (fuel : Nat) :
    ∀ (T₁ T₂ : List Api.Decision) (m : Api.Machine) (st st' st'' : σ),
      HostAnswered table host program fuel T₁ m st st' →
      HostAnswered table host program fuel T₂ (stepsBy program fuel table m T₁) st' st'' →
      HostAnswered table host program fuel (T₁ ++ T₂) m st st''
  | [], _, _, _, _, _, h₁, h₂ => by
    subst h₁
    exact h₂
  | .answerAsync f t (.ofExit ex) :: T, T₂, m, st, st', st'', h₁, h₂ => by
    obtain ⟨i, v, hi, s₁, hrq, hans, hA⟩ := h₁
    exact ⟨i, v, hi, s₁, hrq, hans, hostAnswered_append table host program fuel T T₂ _ s₁ st' st''
      hA h₂⟩
  | .answerAsync _ _ (.ofRefGet _) :: T, T₂, _, st, st', st'', h₁, h₂ =>
    hostAnswered_append table host program fuel T T₂ _ st st' st'' h₁ h₂
  | .fire _ :: T, T₂, _, st, st', st'', h₁, h₂ | .flush :: T, T₂, _, st, st', st'', h₁, h₂
  | .evaluate _ :: T, T₂, _, st, st', st'', h₁, h₂
  | .yieldVerdict _ _ :: T, T₂, _, st, st', st'', h₁, h₂
  | .interruptFrom _ _ _ :: T, T₂, _, st, st', st'', h₁, h₂
  | .installMiddleware :: T, T₂, _, st, st', st'', h₁, h₂
  | .advance _ :: T, T₂, _, st, st', st'', h₁, h₂ =>
    hostAnswered_append table host program fuel T T₂ _ st st' st'' h₁ h₂

/-- Step of `drive_hostAnswered`: a tape with no answer decision asks the host nothing. -/
theorem hostAnswered_quiet (table : RowTable) {σ : Type}
    (host : Effects.Comodel (RowSig table) σ) (program : Api.Program) (fuel : Nat) (st : σ) :
    ∀ (T : List Api.Decision) (m : Api.Machine),
      (∀ d ∈ T, d = Api.flush ∨ d = Api.evaluate) →
      HostAnswered table host program fuel T m st st
  | [], _, _ => rfl
  | d :: T, m, h => by
    rcases h d List.mem_cons_self with rfl | rfl
    · exact hostAnswered_quiet table host program fuel st T _
        fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    · exact hostAnswered_quiet table host program fuel st T _
        fun d' hd' => h d' (List.mem_cons_of_mem _ hd')

/-! ## The machine after rows is the raw stepper's on their tape -/

/-- Step of `drive_hostAnswered`: when the tape reads every row, the machine that the rows leave
is the raw stepper's on the tape's decisions. It is `tape_replays` with the stepper in place of
the replay, which stops where the stepper does not. -/
theorem play_machine_stepsBy (s : Run) (rows : List Command) (h : (tapeFrom s rows).2 = []) :
    (s.play rows).machine =
      stepsBy s.built.program s.budget.fuel s.built.table s.machine
        ((tapeFrom s rows).1.map (·.decision)) := by
  induction rows generalizing s with
  | nil => rfl
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
          rw [ih (s.step c) h, Run.step_built, Run.step_budget,
            step_takes_decision s c decision hdec]
          rfl

/-- Step of `drive_hostAnswered`: the tape of rows played in two parts, when the whole tape reads
every row. -/
theorem tapeFrom_append_read (s : Run) (a b : List Command) (h : (tapeFrom s (a ++ b)).2 = []) :
    (tapeFrom s a).2 = [] ∧ (tapeFrom (s.play a) b).2 = [] ∧
      (tapeFrom s (a ++ b)).1 = (tapeFrom s a).1 ++ (tapeFrom (s.play a) b).1 := by
  rw [tapeFrom_append] at h ⊢
  by_cases ha : (tapeFrom s a).2 = []
  · rw [if_pos ha] at h ⊢
    exact ⟨ha, h, rfl⟩
  · rw [if_neg ha] at h
    exact absurd (List.append_eq_nil_iff.mp h).1 ha

/-! ## The tape of a control row and of an answer -/

/-- Step of `drive_hostAnswered`: a control row gives its own decision or none. -/
theorem tapeFrom_control (s : Run) (d : Api.Decision) :
    ∀ x ∈ (tapeFrom s [.control d]).1.map (·.decision), x = d := by
  intro x hx
  cases hfront : ((Api.Runner.result s.runner (.control d)).phase == Phase.frontier) with
  | true =>
    rw [tapeFrom_frontier s _ [] hfront] at hx
    cases hx
  | false =>
    cases hdec : decisionOf s (.control d) (Api.Runner.result s.runner (.control d)).phase with
    | none =>
      rw [tapeFrom_skip s _ [] hfront hdec] at hx
      cases hx
    | some decision =>
      cases hreads : readsOn s decision with
      | false =>
        rw [tapeFrom_stop s _ [] decision hfront hdec hreads] at hx
        cases hx
      | true =>
        rw [tapeFrom_take s _ [] decision hfront hdec hreads] at hx
        rcases List.mem_cons.mp hx with rfl | hrest
        · generalize (Api.Runner.result s.runner (.control d)).phase = phase at hdec
          cases phase <;> cases hdec
          rfl
        · cases hrest

/-- Step of `drive_hostAnswered`: an answer that the session accepts, read on the tape. A call
the machine is holding at a key the session has no record of, answered with a completion the
machine admits: when the tape reads its three rows, it holds one decision, the answer. The
session facts are `answer_accepted`'s. -/
theorem answer_tape (s : Run) (key : Key) (c : Answer) (call : Call)
    (hat : Api.HostSession.Call.at s key = some call)
    (hfresh : s.session.active.any (fun b => b.key == key) = false)
    (hslot : s.session.pending.any (fun slot => slot.key == key) = false)
    (hfits : admit s.built.table s.machine (.answerAsync key.fiber key.token c) = none)
    (hread : (tapeFrom s (Rows.answer s key c)).2 = []) :
    (tapeFrom s (Rows.answer s key c)).1.map (·.decision) = [.answerAsync key.fiber key.token c] := by
  obtain ⟨op, request, hr, hshape⟩ := at_eq s key call hat
  have hfib : call.fiber = key.fiber := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hop : call.op = op := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hreq : call.request = request := by
    simp only [hshape, Api.HostSession.Call.claim]
  have htab : call.table = s.built.table := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hbkey : (⟨call, key.token⟩ : BoundCall).key = key := by
    show (⟨call.fiber, key.token⟩ : Key) = key
    rw [hfib]
  have hobs : Api.HostProtocol.observe s.session.machine = .awaitingAsync :=
    observe_awaitingAsync s.session.machine key.fiber key.token op request hr
  -- the run after the bind row
  have hb := bindCall_at_bound s key call hat hfresh
  have ha1 : (s.step (.bind call key.token)).session.active =
      s.session.active ++ [(⟨call, key.token⟩ : BoundCall)] := by
    rw [step_session_bind, hb]
  have hp1 : (s.step (.bind call key.token)).session.pending =
      s.session.pending ++ [(⟨key, none⟩ : ReplySlot)] := by
    rw [step_session_bind, hb]
  have hm1 : (s.step (.bind call key.token)).session.machine = s.session.machine := by
    rw [step_session_bind, hb]
  have hh1 : (s.step (.bind call key.token)).session.header = s.session.header := by
    rw [step_session_bind, hb]
  -- the receipt is accepted
  have hfind : (s.step (.bind call key.token)).session.active.find?
      (fun b => b.key == (Rows.reply s call key c).key) = some ⟨call, key.token⟩ := by
    rw [ha1]
    exact find_append_fresh s.session.active ⟨call, key.token⟩ key hbkey hfresh
  have hslot1 : Api.HostSession.readReply (s.step (.bind call key.token)).session.pending
      (Rows.reply s call key c).key = none := by
    rw [hp1]
    exact readReply_append_fresh s.session.pending key hslot
  have hany1 : (s.step (.bind call key.token)).session.pending.any
      (fun slot => slot.key == (Rows.reply s call key c).key) = true := by
    rw [hp1]
    exact any_append_key s.session.pending key
  have henv : Envelope s.built.table (s.step (.bind call key.token)).session.machine
      ((⟨call, key.token⟩ : BoundCall).record (Rows.reply s call key c)) := by
    rw [hm1]
    refine ⟨htab, ?_, ?_⟩
    · show requestOf s.session.machine call.fiber key.token = some (call.op, call.request)
      rw [hfib, hop, hreq]
      exact hr
    · show admit s.built.table s.session.machine (.answerAsync call.fiber key.token c) = none
      rw [hfib]
      exact hfits
  have hobs1 : Api.HostProtocol.observe (s.step (.bind call key.token)).session.machine =
      .awaitingAsync := by
    rw [hm1]
    exact hobs
  have hsub := submit_accepted (s.step (.bind call key.token)).session (Rows.reply s call key c)
    ⟨call, key.token⟩ rfl (by rw [hh1]; rfl) hfind rfl hslot1 hany1 henv hobs1
  have hpre := preflight_ok (s.step (.bind call key.token)).session (Rows.reply s call key c)
    ⟨call, key.token⟩ rfl (by rw [hh1]; rfl) hfind rfl henv
  -- the run after the receipt row
  have ha2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.active
      = (s.step (.bind call key.token)).session.active := by
    rw [step_session_submit, hsub]
  have hp2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.pending
      = Api.HostSession.storeReply (s.step (.bind call key.token)).session.pending
        (Rows.reply s call key c) := by
    rw [step_session_submit, hsub]
  have hm2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.machine
      = (s.step (.bind call key.token)).session.machine := by
    rw [step_session_submit, hsub]
  have hfind2 : ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.active.find? (fun b => b.key == key)
      = some ⟨call, key.token⟩ := by
    rw [ha2]
    exact hfind
  have hread2 : Api.HostSession.readReply ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.pending key
      = some (Rows.reply s call key c) := by
    rw [hp2]
    exact Api.HostSession.readReply_store_self (s.step (.bind call key.token)).session.pending
      (Rows.reply s call key c) hany1
  have hpre2 : Api.HostSession.preflight ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session (Rows.reply s call key c)
      = .ok (.answerAsync call.fiber key.token c) := by
    rw [step_session_submit, hsub]
    exact hpre
  have hobs2 : Api.HostProtocol.observe ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.machine = .awaitingAsync := by
    rw [hm2]
    exact hobs1
  have happly := applyReply_accepted ((s.step (.bind call key.token)).step
    (.submit (Rows.reply s call key c))).session key s.budget.fuel ⟨call, key.token⟩
    (Rows.reply s call key c) (.answerAsync call.fiber key.token c) hfind2 hread2 hpre2 hobs2
  -- the tape of the three rows
  have hfront1 : ((Api.Runner.result s.runner (.bind call key.token)).phase == Phase.frontier)
      = false := by
    show ((Api.HostSession.bindCall s.session call key.token).phase == Phase.frontier) = false
    rw [hb]
    rfl
  have hfront2 : ((Api.Runner.result (s.step (.bind call key.token)).runner
      (.submit (Rows.reply s call key c))).phase == Phase.frontier) = false := by
    show ((Api.HostSession.submit (s.step (.bind call key.token)).session
      (Rows.reply s call key c)).phase == Phase.frontier) = false
    rw [hsub]
    rfl
  rw [answer_rows_three s key c call hat] at hread ⊢
  rw [tapeFrom_skip s _ _ hfront1 rfl, tapeFrom_skip _ _ _ hfront2 rfl] at hread ⊢
  rcases happly with happlied | hfrontier
  · have hfront3 : ((Api.Runner.result ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))).runner (.apply key)).phase == Phase.frontier)
        = false := by
      show ((Api.HostSession.applyReply ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))).session key s.budget.fuel).phase == Phase.frontier)
        = false
      rw [happlied]
      rfl
    have hdec3 : decisionOf ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))) (.apply key)
        (Api.Runner.result ((s.step (.bind call key.token)).step
          (.submit (Rows.reply s call key c))).runner (.apply key)).phase
        = some (.answerAsync key.fiber key.token c) := by
      show decisionOf _ (.apply key) (Api.HostSession.applyReply ((s.step (.bind call
        key.token)).step (.submit (Rows.reply s call key c))).session key s.budget.fuel).phase = _
      rw [happlied]
      show (Api.HostSession.readReply _ key).map replyDecision = _
      rw [hread2]
      rfl
    cases hreads : readsOn ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))) (.answerAsync key.fiber key.token c) with
    | false =>
      rw [tapeFrom_stop _ _ _ _ hfront3 hdec3 hreads] at hread
      cases hread
    | true =>
      rw [tapeFrom_take _ _ _ _ hfront3 hdec3 hreads]
      rfl
  · have hfront3 : ((Api.Runner.result ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))).runner (.apply key)).phase == Phase.frontier)
        = true := by
      show ((Api.HostSession.applyReply ((s.step (.bind call key.token)).step
        (.submit (Rows.reply s call key c))).session key s.budget.fuel).phase == Phase.frontier)
        = true
      rw [hfrontier]
      rfl
    rw [tapeFrom_frontier _ _ _ hfront3] at hread
    cases hread

/-! ## The drive -/

/-- The reactor read as a host answers a call on a table row as the reactor does. -/
theorem reactorHost_answer (table : RowTable) {σ : Type} (r : Reactor σ) {i : Nat}
    (hi : i < table.length) {row : Program.Row} {request : Val} {st next : σ} {ex : ExitV}
    (hrow : externalRow table i = some row) (h : r row request st = some (.ofExit ex, next)) :
    (reactorHost table r).answer ⟨⟨i, hi⟩, request⟩ st = some (ex, next) := by
  show (match externalRow table i with
    | none => none
    | some row =>
      match r row request st with
      | some (.ofExit ex, next) => some (ex, next)
      | _ => none) = some (ex, next)
  rw [hrow]
  dsimp only
  rw [h]

/-- **The drive's answers are its reactor's.** From any run, a reactor inside the envelope that
answers with exits drives rows whose tape, when it reads every row, the reactor read as a host
answered: at each answer, the host gives the machine's request the answer's exit, and its state
moves as the reactor's did. Every decision of the tape is a host's (`hostDecision`). Reach: any
run of the table, any rounds. Not established: that the drive finishes or reads every row. -/
theorem drive_hostAnswered {σ : Type} (table : RowTable) (r : Reactor σ)
    (henv : r.Envelops table) (hexits : r.ExitsOnly) :
    ∀ (rounds : Nat) (s : Run) (st : σ), s.built.table = table →
      (tapeFrom s (driveFrom r rounds s st).2.1).2 = [] →
      HostAnswered table (reactorHost table r) s.built.program s.budget.fuel
          ((tapeFrom s (driveFrom r rounds s st).2.1).1.map (·.decision)) s.machine st
          (driveFrom r rounds s st).2.2 ∧
        ((tapeFrom s (driveFrom r rounds s st).2.1).1.map (·.decision)).all hostDecision = true
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | rounds + 1, s, st, htable, hread => by
    rw [driveFrom] at hread ⊢
    split at hread
    · rename_i await hfreshCall
      split at hread
      · rename_i hrow
        exact ⟨rfl, rfl⟩
      · rename_i row hrow
        split at hread
        · rename_i hreact
          exact ⟨rfl, rfl⟩
        · rename_i c next hreact
          dsimp only at hread ⊢
          obtain ⟨hmem, hactive, hpending⟩ := freshCall_facts s await hfreshCall
          obtain ⟨i, hop, hext⟩ := rowOf_external s await.op row hrow
          rw [htable] at hext
          obtain ⟨ex, rfl⟩ := hexits row await.request st c next hreact
          have hreq : requestOf s.machine await.fiber await.token =
              some (.external i, await.request) := by
            rw [← hop]
            exact requestOf_of_mem_awaits s.machine await hmem
          have hfits : admit s.built.table s.machine
              (.answerAsync (⟨await.fiber, await.token⟩ : Key).fiber
                (⟨await.fiber, await.token⟩ : Key).token (.ofExit ex)) = none := by
            rw [htable]
            exact henv s.machine await.fiber await.token i row await.request st (.ofExit ex) next
              hreq hext hreact
          obtain ⟨hA, hB, htape⟩ := tapeFrom_append_read s _ _ hread
          have hans := answer_tape s ⟨await.fiber, await.token⟩ (.ofExit ex)
            (Api.HostSession.Call.claim s ⟨await.fiber, await.token⟩ (.external i) await.request)
            (at_of_requestOf s ⟨await.fiber, await.token⟩ (.external i) await.request hreq)
            hactive hpending hfits hA
          have hmach := play_machine_stepsBy s _ hA
          rw [hans] at hmach
          obtain ⟨hrest, hall⟩ := drive_hostAnswered table r henv hexits rounds
            (s.play (Rows.answer s ⟨await.fiber, await.token⟩ (.ofExit ex))) next
            (by rw [play_built]; exact htable) hB
          rw [hmach, play_built, play_budget, htable] at hrest
          rw [htape, List.map_append, hans]
          refine ⟨hostAnswered_append table (reactorHost table r) _ _ _ _ _ st next _
            ⟨i, await.request, lt_of_externalRow hext, next, hreq,
              reactorHost_answer table r (lt_of_externalRow hext) hext hreact, rfl⟩ hrest, ?_⟩
          rw [List.cons_append, List.nil_append, List.all_cons, hall]
          rfl
    · rename_i hfreshCall
      split at hread
      · rename_i hout
        rw [if_pos hout]
        exact ⟨rfl, rfl⟩
      · rename_i hout
        rw [if_neg hout]
        dsimp only at hread ⊢
        have hflush : ∀ x ∈ (tapeFrom s Rows.flush).1.map (·.decision), x = Api.flush :=
          tapeFrom_control s Api.flush
        split at hread
        · rename_i hdone
          rw [if_pos hdone]
          refine ⟨hostAnswered_quiet table _ _ _ st _ _ fun d hd => Or.inl (hflush d hd), ?_⟩
          rw [List.all_eq_true]
          intro d hd
          rw [hflush d hd]
          rfl
        · rename_i hdone
          rw [if_neg hdone]
          dsimp only at hread ⊢
          obtain ⟨hA, hB, htape⟩ := tapeFrom_append_read s _ _ hread
          have hmach := play_machine_stepsBy s _ hA
          obtain ⟨hrest, hall⟩ := drive_hostAnswered table r henv hexits rounds
            (s.play Rows.flush) st (by rw [play_built]; exact htable) hB
          rw [hmach, play_built, play_budget, htable] at hrest
          rw [htape, List.map_append]
          refine ⟨hostAnswered_append table (reactorHost table r) _ _ _ _ _ st st _
            (hostAnswered_quiet table _ _ _ st _ _ fun d hd => Or.inl (hflush d hd)) hrest, ?_⟩
          rw [List.all_append, hall, Bool.and_true, List.all_eq_true]
          intro d hd
          rw [hflush d hd]
          rfl

/-! ## The driver's run -/

/-- Step of `runWith_hostAnswered`: playing rows appends them to the journal. -/
theorem play_journal (s : Run) (rows : List Command) : (s.play rows).journal = s.journal ++ rows := by
  induction rows generalizing s with
  | nil => exact (List.append_nil _).symm
  | cons c rest ih => rw [Run.play_cons, ih, Run.step_journal, List.append_assoc]; rfl

/-- Step of `runWith_hostAnswered`: a run played from a fresh open was opened as that open. -/
theorem openedOf_play_open (b : Api.Built) (id : String) (budget : Api.Budget)
    (rows : List Command) : openedOf ((Run.open b id budget).play rows) = Run.open b id budget := by
  rw [openedOf, play_built, play_id, play_budget, play_profile]
  rfl

/-- **The driver's run is answered by its reactor.** Open a program, evaluate its root, and
drive it with a reactor inside the envelope that answers with exits. When the run is funded, the
reactor read as a host answered the run's tape from the program's load, its state going from the
start to the drive's end, and every decision of the tape is a host's. -/
theorem runWith_hostAnswered {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.table) (hexits : r.ExitsOnly)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true) :
    HostAnswered b.table (reactorHost b.table r) b.program budget.fuel
        (tapeOf (Run.runWith b r st id budget rounds).1)
        (Api.load b.program budget.compileFuel) st (Run.runWith b r st id budget rounds).2 ∧
      hostDriven (Run.runWith b r st id budget rounds).1 = true := by
  have hrun : (Run.runWith b r st id budget rounds).1 =
      (Run.open b id budget).play (Rows.start ++
        (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).2.1) := by
    show (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1 = _
    rw [drive_eq_play, play_append]
  have hjournal : (Run.runWith b r st id budget rounds).1.journal = Rows.start ++
      (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).2.1 := by
    rw [hrun, play_journal, open_journal]
    rfl
  have htapeOf : tapeOf (Run.runWith b r st id budget rounds).1 =
      (tapeFrom (Run.open b id budget) (Rows.start ++
        (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).2.1)).1.map
          (·.decision) := by
    rw [tapeOf, ← hjournal, hrun, openedOf_play_open]
  have hread : (tapeFrom (Run.open b id budget) (Rows.start ++
      (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).2.1)).2 = [] := by
    have h := List.isEmpty_iff.mp hfund
    rw [hrun, openedOf_play_open, play_journal, open_journal] at h
    exact h
  obtain ⟨hA, hB, htape⟩ := tapeFrom_append_read _ _ _ hread
  have hstart : ∀ x ∈ (tapeFrom (Run.open b id budget) Rows.start).1.map (·.decision),
      x = Api.evaluate := tapeFrom_control _ Api.evaluate
  obtain ⟨hdrive, hall⟩ := drive_hostAnswered b.table r henv hexits rounds
    ((Run.open b id budget).play Rows.start) st (by rw [play_built]; rfl) hB
  rw [play_built, play_budget, play_machine_stepsBy _ _ hA] at hdrive
  refine ⟨?_, ?_⟩
  · rw [htapeOf, htape, List.map_append]
    exact hostAnswered_append b.table (reactorHost b.table r) _ _ _ _ _ st st _
      (hostAnswered_quiet b.table _ _ _ st _ _ fun d hd => Or.inr (hstart d hd)) hdrive
  · show (tapeOf (Run.runWith b r st id budget rounds).1).all hostDecision = true
    rw [htapeOf, htape, List.map_append, List.all_append, hall, Bool.and_true, List.all_eq_true]
    intro d hd
    rw [hstart d hd]
    rfl

/-- **The driver's run, read as a session** (the shared prefix of H9 at the driver, straight and
on loops): it is reached, at its program and budget, answered by its reactor read as a host and
driven by it. -/
theorem runWith_session {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.table) (hexits : r.ExitsOnly)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true) :
    Run.Reached (Run.runWith b r st id budget rounds).1 ∧
      (Run.runWith b r st id budget rounds).1.built = b ∧
      (Run.runWith b r st id budget rounds).1.budget = budget ∧
      HostAnswered b.table (reactorHost b.table r) b.program budget.fuel
        (tapeOf (Run.runWith b r st id budget rounds).1)
        (Api.load b.program budget.compileFuel) st (Run.runWith b r st id budget rounds).2 ∧
      hostDriven (Run.runWith b r st id budget rounds).1 = true := by
  obtain ⟨hA, hhost⟩ := runWith_hostAnswered b r st id budget rounds henv hexits hfund
  refine ⟨?_, ?_, ?_, hA, hhost⟩
  · show Run.Reached (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1
    rw [drive_eq_play]
    exact Run.Reached.play _ _ (Run.Reached.play _ _ (Run.Reached.open b id budget))
  · show (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1.built = b
    rw [drive_eq_play, play_built, play_built]
    rfl
  · show (driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1.budget = budget
    rw [drive_eq_play, play_budget, play_budget]
    rfl

/-- **H9 at the driver**: the reactor's run of the call tree is the driver's. Open a program of
the fragment, evaluate its root and drive it with a reactor inside the envelope that answers
with exits. When the run is funded, at rest and its root exited, the reactor read as a host runs
the program's call tree to the root's exit with the run's stores, and ends at the drive's state.
Reach: `StraightRows`, one fiber, a reactor inside the envelope that answers with exits. It does
not establish that the drive finishes, that its rounds suffice, or that the run is funded.
Concept `translation-simulation`, role simulation; requirement R6. Consumer: the run
interface's hosts, composed by `Effects.Comodel` (slice CO-6). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_denotes {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.table) (hexits : r.ExitsOnly)
    (hfrag : StraightRows b.table b.program = true)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r st id budget rounds).1.exit = some ex) :
    hostRun (reactorHost b.table r) b.program [] Stores.empty st =
      some (ex, ((Run.runWith b r st id budget rounds).1.machine.state,
        (Run.runWith b r st id budget rounds).2)) := by
  obtain ⟨hreach, hbuilt, hbudget, hA, hhost⟩ :=
    runWith_session b r st id budget rounds henv hexits hfund
  have h := denoteRows_eq_session_host (Run.runWith b r st id budget rounds).1 hreach hfund hrest
    hhost
  rw [hbuilt, hbudget] at h
  exact h hfrag (reactorHost b.table r) st _ hA ex hex

/-! ## A reactor behind its rows' types

The envelope asks a reactor's answers to be admitted at every machine that holds the call. A
row's columns decide it, except at a column that allocates an external handle: a success is a
member of the answer column and holds no handle, and a failure holds no reserved defect and fits
the error column. Membership at the empty allocation table is membership at every table
(`hasTy_append`), so a reactor that answers only such exits is inside the envelope, whatever
the machine. `Reactor.guardRows` makes any reactor one: it refuses every other answer. -/

/-- Whether a row's columns admit an answer at every machine: a success that is a member of an
answer column that allocates nothing and that holds no handle, or a failure with no reserved
defect whose reasons fit the error column. A delayed cell read is never admitted here. -/
def answerAdmits (row : Program.Row) : Answer → Bool
  | .ofExit (.success v) =>
    !allocates row.answer && Val.hasTy v row.answer [] && (Store.Val.handles v).isEmpty
  | .ofExit (.failure cause) =>
    !cause.reasons.any reservedDie && cause.reasons.all (errAdmits row.error)
  | .ofRefGet _ => false

/-- A reactor behind its rows' types: it gives the reactor's answer where the row admits it at
every machine (`answerAdmits`), and no answer otherwise. -/
def Reactor.guardRows {σ : Type} (r : Reactor σ) : Reactor σ :=
  fun row request st => (r row request st).filter fun result => answerAdmits row result.1

/-- Step of `guardRows_envelops`: the machine admits an answer at a call it holds, on a table
row, where the row admits it at every machine. -/
theorem admit_of_answerAdmits (table : RowTable) (m : Api.Machine) (fiber : FiberId)
    (token i : Nat) (row : Program.Row) (request : Val) (c : Answer)
    (hreq : requestOf m fiber token = some (.external i, request))
    (hrow : externalRow table i = some row) (hadmits : answerAdmits row c = true) :
    admit table m (.answerAsync fiber token c) = none := by
  obtain ⟨f, controller, cancel, origin, hf, hp, -⟩ := requestOf_current m fiber token _ _ hreq
  have hanswer : admitAnswer row m fiber token c = none := by
    cases c with
    | ofExit ex =>
      cases ex with
      | success v =>
        simp only [answerAdmits, Bool.and_eq_true, Bool.not_eq_true'] at hadmits
        obtain ⟨⟨halloc, hty⟩, hhandles⟩ := hadmits
        have hmember : Val.hasTy v row.answer m.state.externals.allocated = true :=
          hasTy_append row.answer v [] m.state.externals.allocated hty
        have hvalue : (externalValue row.answer m.state.externals.allocated v).isNone = false := by
          rw [externalValue_unallocating halloc, hmember, hhandles]
          rfl
        have hminted : mintedIn m v = true := by
          rw [mintedIn, List.isEmpty_iff.mp hhandles]
          rfl
        simp only [admitAnswer, hvalue, hminted, Bool.not_true, Bool.false_eq_true, if_false]
      | failure cause =>
        simp only [answerAdmits, Bool.and_eq_true, Bool.not_eq_true'] at hadmits
        obtain ⟨hreserved, herr⟩ := hadmits
        simp only [admitAnswer, hreserved, herr, Bool.false_eq_true, if_false, if_true]
    | ofRefGet cell => cases hadmits
  simp only [admit, hf, hp, ne_eq, not_true_eq_false, if_false, hreq, hrow]
  exact hanswer

/-- **A reactor behind its rows' types is inside the envelope**, at every table: each answer it
gives at a call a machine holds is one the machine admits. -/
theorem guardRows_envelops {σ : Type} (r : Reactor σ) (table : RowTable) :
    r.guardRows.Envelops table := by
  intro m fiber token i row request st c next hreq hrow hguard
  have hadmits : answerAdmits row c = true := by
    unfold Reactor.guardRows at hguard
    cases hr : r row request st with
    | none =>
      rw [hr] at hguard
      cases hguard
    | some result =>
      rw [hr, Option.filter_some] at hguard
      split at hguard
      · cases hguard
        assumption
      · cases hguard
  exact admit_of_answerAdmits table m fiber token i row request c hreq hrow hadmits

/-- A reactor behind its rows' types answers with exits. -/
theorem guardRows_exitsOnly {σ : Type} (r : Reactor σ) : r.guardRows.ExitsOnly := by
  intro row request st c next hguard
  unfold Reactor.guardRows at hguard
  cases hr : r row request st with
  | none =>
    rw [hr] at hguard
    cases hguard
  | some result =>
    rw [hr, Option.filter_some] at hguard
    split at hguard
    · rename_i hadmits
      cases hguard
      cases c with
      | ofExit ex => exact ⟨ex, rfl⟩
      | ofRefGet cell => cases hadmits
    · cases hguard

/-- **H9 at the driver, for any reactor behind its rows' types.** Guard a reactor by its rows'
columns and drive a `StraightRows` program with it. When the run is funded, at rest and its root
exited, the guarded reactor, read as a host, runs the program's call tree to the root's exit
with the run's stores, and ends at the drive's state. It is `runWith_denotes` with the envelope
supplied by the guard. Reach and limits as there; a row whose answer column allocates an
external handle answers nothing through the guard. Concept `translation-simulation`, role
simulation; requirement R6. Consumer: the battery's repository runs
(`Test/Api/SessionMeaning.lean`). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_guarded_denotes {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (hfrag : StraightRows b.table b.program = true)
    (hfund : funded (Run.runWith b r.guardRows st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r.guardRows st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r.guardRows st id budget rounds).1.exit = some ex) :
    hostRun (reactorHost b.table r.guardRows) b.program [] Stores.empty st =
      some (ex, ((Run.runWith b r.guardRows st id budget rounds).1.machine.state,
        (Run.runWith b r.guardRows st id budget rounds).2)) :=
  runWith_denotes b r.guardRows st id budget rounds (guardRows_envelops r b.table)
    (guardRows_exitsOnly r) hfrag hfund hrest ex hex

/-! ## Any host drives the run

A table's rows have distinct keys (`rowKey`: the spelling and the trailing arguments;
`Table.lawful`). So a reactor that finds its row by key can ask a host of the row signature at
that row's position (`Reactor.ofHost`), and reading that reactor back as a host gives the host
again at every external row (`reactorHost_ofHost`). Every construction of `Effects.Comodel`
(routing, renaming, implementation by programs over other operations, admission, recording)
then drives a run. Behind the rows' types, H9 holds at the driver for every host so driven
(`runWith_host_denotes`), and a host whose answers the rows admit needs no guard
(`hostGuard_of_meets`). -/

/-- The position of a row in a table, by its key. -/
def rowPosition (table : RowTable) (row : Program.Row) : Option (Fin table.length) :=
  (table.findIdx? fun r => decide (rowKey r = rowKey row)).bind fun i =>
    if hi : i < table.length then some ⟨i, hi⟩ else none

/-- **A host of the row signature as a reactor**: it finds the row by its key, asks the host at
that position, and answers the host's exit. -/
def Reactor.ofHost (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ) :
    Reactor σ :=
  fun row request st =>
    match rowPosition table row with
    | none => none
    | some i => (host.answer ⟨i, request⟩ st).map fun result => (.ofExit result.1, result.2)

/-- Whether a row admits an exit at every machine: `answerAdmits` at an external row, and no
exit elsewhere. -/
def externalAdmitsAt (table : RowTable) (op : (RowSig table).Op) (ex : ExitV) : Bool :=
  match externalRow table op.1.val with
  | some row => answerAdmits row (.ofExit ex)
  | none => false

/-- A host behind its rows' types: its answers that an external row admits at every machine. -/
def hostGuard (table : RowTable) {σ : Type} (host : Effects.Comodel (RowSig table) σ) :
    Effects.Comodel (RowSig table) σ :=
  host.guard (externalAdmitsAt table)

/-- A host whose answers the rows admit is its own guard. -/
theorem hostGuard_of_meets (table : RowTable) {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    (h : host.Meets fun op ex => externalAdmitsAt table op ex = true) : hostGuard table host = host :=
  Effects.Comodel.guard_of_meets h

/-- Step of `reactorHost_ofHost`: an external row of a table with distinct keys is found at its
own position. -/
theorem rowPosition_external {table : RowTable} (hkeys : (table.map rowKey).Nodup) {i : Nat}
    {row : Program.Row} (hrow : externalRow table i = some row) :
    rowPosition table row = some ⟨i, lt_of_externalRow hrow⟩ := by
  have hi := lt_of_externalRow hrow
  have hkey : rowKey row = rowKey table[i] := by
    unfold externalRow at hrow
    obtain ⟨w, hw, hsome⟩ := Option.bind_eq_some_iff.mp hrow
    obtain ⟨_, -, hsome⟩ := Option.bind_eq_some_iff.mp hsome
    cases hsome
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hw
    subst hw
    rfl
  unfold rowPosition
  rw [hkey, rowIndex_roundTrip table hkeys i hi]
  exact dif_pos hi

/-- Two hosts that answer alike are one. -/
theorem comodel_ext {S : Effects.Signature.{0, 0}} {σ : Type} {a b : Effects.Comodel S σ}
    (h : ∀ op st, a.answer op st = b.answer op st) : a = b := by
  cases a
  cases b
  congr 1
  funext op st
  exact h op st

/-- **Reading a host as a reactor and back, behind the rows' types, is the host behind them**,
at a table with distinct keys. -/
theorem reactorHost_ofHost (table : RowTable) (hkeys : (table.map rowKey).Nodup) {σ : Type}
    (host : Effects.Comodel (RowSig table) σ) :
    reactorHost table (Reactor.ofHost table host).guardRows = hostGuard table host := by
  apply comodel_ext
  intro op st
  obtain ⟨⟨i, hi⟩, v⟩ := op
  show (match externalRow table i with
      | none => none
      | some row =>
        match (Reactor.ofHost table host).guardRows row v st with
        | some (.ofExit ex, next) => some (ex, next)
        | _ => none) =
    (host.answer ⟨⟨i, hi⟩, v⟩ st).filter fun result =>
      externalAdmitsAt table ⟨⟨i, hi⟩, v⟩ result.1
  cases hrow : externalRow table i with
  | none =>
    have hadmit : ∀ ex, externalAdmitsAt table ⟨⟨i, hi⟩, v⟩ ex = false := by
      intro ex
      show (match externalRow table i with
        | some row => answerAdmits row (.ofExit ex)
        | none => false) = false
      rw [hrow]
    dsimp only
    cases hans : host.answer ⟨⟨i, hi⟩, v⟩ st with
    | none => rfl
    | some result =>
      rw [Option.filter_some, hadmit result.1]
      rfl
  | some row =>
    have hadmit : ∀ ex, externalAdmitsAt table ⟨⟨i, hi⟩, v⟩ ex = answerAdmits row (.ofExit ex) := by
      intro ex
      show (match externalRow table i with
        | some row => answerAdmits row (.ofExit ex)
        | none => false) = _
      rw [hrow]
    have hpos := rowPosition_external hkeys hrow
    dsimp only
    show (match ((Reactor.ofHost table host) row v st).filter
        (fun result => answerAdmits row result.1) with
      | some (.ofExit ex, next) => some (ex, next)
      | _ => none) = _
    show (match ((match rowPosition table row with
        | none => none
        | some j => (host.answer ⟨j, v⟩ st).map fun result => (Completion.ofExit result.1, result.2))
          : Option (Answer × σ)).filter (fun result => answerAdmits row result.1) with
      | some (.ofExit ex, next) => some (ex, next)
      | _ => none) = _
    rw [hpos]
    dsimp only
    cases hans : host.answer ⟨⟨i, hi⟩, v⟩ st with
    | none => rfl
    | some result =>
      obtain ⟨ex, next⟩ := result
      rw [Option.map_some, Option.filter_some, Option.filter_some, hadmit ex]
      by_cases hok : answerAdmits row (.ofExit ex) = true
      · rw [if_pos hok, if_pos hok]
        rfl
      · rw [if_neg hok, if_neg hok]
        rfl

/-- **H9 at the driver, for any host.** Read a host of the row signature as a reactor, behind
its rows' types, and drive a `StraightRows` program with it, at a table with distinct keys. When
the run is funded, at rest and its root exited, the host behind its rows' types runs the
program's call tree to the root's exit with the run's stores, and ends at the drive's state. A
host whose answers the rows admit is its own guard (`hostGuard_of_meets`). Reach and limits as
`runWith_denotes`. Concept `translation-simulation`, role simulation; requirement R6. Consumer:
the battery's recorded and replayed sessions (`Test/Api/SessionMeaning.lean`). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_host_denotes {σ : Type} (b : Api.Built) (host : Effects.Comodel (RowSig b.table) σ)
    (st : σ) (id : String) (budget : Api.Budget) (rounds : Nat)
    (hkeys : (b.table.map rowKey).Nodup) (hfrag : StraightRows b.table b.program = true)
    (hfund : funded (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1
      = true)
    (hrest : atRest (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1
      = true)
    (ex : ExitV)
    (hex : (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1.exit =
      some ex) :
    hostRun (hostGuard b.table host) b.program [] Stores.empty st =
      some (ex, ((Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1.machine.state,
        (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).2)) := by
  rw [← reactorHost_ofHost b.table hkeys host]
  exact runWith_guarded_denotes b (Reactor.ofHost b.table host) st id budget rounds hfrag hfund
    hrest ex hex

/-! ## Typed layers need no guard

A layer implements each row by a program over another signature (`Effects.Comodel.through`).
Take a layer typed from the rows' protocol to a lower protocol (`Effects.Handler.Typed`). A host
that meets the lower protocol meets the rows' protocol behind the layer
(`Effects.Comodel.Meets.through`), so the layered host is its own guard (`hostGuard_through`).
Then H9 holds at the driver for the layered host itself (`runWith_layer_denotes`). A retry is
such a layer at every protocol (`retry_typed`). -/

/-- The rows' protocol: the exits an external row admits at every machine. -/
def externalProtocol (table : RowTable) : Effects.Protocol (RowSig table) :=
  fun op ex => externalAdmitsAt table op ex = true

/-- A host behind a typed layer is its own guard. -/
theorem hostGuard_through (table : RowTable) {T : Effects.Signature.{0, 0}}
    {PT : Effects.Protocol T} {impl : Effects.Handler (RowSig table) (Effects.Program T)}
    (htyped : impl.Typed (externalProtocol table) PT) {σ : Type} {host : Effects.Comodel T σ}
    (hmeets : host.Meets PT) : hostGuard table (host.through impl) = host.through impl :=
  hostGuard_of_meets table (Effects.Comodel.Meets.through htyped hmeets)

/-- **H9 at the driver, for a typed layer.** Implement the rows by a layer typed from the rows'
protocol to a lower one, over a host that meets the lower protocol, and drive a `StraightRows`
program with the layered host read as a reactor. When the run is funded, at rest and its root
exited, the layered host itself runs the program's call tree to the root's exit with the run's
stores, and ends at the drive's state. Reach and limits as `runWith_denotes`; the layer's typing
and the host's protocol are premises. Concept `translation-simulation`, role simulation;
requirement R6. Consumer: typed host utilities (the battery's retry), and the printed services
of slice CO-6b, shape (c). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_layer_denotes {σ : Type} {T : Effects.Signature.{0, 0}} {PT : Effects.Protocol T}
    (b : Api.Built) (impl : Effects.Handler (RowSig b.table) (Effects.Program T))
    (htyped : impl.Typed (externalProtocol b.table) PT) (host : Effects.Comodel T σ)
    (hmeets : host.Meets PT) (st : σ) (id : String) (budget : Api.Budget) (rounds : Nat)
    (hkeys : (b.table.map rowKey).Nodup) (hfrag : StraightRows b.table b.program = true)
    (hfund : funded (Run.runWith b (Reactor.ofHost b.table (host.through impl)).guardRows st id
      budget rounds).1 = true)
    (hrest : atRest (Run.runWith b (Reactor.ofHost b.table (host.through impl)).guardRows st id
      budget rounds).1 = true)
    (ex : ExitV)
    (hex : (Run.runWith b (Reactor.ofHost b.table (host.through impl)).guardRows st id budget
      rounds).1.exit = some ex) :
    hostRun (host.through impl) b.program [] Stores.empty st =
      some (ex, ((Run.runWith b (Reactor.ofHost b.table (host.through impl)).guardRows st id budget
        rounds).1.machine.state,
        (Run.runWith b (Reactor.ofHost b.table (host.through impl)).guardRows st id budget
          rounds).2)) := by
  have h := runWith_host_denotes b (host.through impl) st id budget rounds hkeys hfrag hfund hrest ex
    hex
  rw [hostGuard_through b.table htyped hmeets] at h
  exact h

/-- **A retry**: each row is called, and called once more where its first exit is a failure. -/
def retry (table : RowTable) : Effects.Handler (RowSig table) (Effects.Program (RowSig table)) where
  handle op := .vis op fun ex => match ex with
    | .failure _ => .vis op .pure
    | .success _ => .pure ex

/-- A retry is typed from any protocol to itself: each exit it answers is one that the host below
gave. -/
theorem retry_typed (table : RowTable) (P : Effects.Protocol (RowSig table)) :
    (retry table).Typed P P :=
  fun _ ex hex => match ex, hex with
    | .failure _, _ => fun _ hex' => hex'
    | .success _, hex => hex

/-! ## The session as a system

The coalgebra's reading of the host session. A program's call tree, with its store operations
answered by the stores and hidden, is a system of the row signature (`sessionSystem`,
`Effects.System.peel`). A state is a residual call tree with its stores. A step ends with the
exit and the stores, or calls a host row and continues from the answer. Its unfolding at a depth
is the call tree the session walks, as far as that depth, with a cut below it: the picture of a
session, top to bottom. Where the system finishes against a host, the host's run of the call
tree finishes the same way (`Effects.System.run_peel`). So under H9's premises, every finished
run of the system, at every depth, is the session's observation (`sessionSystem_finished`). -/

/-- **The session's system**: the call tree with the stores hidden. -/
def sessionSystem (table : RowTable) :
    Effects.System (RowSig table) (ExitV × Stores) (Effects.Program (RowsSig table) ExitV × Stores) :=
  Effects.System.peel storeStep

/-- **A finished unfolding is the session's observation.** For a recorded `StraightRows` run that
is funded, at rest, driven by a host and finished, and a host whose answers are the run's
(`HostAnswered`): wherever the session's system finishes against that host, at any depth, it
ends with the root's exit and the run's stores, and the host ends where the answers left it. A
depth too small is a cut, never an error. Reach and limits as H9 (`denoteRows_eq_session_host`).
Concept `translation-simulation`, role simulation; requirement R6. Consumer: the picture of a
session as its system's unfolding (the coalgebra note, sections 5.2 and 5.3). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem sessionSystem_finished (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : StraightRows s.built.table s.built.program = true) {σ : Type}
    (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st')
    (ex : ExitV) (hex : s.exit = some ex) (depth : Nat) (result : ExitV × Stores) (finish : σ)
    (hrun : (sessionSystem s.built.table).run host depth
      (denoteRows s.built.table s.built.program [], Stores.empty) st = some (some result, finish)) :
    result = (ex, s.machine.state) ∧ finish = st' := by
  have hpeel := Effects.System.run_peel storeStep host depth
    (denoteRows s.built.table s.built.program []) Stores.empty st hrun
  have h9 := denoteRows_eq_session_host s hreach hfund hrest hhost hfrag host st st' hA ex hex
  have heq : some (result.1, (result.2, finish)) = some (ex, (s.machine.state, st')) :=
    hpeel.symm.trans h9
  rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at heq
  exact ⟨Prod.ext heq.1 heq.2.1, heq.2.2⟩

/-- **The session's system finishes, at the session's observation.** Under H9's premises, the
session's system, run against the host, finishes at some depth with the root's exit and the
run's stores, the host ending where the answers left it. With `sessionSystem_finished`, the
system's finished runs are exactly the session's observation: the unfolding is the session.
Reach and limits as H9. Concept `translation-simulation`, role simulation; requirement R6.
Consumer: the picture of a session as its system's unfolding (the coalgebra note, section 5.3). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem sessionSystem_finishes (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : StraightRows s.built.table s.built.program = true) {σ : Type}
    (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st')
    (ex : ExitV) (hex : s.exit = some ex) :
    ∃ depth, (sessionSystem s.built.table).run host depth
      (denoteRows s.built.table s.built.program [], Stores.empty) st =
        some (some (ex, s.machine.state), st') :=
  Effects.System.run_peel_complete storeStep host (denoteRows s.built.table s.built.program [])
    Stores.empty st (denoteRows_eq_session_host s hreach hfund hrest hhost hfrag host st st' hA ex hex)

end Effect4.Run
