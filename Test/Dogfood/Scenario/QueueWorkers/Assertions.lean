import Test.Dogfood.Proofs.CrewLogHistory
import Test.Dogfood.Scenario.QueueWorkers.Ledger
import Test.Dogfood.Scenario.QueueWorkers.CleanupSource
import Test.Dogfood.Scenario.Programs
import Test.Dogfood.Scenario.Frame
import Effect4.Laws.Program.ReleaseTrace
import Test.Dogfood.Proofs.CrewLogHistory

/-!
# Queue assertions at every command boundary

Concepts: translation-simulation R10, scope-lifetime-finalization R11 and reactive-scheduling R12.
Question: these helpers serve the four original queue scenario clauses, consumed by `queueWorkers`.
Reach: the actual built crew, all job counts, command budgets, raw rows and admitted host replies.
The assertions retain job custody, withdrawn jobs and actual release-source identities.
The rest reading requires a journal of host rows and the original rest premise.
Two named preservation obligations retain the unfinished queue custody and resting-state work.
The four assemblies are proved modulo those obligations.
They establish neither progress, fairness nor any outside-host behavior.
Decisions rows 254 and 275 bound the scenario fragment.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.QueueWorkers.Assertions

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)
open Accounting

/-- The rows that a host act plays: a held call, a reply receipt of a completion, a reply
application, the root's start, a flush, a clock step and an interruption with no interruptor. -/
def HostRow : Command → Prop
  | .bind _ _ => True
  | .submit reply => ∃ e, reply.completion = .ofExit e
  | .apply _ => True
  | .control (.evaluate fiber) => fiber = Api.root
  | .control .flush => True
  | .control (.advance _) => True
  | .control (.interruptFrom none _ _) => True
  | .control _ => False

open Test.Dogfood.Scenario.QueueWorkers in
/-- A host act plays host rows only. -/
theorem hostAct_rows (s : Run) (m : Move) (h : Move.hostAct m = true) :
    ∀ c ∈ m.rows s, HostRow c := by
  intro c hc
  cases m with
  | control d =>
    rw [List.mem_singleton.mp hc]
    cases d with
    | evaluate fiber => exact beq_iff_eq.mp h
    | flush => trivial
    | advance _ => trivial
    | interruptFrom who annotations target =>
      cases who with
      | none => trivial
      | some _ => exact absurd h Bool.false_ne_true
    | fire _ => exact absurd h Bool.false_ne_true
    | yieldVerdict _ _ => exact absurd h Bool.false_ne_true
    | answerAsync _ _ _ => exact absurd h Bool.false_ne_true
    | installMiddleware => exact absurd h Bool.false_ne_true
  | hold sel =>
    simp only [Effect4.Run.Event.rows, Effect4.Run.Event.commands] at hc
    cases hone : sel.one s with
    | none =>
      rw [hone] at hc
      exact absurd hc List.not_mem_nil
    | some seen =>
      rw [hone] at hc
      dsimp only at hc
      cases hat : Api.HostSession.Call.at s seen.key with
      | none =>
        rw [hat] at hc
        exact absurd hc List.not_mem_nil
      | some claim =>
        rw [hat] at hc
        rw [List.mem_singleton.mp hc]
        trivial
  | receive sel completion =>
    cases completion with
    | ofExit e =>
      simp only [Effect4.Run.Event.rows, Effect4.Run.Event.commands] at hc
      cases hkey : sel.resolve s with
      | none =>
        rw [hkey] at hc
        exact absurd hc List.not_mem_nil
      | some key =>
        rw [hkey] at hc
        dsimp only at hc
        cases hheld : (bound s).reverse.find?
            (fun entry => (⟨entry.1.fiber, entry.2⟩ : Api.HostSession.Key) == key) with
        | some entry =>
          rw [hheld] at hc
          rw [List.mem_singleton.mp hc]
          exact ⟨e, rfl⟩
        | none =>
          rw [hheld] at hc
          dsimp only at hc
          unfold Rows.receive at hc
          split at hc
          · exact absurd hc List.not_mem_nil
          · rcases List.mem_cons.mp hc with rfl | hc
            · trivial
            · rw [List.mem_singleton.mp hc]
              exact ⟨e, rfl⟩
    | ofRefGet _ => exact absurd h Bool.false_ne_true
  | apply sel =>
    simp only [Effect4.Run.Event.rows, Effect4.Run.Event.commands] at hc
    cases hkey : sel.resolve s with
    | none =>
      rw [hkey] at hc
      exact absurd hc List.not_mem_nil
    | some key =>
      rw [hkey] at hc
      rw [List.mem_singleton.mp hc]
      trivial
  | wire _ => exact absurd h Bool.false_ne_true

open Test.Dogfood.Scenario.QueueWorkers in
/-- A script of host acts plays host rows only. -/
theorem hostAct_scriptRows : ∀ (s : Run) (moves : List Move), moves.all Move.hostAct = true →
    ∀ c ∈ scriptRows s moves, HostRow c
  | _, [], _, c, hc => absurd hc List.not_mem_nil
  | s, m :: ms, h, c, hc => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_append.mp hc with here | later
    · exact hostAct_rows s m h.1 c here
    · exact hostAct_scriptRows (Test.Dogfood.Scenario.step s m) ms h.2 c later

/-- Every command in the actual session journal is a host row. -/
def HostRows (s : Run) : Prop := ∀ c ∈ s.journal, HostRow c

/-- A conserving ledger matches the actual observation, including unfinished command custody. -/
def RawJobs (s : Run) : Prop :=
  ∃ a : Ledger, a.Shows (observe s) ∧ a.Conserved

/-- The retained original ledger claim reads accepted terminal reply applications. -/
def OriginalRawJobs (s : Run) : Prop :=
  ∃ a : Ledger, a.Shows (QueueWorkers.Original.observe s) ∧ a.Conserved

/-- The conserving ledger reads resolved jobs entering actual offer continuations. -/
def Jobs (s : Run) : Prop := RawJobs s

/-- At rest a host journal empties custody and bounds loss, with the queue's actual wait counts. -/
def Rest (s : Run) : Prop :=
  HostRows s → Run.atRest s = true →
    ∃ a : Ledger, a.Shows (observe s) ∧ a.Conserved ∧ a.custody = [] ∧
      a.lost.length ≤ (if (observe s).live 3 then 0 else 1) ∧ a.RestQueue (observe s)

abbrev acquirePath := Programs.queueAcquire

/-- The third allocated reference records actual cleanup identities. -/
def log (m : NativeMachine) : List Val := entries (m.state.refs[2]?)

/-- Each actual acquisition registers once, each release spends its registration, and each log
entry spends its release start. All counters use the shared source-path classifiers. -/
structure Cleanup (m : NativeMachine) : Prop where
  registrations : ∀ i ∈ [1, 2, 3],
    m.trace.countP (ReleaseTrace.registeredAt (acquirePath i)) ≤ 1
  releases : ∀ i ∈ [1, 2, 3],
    m.trace.countP (ReleaseTrace.releaseAt (acquirePath i)) ≤
      m.trace.countP (ReleaseTrace.registeredAt (acquirePath i))
  identities : ∀ v ∈ log m, ∃ i ∈ [1, 2, 3], v = .nat i
  logs : ∀ i ∈ [1, 2, 3],
    (log m).count (.nat i) ≤ m.trace.countP (ReleaseTrace.releaseAt (acquirePath i))

/-- Concrete assertions at every command boundary, restricted to actual admitted histories. -/
structure Basis (b : Api.Built) (s : Run) : Prop where
  built : s.built = b
  reached : Run.Reached s
  history : Run.HistoryOf b s.budget.compileFuel s.machine
  sites : ∀ i ∈ [1, 2, 3], Programs.acquisitionAt b.program (acquirePath i) = true
  placement : ∀ i ∈ [1, 2, 3], OncePlaced (Node.eff b.program) (acquirePath i) = true

/-- Conservation, rest and cleanup assertions share only the actual source and admitted history. -/
structure Holds (b : Api.Built) (s : Run) : Prop extends Basis b s where
  jobs : Jobs s
  rest : Rest s
  cleanup : Cleanup s.machine

/-- Initial assertion: the universally certified source has an empty ledger and cleanup trace. -/
theorem opened (total fuel : Nat) (b : Api.Built)
    (hb : Api.Author.build (crew total) = .ok b) : Holds b (openedAt fuel b) := by
  refine ⟨⟨rfl, Run.Reached.opened b "queue-workers" { budget with fuel := fuel } "",
    ⟨[], trivial, rfl⟩, ?_, Programs.queueCrew_acquire_once_placed total b hb⟩,
    ?_, ?_, ?_⟩
  · rw [Programs.queue_built_program total b hb]
    exact Programs.queue_acquisition_sites total
  · exact ⟨Ledger.empty, ledger_opened fuel b⟩
  · intro _ _
    obtain ⟨shows, conserved⟩ := ledger_opened fuel b
    refine ⟨Ledger.empty, shows, conserved, rfl, Nat.zero_le _, ?_⟩
    exact ⟨rfl, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i _
      exact Nat.zero_le 1
    · intro i _
      exact Nat.le_refl 0
    · intro v hv
      exact False.elim (List.not_mem_nil hv)
    · intro i _
      exact Nat.le_refl 0

/-- Machine-to-model preservation for `held_within_fed` on actual offer-entry values.
It needs the queue-cell writer census, exact take replies and once-entered continuations.
Consumer: `jobs_boundary`, then the first clause. It establishes no rest or progress claim. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal jobs_step :
  ∀ (total : Nat) (b : Api.Built) (s : Run) (c : Command),
    Api.Author.build (crew total) = .ok b → Basis b s → Jobs s → Run.rowReads s c = true →
    Jobs (s.step c)

/-- Rest preservation for `fed_accounted` and `queue_settled` at an actual command boundary.
It needs committed delivery custody, interrupted withdrawal and queue wake-to-wait correspondence.
Consumer: `rest_script`, then the two rest clauses. It establishes no fairness or liveness claim. -/
@[semantics "reactive-scheduling" (requirement := R12)]
proof_goal rest_step :
  ∀ (total : Nat) (b : Api.Built) (s : Run) (c : Command),
    Api.Author.build (crew total) = .ok b → Basis b s → Jobs s → Rest s → Run.rowReads s c = true →
    Rest (s.step c)

/-- The concrete cleanup writer bound on the original actual history.
Each observed identity spends a release start at its own source acquisition.
Consumer: `cleanup_step`, then the unchanged `releases_once`; no progress or release order follows. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem logs_history (total compileFuel : Nat) (b : Api.Built) (machine : NativeMachine)
    (built : Api.Author.build (crew total) = .ok b) (history : Run.HistoryOf b compileFuel machine) :
    (∀ value ∈ log machine, ∃ i ∈ [1, 2, 3], value = .nat i) ∧
      ∀ i ∈ [1, 2, 3], (log machine).count (.nat i) ≤
        machine.trace.countP (ReleaseTrace.releaseAt (acquirePath i)) := by
  exact (Proofs.CrewLogHistory.queue total b built compileFuel machine history).observe
    (log machine) (CrewLogs.list_observation _)


/-- Cleanup preservation uses source uniqueness, actual release custody and the initialized writer history.
Consumer: `cleanup_boundary`, then the unchanged cleanup clause; no progress or order follows. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem cleanup_step :
  ∀ (total : Nat) (b : Api.Built) (s : Run) (c : Command),
    Api.Author.build (crew total) = .ok b → Basis b s → Cleanup s.machine → Run.rowReads s c = true →
    Cleanup (s.step c).machine := by
  intro total b s command built held _ _
  have reached := Run.Reached.step s command held.reached
  have history := (Run.reached_history (s.step command) reached).2
  rw [Run.step_built, held.built] at history
  have logs := logs_history total (s.step command).budget.compileFuel b (s.step command).machine built history
  exact ⟨CleanupSource.registrations total _ b built _ history,
    CleanupSource.releases total _ b built _ history, logs.1, logs.2⟩

/-- Actual source and admission facts extend without a preservation goal. -/
theorem basis_step (b : Api.Built) (s : Run) (c : Command) (hs : Basis b s) :
    Basis b (s.step c) := by
  have reached := Run.Reached.step s c hs.reached
  have history := (Run.reached_history (s.step c) reached).2
  rw [Run.step_built, hs.built] at history
  exact ⟨(Run.step_built s c).trans hs.built, reached, history, hs.sites, hs.placement⟩

/-- A refused row keeps the conservation assertion outright. -/
theorem jobs_refused (s : Run) (c : Command)
    (why : Api.HostSession.Refusal) (hlen : s.journal.length = s.phases.length)
    (h : (Api.Runner.result s.runner c).phase = .refused why) (hs : Jobs s) :
    Jobs (s.step c) := by
  obtain ⟨a, shows, conserved⟩ := hs
  exact ⟨a, shows_refused s c why hlen h shows, conserved⟩

/-- A refused row keeps the cleanup assertion outright. -/
theorem cleanup_refused (s : Run) (c : Command)
    (why : Api.HostSession.Refusal)
    (h : (Api.Runner.result s.runner c).phase = .refused why) (hs : Cleanup s.machine) :
    Cleanup (s.step c).machine := by
  rw [machine_refused s c why h]
  exact hs

/-- Actual journals retain one verdict per command. -/
theorem reached_lengths (s : Run) (hs : Run.Reached s) :
    s.journal.length = s.phases.length := by
  induction hs with
  | opened _ _ _ _ => rfl
  | step s c _ ih =>
    change (s.journal ++ [c]).length = (s.phases ++ [(Api.Runner.result s.runner c).phase]).length
    rw [List.length_append, List.length_append, ih]
    rfl

/-- The command boundary uses the proved refused-row conservation leaf. -/
theorem jobs_boundary (total : Nat) (b : Api.Built)
    (hb : Api.Author.build (crew total) = .ok b) (s : Run) (c : Command)
    (hs : Basis b s) (hj : Jobs s) (hc : Run.rowReads s c = true) : Jobs (s.step c) := by
  cases hp : (Api.Runner.result s.runner c).phase with
  | refused why => exact jobs_refused s c why (reached_lengths s hs.reached) hp hj
  | bound | preflight | applied | progressed | frontier =>
    exact jobs_step total b s c hb hs hj hc

/-- The command boundary uses the proved refused-row cleanup leaf. -/
theorem cleanup_boundary (total : Nat) (b : Api.Built)
    (hb : Api.Author.build (crew total) = .ok b) (s : Run) (c : Command)
    (hs : Basis b s) (hj : Cleanup s.machine) (hc : Run.rowReads s c = true) :
    Cleanup (s.step c).machine := by
  cases hp : (Api.Runner.result s.runner c).phase with
  | refused why => exact cleanup_refused s c why hp hj
  | bound | preflight | applied | progressed | frontier =>
    exact cleanup_step total b s c hb hs hj hc

/-- Conservation transfers over every funded raw-row script using only its own obligation. -/
theorem jobs_script (total fuel : Nat) (b : Api.Built) (moves : List Move)
    (hb : Api.Author.build (crew total) = .ok b)
    (hf : funded (Scenario.play (openedAt fuel b) moves) = true) :
    Jobs (Scenario.play (openedAt fuel b) moves) := by
  have initial := opened total fuel b hb
  exact (Scenario.keeps_funded (I := fun s => Basis b s ∧ Jobs s)
    (fun s c hc hs => ⟨basis_step b s c hs.1, jobs_boundary total b hb s c hs.1 hs.2 hc.2⟩)
    b "queue-workers" { budget with fuel := fuel } "" moves (fun _ _ => True.intro)
    ⟨initial.toBasis, initial.jobs⟩ hf).2

/-- The rest transfer adds only its custody and wait correspondence obligation. -/
theorem rest_script (total fuel : Nat) (b : Api.Built) (moves : List Move)
    (hb : Api.Author.build (crew total) = .ok b)
    (hf : funded (Scenario.play (openedAt fuel b) moves) = true) :
    Rest (Scenario.play (openedAt fuel b) moves) := by
  have initial := opened total fuel b hb
  exact (Scenario.keeps_funded (I := fun s => Basis b s ∧ Jobs s ∧ Rest s)
    (fun s c hc hs => ⟨basis_step b s c hs.1,
      jobs_boundary total b hb s c hs.1 hs.2.1 hc.2,
      rest_step total b s c hb hs.1 hs.2.1 hs.2.2 hc.2⟩)
    b "queue-workers" { budget with fuel := fuel } "" moves (fun _ _ => True.intro)
    ⟨initial.toBasis, initial.jobs, initial.rest⟩ hf).2.2

/-- Cleanup transfers independently of queue conservation and rest obligations. -/
theorem cleanup_script (total fuel : Nat) (b : Api.Built) (moves : List Move)
    (hb : Api.Author.build (crew total) = .ok b)
    (hf : funded (Scenario.play (openedAt fuel b) moves) = true) :
    Cleanup (Scenario.play (openedAt fuel b) moves).machine := by
  have initial := opened total fuel b hb
  exact (Scenario.keeps_funded (I := fun s => Basis b s ∧ Cleanup s.machine)
    (fun s c hc hs => ⟨basis_step b s c hs.1,
      cleanup_boundary total b hb s c hs.1 hs.2 hc.2⟩)
    b "queue-workers" { budget with fuel := fuel } "" moves (fun _ _ => True.intro)
    ⟨initial.toBasis, initial.cleanup⟩ hf).2

/-- A host script's actual journal satisfies the rest assertion's host-row premise. -/
theorem host_journal (fuel : Nat) (b : Api.Built) (moves : List Move)
    (hh : moves.all Move.hostAct = true) : HostRows (Scenario.play (openedAt fuel b) moves) := by
  unfold HostRows
  rw [Scenario.play_scriptRows, Run.journal_play]
  change ∀ c ∈ Scenario.scriptRows (openedAt fuel b) moves, HostRow c
  exact hostAct_scriptRows (openedAt fuel b) moves hh

/-- Every host-row journal satisfies the accepted terminal-reply profile. -/
theorem host_terminal (s : Run) (host : HostRows s) : QueueWorkers.Original.TerminalReplies s := by
  intro reply member
  change (.submit reply, Api.HostSession.Phase.preflight) ∈ s.journal.zip s.phases at member
  exact host (.submit reply) (List.of_mem_zip member).1

/-- A checked journal supplies the same explicit terminal-reply premise as the public claim. -/
theorem terminal_of_check (s : Run) (checked : QueueWorkers.Original.terminalRepliesCheck s = true) : QueueWorkers.Original.TerminalReplies s := by
  intro reply member
  have selected := List.all_eq_true.mp checked (.submit reply, .preflight) member
  cases completion : reply.completion with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    change (match reply.completion with | .ofExit _ => true | .ofRefGet _ => false) = true at selected
    rw [completion] at selected
    cases selected

/-- The concrete source-path debit bounds imply no repeated actual cleanup entry. -/
theorem cleanup_read (m : NativeMachine) (hc : Cleanup m) : (log m).Nodup := by
  rw [List.nodup_iff_count]
  intro v
  by_cases hv : v ∈ log m
  · obtain ⟨i, hi, rfl⟩ := hc.identities v hv
    exact Nat.le_trans (hc.logs i hi) (Nat.le_trans (hc.releases i hi) (hc.registrations i hi))
  · exact (List.count_eq_zero_of_not_mem hv).symm ▸ Nat.zero_le 1

end Test.Dogfood.Scenario.QueueWorkers.Assertions
