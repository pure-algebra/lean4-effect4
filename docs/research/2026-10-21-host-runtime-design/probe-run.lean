import Effect4.Laws.Api.Live
import Effect4.Laws.Api.HostDrive
import Test.Dogfood.Scenario.Todo.CachedProgram
import Test.Dogfood.Scenario.Todo.Data

/-! Probe: a run is data. The deployment's run is the journal played from an open of the admitted
object; the session and the verdicts are folds of it. Every call a journal binds is the machine's
own call at that point, so a replay checks what a deployment sent its host. Each `#guard` is a
finite evaluation on the to-do; each theorem is proved. -/

set_option autoImplicit false
namespace Probe.Run
open Effect4 Effect4.Program Effect4.Machine
open Effect4.Api.Runner (Command)
open Test.Dogfood.Scenario.Todo (repository Repo)

/-! ## 1. A driven run is reached, and replays from its journal alone -/

/-- **A driven run is a reached run**: the driver only opens and plays (`drive_eq_play`).
Placement: concept `host-session-protocol`; a step of `runWith_replays`; consumer the
deployment's restore (README §4). -/
theorem runWith_reached {σ : Type} (b : Api.Built) (r : Run.Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) : Run.Reached (Run.runWith b r st id budget rounds).1 := by
  show Run.Reached (Run.driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1
  rw [Run.drive_eq_play]
  exact Run.Reached.play _ _ (Run.Reached.play _ _ (Run.Reached.open b id budget))

/-- **A driven run replays from its journal, with no host**: `journal_replays` at the driver.
Placement: concept `host-session-protocol`; R13's top node `journal_replays`, read at the run a
deployment makes; consumer: the native journal's replay (README §6). -/
theorem runWith_replays {σ : Type} (b : Api.Built) (r : Run.Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) :
    (Run.open b id budget).play (Run.runWith b r st id budget rounds).1.journal =
      (Run.runWith b r st id budget rounds).1 := by
  have h := Run.journal_replays _ (runWith_reached b r st id budget rounds)
  have hopen : Run.openedOf (Run.runWith b r st id budget rounds).1 = Run.open b id budget := by
    show Run.openedOf (Run.driveFrom r rounds ((Run.open b id budget).play Rows.start) st).1 = _
    rw [Run.drive_eq_play, ← Run.play_append, Run.openedOf_play_open]
  exact (congrArg (fun s => s.play (Run.runWith b r st id budget rounds).1.journal) hopen).symm.trans h

/-- **Drive a live run with a host**: the driven run is reached by playing the rows the host chose
(`drive_eq_play`), so it stays a `Live`, and `LiveRecord.save` and `restore_save` read it.
Proposed for `src/Effect4/Run/Live.lean`, as the native engine's driving root. -/
def liveDrive {σ : Type} (l : Live) (r : Run.Reactor σ) (st : σ) (rounds : Nat := 64) : Live × σ :=
  (⟨(Run.driveFrom r rounds l.run st).1, by
    obtain ⟨b, id, budget, binding, commands, h⟩ := l.opened
    refine ⟨b, id, budget, binding, commands ++ (Run.driveFrom r rounds l.run st).2.1, ?_⟩
    rw [Run.play_append, h]
    exact (Run.drive_eq_play r rounds l.run st).symm⟩, (Run.driveFrom r rounds l.run st).2.2)

/-- The live drive is the run's drive. By definition. -/
theorem liveDrive_run {σ : Type} (l : Live) (r : Run.Reactor σ) (st : σ) (rounds : Nat) :
    (liveDrive l r st rounds).1.run = (Run.driveFrom r rounds l.run st).1 := rfl

/-! ## 2. A bound call is the machine's call -/

/-- **A `bound` verdict restates the machine** (inversion of `bindCall`): the call names the
session, the table, and the request the machine holds at that fiber and token.
Placement: concept `host-session-protocol`; a step of the proposed claim
`replay-validates-calls`; consumer `journal_bound_call`. -/
theorem bindCall_bound {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (call : Api.HostSession.Call) (token : Nat)
    (h : (Api.HostSession.bindCall s call token).phase = .bound) :
    call.session = s.header.session ∧ call.table = app.rows ∧
      requestOf s.machine call.fiber token = some (call.op, call.request) := by
  unfold Api.HostSession.bindCall at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hs
      split at h
      · cases h
      · rename_i ht
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i hr
              exact ⟨Decidable.of_not_not hs, Decidable.of_not_not ht, Decidable.of_not_not hr⟩

/-- **Every call a journal binds is the machine's call at that point.** Take a row of a live run's
journal whose verdict is `bound`. At the run after the rows before it (`Live.upTo`), the machine
holds exactly that call's row and request, and the call names the run and its table. So a replay of
a journal checks every request that its run sent a host.
Placement: concept `host-session-protocol`, role inversion; question: the proposed claim
`replay-validates-calls`, an open part of R6 ("the host as a relation between the machine's calls
and its answers", the calls' half); consumer: the deployment's per-run check (README §6). Reach:
every `Live` and every row whose verdict is `bound`. It does not establish that a native driver
recorded what it sent, the answers' half (`replay_at_call_instance` has it), or host progress. -/
theorem journal_bound_call (l : Live) (i : Nat) (call : Api.HostSession.Call) (token : Nat)
    (h : (Run.rows l.run)[i]? = some (.bind call token, .bound)) :
    requestOf (l.upTo i).run.machine call.fiber token = some (call.op, call.request) ∧
      call.session = (l.upTo i).run.id ∧ call.table = (l.upTo i).run.built.table := by
  have hphase := Live.rows_upTo l i _ _ h
  obtain ⟨hs, ht, hr⟩ := bindCall_bound _ call token hphase
  exact ⟨hr, hs, ht⟩

/-! ## 3. The to-do's run, read as data -/

/-- The to-do's service block, admitted. -/
def todoBuilt : Option Api.Built :=
  Test.Dogfood.Scenario.Todo.Cached.built? Test.Dogfood.Scenario.Todo.application

/-- One request's run: the entry `add` at "milk", over the reference repository. -/
def addRun : Option (Run × Repo) :=
  ((Test.Dogfood.Scenario.Todo.application.entry? "add").map fun e =>
    Test.Dogfood.Scenario.Todo.application.moduleOf e [Authoring.str "milk"]).bind fun m =>
      (Api.Author.build m).toOption.map fun b => Run.runWith b repository (1, [])

-- finite evaluation: the run finished; its journal is the start, the three rows of the one answer
-- (bind, submit, apply), and the last flush; the host's next id moved from 1 to 2
#guard addRun.map (fun (s, st) => (s.exit.isSome, s.journal.length, st.1)) = some (true, 5, 2)
#guard addRun.map (fun (s, _) => s.journal.map fun
  | .control _ => "control" | .bind _ _ => "bind" | .submit _ => "submit" | .apply _ => "apply") =
  some ["control", "bind", "submit", "apply", "control"]
-- finite evaluation: the session and the verdicts are the journal's fold (`runWith_replays`)
#guard addRun.map (fun (s, _) =>
  (Run.open s.built s.id s.budget s.profile).play s.journal |>.observe) = addRun.map (·.1.observe)
-- finite evaluation: every bind row of the journal is bound, so `journal_bound_call` reads each
#guard addRun.map (fun (s, _) => (Run.rows s).all fun (c, ph) => match c with
  | .bind _ _ => decide (ph = .bound)
  | _ => true) = some true
-- finite evaluation (the binding): no session transition reads the header's binding; two opens
-- that differ only there play the journal to equal observations and verdicts
#guard addRun.map (fun (s, _) =>
  let a := (Run.open s.built s.id s.budget "keyed-v3").play s.journal
  let z := (Run.open s.built s.id s.budget "another-host").play s.journal
  decide (a.observe = z.observe) && decide (a.phases = z.phases)) = some true
-- finite evaluation: opening, starting and driving a `Live` reaches the driver's run
#guard (((Test.Dogfood.Scenario.Todo.application.entry? "add").map fun e =>
    Test.Dogfood.Scenario.Todo.application.moduleOf e [Authoring.str "milk"]).bind fun m =>
      (Api.Author.build m).toOption.map fun b =>
        let l := ((Live.open b "run").feed Run.Event.start).1
        decide ((liveDrive l repository (1, [])).1.run.observe = (Run.runWith b repository (1, [])).1.observe)) =
  some true
-- control: a journal replayed under another run name refuses its bind rows (`staleCall` is not
-- the reason: the name is checked first, as `Refusal.session`)
#guard addRun.map (fun (s, _) =>
  ((Run.open s.built "other" s.budget s.profile).play s.journal).phases.any fun ph =>
    decide (ph = .refused .session)) = some true

end Probe.Run
