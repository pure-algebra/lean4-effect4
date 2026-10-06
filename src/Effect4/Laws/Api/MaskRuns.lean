import Effect4.Laws.Program.MaskRuns
import Effect4.Laws.Run
import Effect4.Api.RunnerBytes

/-!
# Laws.Api.MaskRuns — the saved mask's chain at the session, the runner and the run API

`Laws/Program/MaskRuns.lean` states the lift of the chain `FrameFiber.MaskChain` at the compiled
program's interpreter, and at the entries of `src/Effect4/Api.lean`. This module states it at the
entries above them, each of which returns a machine inside a session:

* **The host session** (`src/Effect4/Api/HostSession.lean`). `start` loads the machine
  (`HostSession.start_maskRuns`). `advance` and `applyReply` apply one decision under the native
  evaluator, or they refuse and change nothing (`advance_maskRuns`, `applyReply_maskRuns`,
  `applyPending_maskRuns`). `bindCall` and `submit` write the ledger alone (`bindCall_machine`,
  and `submit_machine` of `Laws/Api/HostSession.lean`). `inspect` reads the session's machine
  (`inspect_machine`).
* **The runner** (`src/Effect4/Api/Runner.lean`, `src/Effect4/Api/RunnerBytes.lean`). One row is
  one of the session's four transitions (`Runner.step_maskRuns`). A journal is a fold of rows
  (`Runner.replay_maskRuns`), and so is a journal of bytes (`Runner.stepRow_maskRuns`,
  `Runner.replayRows_maskRuns`, with `stepBytes` and `replayBytes`).
* **The run API** (`src/Effect4/Run.lean`). An opened run holds the invariant at the table of
  its root (`Run.open_maskRuns`). Each row and each journal played keeps it (`Run.step_maskRuns`,
  `Run.play_maskRuns`, `Run.open_play_maskRuns`). The drive under a host plays the rows that it
  chose (`Run.driveFrom_maskRuns`, `Run.drive_maskRuns`, by `Run.drive_eq_play`).

No entry owes a premise for the command condition `ClearReady`. The command loop discharges it
(`Machine.maskRuns_stepKeeps`), and an entry's first commands hold no `Cmd.exitDone`. So each
statement here takes one hypothesis, the invariant at the machine that the entry starts from,
and an opened run or a started session has it.

The file is here by the import graph. Its statements read `Effect4.Run` and the run API's laws
(`Laws/Run.lean`, `drive_eq_play`), which are above `Laws/Program`. The claim's pointer
`Program.compiled_mask_chain_runs` keeps its smaller imports.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. Each
  tagged theorem is a step of the proposed registry claim `saved-mask-chain-runs`, whose pointer
  is `Program.compiled_mask_chain_runs`. It names the entry that it covers;
- reach: every built program, row table, journal, budget and host function, at the native
  evaluator. A fiber is live while its `exit` is `none`;
- it does not establish the bracket of a region, a flag or a stack of an exited fiber as a state
  invariant, a cleanup's multiplicity, a delivery, a budget or liveness. It gives no agreement
  with a target and no law of a host. An entry that a later change adds has no statement until
  someone adds its theorem. An invariant is not progress;
- consumers: a law that reads the chain at a journaled run. The first is the bracket's law, then
  the waiting wrapper under a masked caller, Semaphore's protected permit and Pool's `use`.
-/

set_option autoImplicit false

namespace Effect4.Api.HostSession

open Effect4 Effect4.Machine Effect4.Program

/-- **The entry `HostSession.start` keeps the invariant**: a started session holds it at the
table of its root. Each refusal returns no session.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`Runner.load_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem start_maskRuns (program : Api.Program) (table : RowTable) (expectedProfile : String)
    (header : Header) (compileFuel : Nat) (s : Session program table)
    (started : start program table expectedProfile header compileFuel = .ok s) :
    MaskRuns [true] s.machine := by
  unfold start at started
  split at started
  · cases started
  · split at started
    · cases started
    · split at started
      · cases started
      · split at started
        · cases started
        · split at started
          · cases started
          · cases started
            exact Api.load_maskRuns program compileFuel []

/-- A binding writes the ledger alone: the machine is the same. A step of
`Runner.step_maskRuns`. -/
theorem bindCall_machine {program : Api.Program} {table : RowTable} (s : Session program table)
    (call : Call) (token : Nat) : (bindCall s call token).session.machine = s.machine := by
  unfold bindCall
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · rfl

/-- A reading holds the session's machine: `inspect` replays the empty tape at budget 0. So the
invariant at a session is the invariant at its reading. A step of the run API's readings
(`Runner.inspect`, `Run.inspect`). -/
theorem inspect_machine {program : Api.Program} {table : RowTable} (s : Session program table) :
    (inspect s).machine = s.machine := by
  letI := evaluatorFor program table
  unfold inspect
  split
  · rename_i m result
    exact (congrArg ReplayResult.machine result).symm.trans
      (Lift.replayEval_nil_machine (interpOf program table) 0 s.machine)
  · rename_i why m result
    exact (congrArg ReplayResult.machine result).symm.trans
      (Lift.replayEval_nil_machine (interpOf program table) 0 s.machine)
  · rename_i why m result
    exact (congrArg ReplayResult.machine result).symm.trans
      (Lift.replayEval_nil_machine (interpOf program table) 0 s.machine)

/-- **The entry `HostSession.advance` keeps the invariant**: a control is one decision at the
compiled program's interpreter, under the native evaluator, or it is a refusal that changes
nothing. The retirement after it writes the ledger alone.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`Runner.step_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem advance_maskRuns {program : Api.Program} {table : RowTable} (s : Session program table)
    (fuel : Nat) (decision : NativeDecision) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (advance s fuel decision).session.machine := by
  have stepped := steppedBy_maskRuns program fuel table bases s.machine decision kept
  unfold advance
  split
  · exact ⟨bases, List.prefix_refl _, kept⟩
  · split
    · exact ⟨bases, List.prefix_refl _, kept⟩
    · dsimp only
      split
      · exact ⟨bases, List.prefix_refl _, kept⟩
      · exact stepped

/-- **The entry `HostSession.applyReply` keeps the invariant**: an applied reply is the step of
`Program.steppedBy` at its accepted decision, or it is a refusal or a zero budget that changes
nothing.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers are
`applyPending_maskRuns` and `Runner.step_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem applyReply_maskRuns {program : Api.Program} {table : RowTable}
    (s : Session program table) (key : Key) (fuel : Nat) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (applyReply s key fuel).session.machine := by
  cases fuel with
  | zero => exact ⟨bases, List.prefix_refl _, kept⟩
  | succ fuel =>
    rw [applyReply]
    split
    · split
      · exact ⟨bases, List.prefix_refl _, kept⟩
      · rename_i decision accepted
        have stepped :=
          steppedBy_maskRuns program (fuel + 1) table bases s.machine decision kept
        dsimp only
        split
        · exact ⟨bases, List.prefix_refl _, kept⟩
        · split
          · exact stepped
          · exact stepped
    · exact ⟨bases, List.prefix_refl _, kept⟩

/-- **The entry `HostSession.applyPending` keeps the invariant**: it applies the single pending
reply by `applyReply`, or it changes nothing.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is a law that reads
the chain at a session which a holder drives by `applyPending`. -/
@[semantics "scope-lifetime-finalization"]
theorem applyPending_maskRuns {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (applyPending s fuel).session.machine := by
  cases fuel with
  | zero => exact ⟨bases, List.prefix_refl _, kept⟩
  | succ fuel =>
    rw [applyPending]
    split
    · exact applyReply_maskRuns s _ (fuel + 1) bases kept
    · exact ⟨bases, List.prefix_refl _, kept⟩
    · exact ⟨bases, List.prefix_refl _, kept⟩

end Effect4.Api.HostSession

namespace Effect4.Api.Runner

open Effect4 Effect4.Machine Effect4.Program Effect4.Store

/-- **The entry `Runner.load` keeps the invariant**: a loaded runner holds it at the table of
its root.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is a law that reads
the chain at a runner which a holder loads and plays. -/
@[semantics "scope-lifetime-finalization"]
theorem load_maskRuns (program : Api.Program) (table : RowTable) (expectedProfile : String)
    (header : HostSession.Header) (compileFuel stepFuel : Nat) (p : Runner)
    (loaded : load program table expectedProfile header compileFuel stepFuel = .ok p) :
    MaskRuns [true] p.session.machine := by
  unfold load at loaded
  split at loaded
  · cases loaded
  · rename_i session started
    cases loaded
    exact HostSession.start_maskRuns program table expectedProfile header compileFuel session
      started

/-- **The entry `Runner.step` keeps the invariant**: one row is one of the session's four
transitions. A binding and a receipt write the ledger alone. An application and a control are
`HostSession.applyReply` and `HostSession.advance`.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers are
`replay_maskRuns`, `stepRow_maskRuns` and `Run.step_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem step_maskRuns (p : Runner) (c : Command) (bases : List Bool)
    (kept : MaskRuns bases p.session.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (step p c).1.session.machine := by
  cases c with
  | bind call token =>
    refine ⟨bases, List.prefix_refl _, ?_⟩
    show MaskRuns bases (HostSession.bindCall p.session call token).session.machine
    rw [HostSession.bindCall_machine]
    exact kept
  | submit reply =>
    refine ⟨bases, List.prefix_refl _, ?_⟩
    show MaskRuns bases (HostSession.submit p.session reply).session.machine
    rw [HostSession.submit_machine]
    exact kept
  | apply key => exact HostSession.applyReply_maskRuns p.session key p.fuel bases kept
  | control decision => exact HostSession.advance_maskRuns p.session p.fuel decision bases kept

/-- **The entry `Runner.replay` keeps the invariant**: each journal replayed keeps it, at a
table that the first one is a prefix of.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is a law that reads
the chain at a runner which replays a journal. -/
@[semantics "scope-lifetime-finalization"]
theorem replay_maskRuns :
    ∀ (rows : List Command) (p : Runner) (bases : List Bool), MaskRuns bases p.session.machine →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replay p rows).1.session.machine
  | [], _, bases, kept => ⟨bases, List.prefix_refl _, kept⟩
  | c :: rest, p, bases, kept => by
    obtain ⟨bases₁, le₁, kept₁⟩ := step_maskRuns p c bases kept
    obtain ⟨bases₂, le₂, kept₂⟩ := replay_maskRuns rest (step p c).1 bases₁ kept₁
    exact ⟨bases₂, List.IsPrefix.trans le₁ le₂, kept₂⟩

/-- **The entry `Runner.stepRow` keeps the invariant**: a row of bytes is one command played by
`step`, or it is unreadable and changes nothing.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers are
`stepBytes_maskRuns` and `replayRows_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem stepRow_maskRuns (p : Runner) (row : Bytes) (bases : List Bool)
    (kept : MaskRuns bases p.session.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (stepRow p row).1.session.machine := by
  unfold stepRow
  split
  · exact ⟨bases, List.prefix_refl _, kept⟩
  · exact step_maskRuns p _ bases kept

/-- **The entry `Runner.stepBytes` keeps the invariant**: its runner is `stepRow`'s.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is a law that reads
the chain at a holder of bytes. -/
@[semantics "scope-lifetime-finalization"]
theorem stepBytes_maskRuns (p : Runner) (row : Bytes) (bases : List Bool)
    (kept : MaskRuns bases p.session.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (stepBytes p row).1.session.machine :=
  stepRow_maskRuns p row bases kept

/-- **The entry `Runner.replayRows` keeps the invariant**: each journal of bytes replayed keeps
it, at a table that the first one is a prefix of.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`replayBytes_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem replayRows_maskRuns :
    ∀ (rows : List Bytes) (p : Runner) (bases : List Bool), MaskRuns bases p.session.machine →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayRows p rows).1.session.machine
  | [], _, bases, kept => ⟨bases, List.prefix_refl _, kept⟩
  | row :: rest, p, bases, kept => by
    obtain ⟨bases₁, le₁, kept₁⟩ := stepRow_maskRuns p row bases kept
    obtain ⟨bases₂, le₂, kept₂⟩ := replayRows_maskRuns rest (stepRow p row).1 bases₁ kept₁
    exact ⟨bases₂, List.IsPrefix.trans le₁ le₂, kept₂⟩

/-- **The entry `Runner.replayBytes` keeps the invariant**: its runner is `replayRows`'s.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is a law that reads
the chain at a holder of bytes. -/
@[semantics "scope-lifetime-finalization"]
theorem replayBytes_maskRuns (p : Runner) (rows : List Bytes) (bases : List Bool)
    (kept : MaskRuns bases p.session.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayBytes p rows).1.session.machine :=
  replayRows_maskRuns rows p bases kept

end Effect4.Api.Runner

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.Runner (Command)

/-- **The entry `Run.open` keeps the invariant**: an opened run holds it at the table of its
root. `Run.open` loads the machine by `Api.load`.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`open_play_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem open_maskRuns (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    MaskRuns [true] (Run.open b id budget profile).machine :=
  Api.load_maskRuns b.program budget.compileFuel []

/-- **The entry `Run.step` keeps the invariant**: one row played is the runner's step.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`play_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem step_maskRuns (s : Run) (c : Command) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (s.step c).machine :=
  Api.Runner.step_maskRuns s.runner c bases kept

/-- **The entry `Run.play` keeps the invariant**: each journal played keeps it, at a table that
the first one is a prefix of. The rows `Run.answer`, `Run.receive`, `Run.control` and
`Run.controlOnce` play are journals, so this statement covers them.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers are
`open_play_maskRuns` and `driveFrom_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem play_maskRuns (s : Run) (rows : List Command) (bases : List Bool)
    (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (s.play rows).machine :=
  Machine.Lift.foldl_lift basesOrder (fun bases (s : Run) => MaskRuns bases s.machine)
    (fun _ _ _ => True) Run.step (fun bases s c kept _ => step_maskRuns s c bases kept) rows bases s
    kept (Machine.Lift.admitted_true _ _ rows s)

/-- **Each machine that a journal reaches from an opened run holds the invariant**, at a table
that starts with the root's flag. So each of its live fibers holds the chain at its start flag.
It takes no premise on the built program, the journal or the budget. `Run.runPure` and
`Run.runClock` are journals played from an opened run, so this statement covers them.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers read the law at a
journaled run: the bracket's law, then the protected permit and Pool's `use`. -/
@[semantics "scope-lifetime-finalization"]
theorem open_play_maskRuns (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (rows : List Command) :
    ∃ bases, [true] <+: bases ∧
      MaskRuns bases ((Run.open b id budget profile).play rows).machine :=
  play_maskRuns _ rows [true] (open_maskRuns b id budget profile)

/-- **The entry `Run.driveFrom` keeps the invariant**: the drive under a host reaches the run
that its rows reach (`drive_eq_play`), and a journal played keeps the invariant.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumer is
`drive_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem driveFrom_maskRuns {σ : Type} (r : Reactor σ) (rounds : Nat) (s : Run) (st : σ)
    (bases : List Bool) (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveFrom r rounds s st).1.machine := by
  rw [drive_eq_play]
  exact play_maskRuns s _ bases kept

/-- **The entry `Run.drive` keeps the invariant**: its run is `driveFrom`'s. `Run.runWith` is a
drive from an opened run that played its start, so this statement and `open_play_maskRuns`
cover it.

A step of the proposed registry claim `saved-mask-chain-runs`. Its consumers read the law at a
run under a host: the bracket's law, then the protected permit and Pool's `use`. -/
@[semantics "scope-lifetime-finalization"]
theorem drive_maskRuns {σ : Type} (s : Run) (r : Reactor σ) (st : σ) (rounds : Nat)
    (bases : List Bool) (kept : MaskRuns bases s.machine) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases' (s.drive r st rounds).1.machine :=
  driveFrom_maskRuns r rounds s st bases kept

end Effect4.Run
