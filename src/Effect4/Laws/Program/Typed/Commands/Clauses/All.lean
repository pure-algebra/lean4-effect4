import Effect4.Laws.Program.Typed.Commands.Clauses.Answer
import Effect4.Laws.Program.Typed.Commands.Clauses.Park
import Effect4.Laws.Program.Typed.Commands.Clauses.Spawn
import Effect4.Laws.Program.Typed.Commands.Clauses.Command
import Effect4.Laws.Program.Typed.Commands.Clauses.Close
import Effect4.Laws.Program.Typed.Commands.Clauses.Iter
import Effect4.Laws.Program.Typed.Commands.Clauses.Loop
import Effect4.Laws.Program.Typed.Commands.Clauses.Async
import Effect4.Laws.Program.Typed.Commands.Clauses.StoreRef
import Effect4.Laws.Program.Typed.Commands.Clauses.StoreScope
import Effect4.Laws.Program.Typed.Commands.Clauses.StoreDeferred
import Effect4.Laws.Program.Typed.Commands.Clauses.Gen
import Effect4.Laws.Program.Typed.Edits

/-!
# Laws.Program.Typed.Commands.Clauses.All — the evaluator's clauses, assembled

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): every fiber clause and every store
clause by name, so `deliver_preserves` and `step_loop` follow from `deliver_preserves_of_clauses`
and `loop_preserves_of_clauses` (`Commands/Evaluate.lean`) with the walk (`walkKeeps`). Every clause is
proved (`storeClauses`, `fiberClauses`, the generator's protocol `genProtocol`), so
`step_deliver` and `step_loop` hold, and with the other sixteen command facts and the six decision
edits, `decision_preserves` and `typedState_reachable` (`decisionKeeps_of_ledger`,
`reachable_of_ledger`): the M6 ledger is closed here. With M5 (`loadsTyped`), M7a–c follow
(`m7_proved`, through `m7_of_ledger`): on the M7 fragment the frame machine's observation is typed
and its run never halts.

The strongest form is `reachable_typed`: every checked program, with no lawful-signature or
closed-row premise (no proof of M5 or M6 reads either), stays in `J` on every tape whose host
answers are admitted at the ghost token table (`AdmittedTape`); `obs_typed` carries it to the frame
machine. Scope-handle validity follows from it and capability membership (`exitHandles_valid`,
`exitHandles_valid`), which closes the M7 ledger.

Not established: progress (`J` is an invariant, not a liveness result); executable admission of host
answers (`AdmittedTape` reads `Θ`, which no host sees: `admit_sound`, rows 97–99); a table-aware
frame machine (DI-57); anything about the OCaml engine or a TypeScript run.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-! ## The open clauses, as ledger goals

`deliver_preserves` and `step_loop` follow from the clauses (`deliver_preserves`,
`loop_preserves` below). The two clauses proved last are the ledger's goals here, so the proof graph
names them: the parallel close (`Clauses/Close.lean`) and the generator's protocol
(`Clauses/Gen.lean`). -/

/-- **Every fiber clause.** -/
theorem fiberClauses (root : ProgramSource) (rootTy : EffTy) :
    ∀ op, FiberClauseKeeps root rootTy op := by
  intro op
  cases op with
  | fork child options site => exact clause_fork root rootTy child options site
  | forkIn child options scope site => exact clause_forkIn root rootTy child options scope site
  | forkScoped child options site => exact clause_forkScoped root rootTy child options site
  | await target mode => exact clause_await root rootTy target mode
  | awaitAll targets => exact clause_awaitAll root rootTy targets
  | awaitAllFailFast targets => exact clause_awaitAllFailFast root rootTy targets
  | yieldNow priority => exact clause_yieldNow root rootTy priority
  | async register request => exact clause_async root rootTy register request
  | interrupt target => exact clause_interrupt root rootTy target
  | interruptAs target who => exact clause_interruptAs root rootTy target who
  | interruptScoped target => exact clause_interruptScoped root rootTy target
  | interruptAll targets who => exact clause_interruptAll root rootTy targets who
  | mask flag body => exact clause_mask root rootTy flag body
  | closeScope scope ex => exact clause_closeScope root rootTy scope ex
  | «scoped» body => exact clause_scoped root rootTy body
  | scopeExit prev scope ex => exact clause_scopeExit root rootTy prev scope ex
  | foreignRelease c ex => exact clause_foreignRelease root rootTy c ex
  | raceAll entrants site => exact clause_raceAll root rootTy entrants site
  | raceRegister race => exact clause_raceRegister root rootTy race
  | cancelRace race => exact clause_cancelRace root rootTy race
  | getId => exact clause_getId root rootTy
  | getInterruptible => exact clause_getInterruptible root rootTy
  | getContext => exact clause_getContext root rootTy
  | setContext ctx => exact clause_setContext root rootTy ctx
  | snapshotChildren => exact clause_snapshotChildren root rootTy
  | awaitNewChildren snapshot => exact clause_awaitNewChildren root rootTy snapshot
  | runIn target scope => exact clause_runIn root rootTy target scope
  | dropObservers token => exact clause_dropObservers root rootTy token
  | refuse cause => exact clause_refuse root rootTy cause
  | ambientScope => exact clause_ambientScope root rootTy
  | closeWalk strategy order ex => exact clause_closeWalk root rootTy strategy order ex
  | closeIter strategy order ex =>
    cases strategy with
    | sequential => exact clause_closeIter_sequential root rootTy order ex
    | parallel => exact clause_closeIter_parallel root rootTy order ex
  | frontier reason p => exact clause_frontier root rootTy reason p
  | guard_ kind => exact clause_guard_ root rootTy kind
  | unguard ex => exact clause_unguard root rootTy ex
  | finishFinalizer ex => exact clause_finishFinalizer root rootTy ex
  | suspend p => exact clause_suspend root rootTy p
  | sync v => exact clause_sync root rootTy v
  | gen p => exact clause_gen_of root rootTy (genProtocol root) p
  | loop p cursor => exact clause_loop root rootTy p cursor
  | construction => exact clause_construction root rootTy

/-- **Every store clause.** -/
theorem storeClauses (root : ProgramSource) (rootTy : EffTy) :
    ∀ op, StoreClauseKeeps root rootTy op := by
  intro op
  cases op with
  | refMake initial => exact clause_refMake root rootTy initial
  -- the twelve heap rows: one clause from their table (`SyncOp.refKernel`)
  | refGet _ | refSet _ _ | refGetAndSet _ _ | refSetAndGet _ _
  | refUpdate _ _ _ | refGetAndUpdate _ _ _ | refUpdateAndGet _ _ _
  | refUpdateSome _ _ _ | refGetAndUpdateSome _ _ _ | refUpdateSomeAndGet _ _ _
  | refModify _ _ _ | refModifySome _ _ _ => exact clause_kernel root rootTy rfl
  | deferredMake => exact clause_deferredMake root rootTy
  | deferredIsDone key => exact clause_deferredIsDone root rootTy key
  | deferredPoll key => exact clause_deferredPoll root rootTy key
  | deferredCompleteWith key c => exact clause_deferredCompleteWith root rootTy key c
  | deferredInterruptWith key c => exact clause_deferredInterruptWith root rootTy key c
  | deferredAwaitCleanup key w t => exact clause_deferredAwaitCleanup root rootTy key w t
  | clockNow => exact clause_clockNow root rootTy
  | sleepCancel w t => exact clause_sleepCancel root rootTy w t
  | scopeMake s => exact clause_scopeMake root rootTy s
  | scopeAdd sc f => exact clause_scopeAdd root rootTy sc f
  | scopeRemove sc k => exact clause_scopeRemove root rootTy sc k
  | scopeIsClosed sc => exact clause_scopeIsClosed root rootTy sc
  | scopeFork p s => exact clause_scopeFork root rootTy p s
  | memoFork p => exact clause_memoFork root rootTy p
  | memoGet l m => exact clause_memoGet root rootTy l m
  | memoBuild l m => exact clause_memoBuild root rootTy l m
  | memoComplete l m e => exact clause_memoComplete root rootTy l m e
  | memoRelease l m => exact clause_memoRelease root rootTy l m

/-- **`deliver` keeps `I`** (`deliver_preserves`): every clause, the walk. -/
theorem deliver_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (y : Bool) :
    StepPreserves root rootTy (.deliver id y) :=
  deliver_preserves_of_clauses root rootTy (fiberClauses root rootTy) (storeClauses root rootTy)
    (walkKeeps root rootTy) id y

/-- **`loop` keeps `I`** (`loop_preserves`): every clause, the walk. -/
theorem loop_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (y : Bool) :
    StepPreserves root rootTy (.loop id y) :=
  LoopPrefix.loop_preserves_of_clauses root rootTy (fiberClauses root rootTy)
    (storeClauses root rootTy) (walkKeeps root rootTy) id y

/-- **Every command keeps `I`**: the eighteen command facts, one per command. -/
theorem steps_preserve (root : ProgramSource) (rootTy : EffTy) :
    ∀ command, StepPreserves root rootTy command
  | .evaluate id => evaluate_preserves root rootTy id
  | .loop id y => loop_preserves root rootTy id y
  | .deliver id y => deliver_preserves root rootTy id y
  | .finish id ex => finish_preserves root rootTy id ex
  | .resume id token code => resume_preserves root rootTy id token code
  | .launch race => launch_preserves root rootTy race
  | .enrollRace race child => enrollRace_preserves root rootTy race child
  | .registrationDone race y => registrationDone_preserves root rootTy race y
  | .interruptTarget target who extra => interruptTarget_preserves root rootTy target who extra
  | .afterInterrupt host y kind => afterInterrupt_preserves root rootTy host y kind
  | .raceCancel race host y remaining visited =>
    raceCancel_preserves root rootTy race host y remaining visited
  | .trackChild parent child => trackChild_preserves root rootTy parent child
  | .observe fiber ex observer => observe_preserves root rootTy fiber ex observer
  | .exitDone fiber => exitDone_preserves root rootTy fiber
  | .closeParAwait host y fibers => closeParAwait_preserves root rootTy host y fibers
  | .link mode scope target who extra => link_preserves root rootTy mode scope target who extra
  | .drainDue => drainDue_preserves root rootTy
  | .wake list phase => wake_preserves root rootTy list phase

/-- **A tape decision keeps `J`** (`decision_preserves`): the command facts and the six
edits through the decision lift (`decisionKeeps_of_ledger`). -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    DecisionKeeps root rootTy fuel d :=
  decisionKeeps_of_ledger root rootTy fuel d (steps_preserve root rootTy)
    ⟨edit_drain root rootTy, edit_yield root rootTy, edit_interrupt root rootTy,
      edit_clockNone root rootTy, edit_clockSome root rootTy, edit_answer root rootTy⟩

/-- **Every reachable machine is typed** (`typedState_reachable`): the load (M5,
`loadsTyped`) and every decision (`reachable_of_ledger`). -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ReachableTyped root rootTy fuel m :=
  reachable_of_ledger root rootTy fuel (loadsTyped root rootTy fuel fuel)
    (decision_preserves root rootTy fuel) m

/-- **M7a–c** (decisions row 138): on the M7 fragment (the empty host table, a checked closed
source, answer-free tapes), the frame machine's observation is typed and its run never halts:
`m7_of_ledger` at the proved load (`loadsTyped`) and decisions (`decision_preserves`). The frame
machine only: not the OCaml engine, not a TypeScript run. -/
theorem m7_proved (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision) :
    M7Exits root rootTy fuel tape ∧ M7Stores root rootTy fuel tape ∧ M7NoHalt root rootTy fuel tape :=
  m7_of_ledger root rootTy fuel tape (loadsTyped root rootTy fuel fuel)
    (decision_preserves root rootTy fuel)

/-- **Every admitted replay of a checked program is typed**: the reference replay of a tape whose
host answers are admitted (`AdmittedTape`, the ghost admission at `Θ`) ends in `J`, for every
checked program, its requirement row open or closed and its signature lawful or not. M5 in its
premise-free form (`load_typed`) and M6 (`decision_preserves`) through `admitted_typed`. Concept 4
(`typed-state-reachable`); it reduces the host lane's typing half (T4) to executable admission
(`admit_sound`, decisions rows 97–99). -/
theorem reachable_typed (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy)
    (tape : List Api.Decision) (admitted : AdmittedTape root rootTy fuel tape) :
    ∃ w, MachineTyped root rootTy w (replayR root.program fuel tape).machine :=
  admitted_typed root rootTy fuel (load_typed root rootTy fuel fuel checked)
    (decision_preserves root rootTy fuel) tape admitted

/-- **The frame machine's observation on every admitted tape is typed** and its run has not
halted: `reachable_typed` across `run_eq_ref`'s relation (`obsTyped_admitted`). M7a–c without the
fragment's lawful, closed-row and answer-free premises; the frame machine at its empty row table
only. -/
theorem obs_typed (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (tape : List Api.Decision)
    (checked : Program.typeOfProgram root.sig.signature root.program = some rootTy)
    (admitted : AdmittedTape root rootTy fuel tape) :
    ∃ w, MachineTyped root rootTy w (replayR root.program fuel tape).machine ∧
      ExitsFit rootTy w (obs (Api.replay root.program fuel tape).machine) ∧
      StoresFit root w (obs (Api.replay root.program fuel tape).machine).stores ∧
      (Api.replay root.program fuel tape).machine.stuck = none :=
  obsTyped_admitted root rootTy fuel tape (load_typed root rootTy fuel fuel checked)
    (decision_preserves root rootTy fuel) admitted

/-- **Recorded successes name only live handles** (`exitHandles_valid`, organization M4, row
139): on every reachable machine of a checked program, a fiber's successful exit value is valid in
the machine's stores. `J` holds there (`reachable_typed`, no closed-row premise needed), the exit
fits its fiber's declared type, and a member of any type is valid in a typed store
(`fits_validIn`, the F-WF repair). The exit connector's validity premise. -/
theorem exitHandles_valid (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ExitHandlesValid root rootTy fuel m := by
  rintro _ checked ⟨tape, free, rfl⟩ f hf v hx
  obtain ⟨w, typed⟩ := reachable_typed root rootTy fuel checked tape
    (admittedTape_of_noHostAnswer root rootTy fuel tape free)
  have store := storeTyped_of_typedState typed
  obtain ⟨⟨valid, ok, _, _, _, _⟩, _, _⟩ := typed
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid.fibers f.id).mpr (List.mem_map_of_mem hf))
  have hfit := (fitsExit_success_iff w ty v).mp ((ok.c0 f hf).c3 _ hx ty declared).1
  rw [← valid.state]
  exact fits_validIn store hfit

end Effect4.Program.Typed
