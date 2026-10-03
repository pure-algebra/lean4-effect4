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
clause by name, so `M6Ledger.step_deliver` and `step_loop` follow from `deliver_preserves_of_clauses`
and `loop_preserves_of_clauses` (`Commands/Evaluate.lean`) with the walk (`walkKeeps`). Every clause is
proved (`storeClauses`, `fiberClauses`, the generator's protocol `genProtocol`), so
`step_deliver` and `step_loop` hold, and with the other sixteen command facts and the six decision
edits, `decision_preserves` and `typedState_reachable` (`decisionKeeps_of_ledger`,
`reachable_of_ledger`): the M6 ledger is closed here. With M5 (`loadsTyped`), M7a–c follow
(`m7_proved`, through `m7_of_ledger`): on the M7 fragment the frame machine's observation is typed
and its run never halts.

Not established: progress (`J` is an invariant, not a liveness result); host answers (the tapes
carry none, `NoHostAnswer`); scope-handle validity (`M7.exitHandles_valid`, stated without the
closed requirement row); anything about the OCaml engine or a TypeScript run.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-! ## The open clauses, as ledger goals

`M6Ledger.step_deliver` and `step_loop` follow from the clauses (`deliver_preserves`,
`loop_preserves` below). The two clauses proved last are the ledger's goals here, so the proof graph
names them: the parallel close (`Clauses/Close.lean`) and the generator's protocol
(`Clauses/Gen.lean`). -/

namespace M6Clauses

/-- **`closeIter`, parallel** (`FiberAction.closePar`, `Machine/Fibers.lean:1502-1507`; rc.112
`internal/effect.ts:3819-3826`): every finalizer forked as an immediate daemon at
`⟨unknown, never⟩`, their runs queued, and the await over them (`closeParAwait`) queued with its
delivery (`CommandDeliveryOk`: the children's columns, the `closeParDone` protocol, the host's
saved answer frame). A step of `M6Ledger.step_deliver` and `step_loop`. -/
theorem closeIter_parallel (root : ProgramSource) (rootTy : EffTy) (order : List FinName)
    (ex : ExitV) :
    ProofGraph.Obligation (FiberClauseKeeps root rootTy (.closeIter .parallel order ex)) := ⟨⟩

/-- **The generator producer's obligation** (`GenProtocol`, decisions row 190): the coinduction
over typed generator positions. A step of `M6Ledger.step_deliver` and `step_loop`. -/
theorem gen_protocol (root : ProgramSource) : ProofGraph.Obligation (GenProtocol root) := ⟨⟩

end M6Clauses

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
  | refGet cell => exact clause_refGet root rootTy cell
  | refSet cell v => exact clause_refSet root rootTy cell v
  | refGetAndSet cell v => exact clause_refGetAndSet root rootTy cell v
  | refSetAndGet cell v => exact clause_refSetAndGet root rootTy cell v
  | refUpdate cell f => exact clause_refUpdate root rootTy cell f
  | refGetAndUpdate cell f => exact clause_refGetAndUpdate root rootTy cell f
  | refUpdateAndGet cell f => exact clause_refUpdateAndGet root rootTy cell f
  | refUpdateSome cell f => exact clause_refUpdateSome root rootTy cell f
  | refGetAndUpdateSome cell f => exact clause_refGetAndUpdateSome root rootTy cell f
  | refUpdateSomeAndGet cell f => exact clause_refUpdateSomeAndGet root rootTy cell f
  | refModify cell f => exact clause_refModify root rootTy cell f
  | refModifySome cell f => exact clause_refModifySome root rootTy cell f
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

/-- **`deliver` keeps `I`** (`M6Ledger.step_deliver`): every clause, the walk. -/
theorem deliver_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (y : Bool) :
    StepPreserves root rootTy (.deliver id y) :=
  deliver_preserves_of_clauses root rootTy (fiberClauses root rootTy) (storeClauses root rootTy)
    (walkKeeps root rootTy) id y

/-- **`loop` keeps `I`** (`M6Ledger.step_loop`): every clause, the walk. -/
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

/-- **A tape decision keeps `J`** (`M6Ledger.decision_preserves`): the command facts and the six
edits through the decision lift (`decisionKeeps_of_ledger`). -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    DecisionKeeps root rootTy fuel d :=
  decisionKeeps_of_ledger root rootTy fuel d (steps_preserve root rootTy)
    ⟨edit_drain root rootTy, edit_yield root rootTy, edit_interrupt root rootTy,
      edit_clockNone root rootTy, edit_clockSome root rootTy, edit_answer root rootTy⟩

/-- **Every reachable machine is typed** (`M6Ledger.typedState_reachable`): the load (M5,
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

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Clauses.closeIter_parallel :=
  @Effect4.Program.Typed.clause_closeIter_parallel
#obligation_proved Effect4.Program.Typed.M6Clauses.gen_protocol := @Effect4.Program.Typed.genProtocol
#typed_state_obligations Effect4.Program.Typed.M6Clauses ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])

#obligation_proved Effect4.Program.Typed.M6Ledger.step_deliver := @Effect4.Program.Typed.deliver_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_loop := @Effect4.Program.Typed.loop_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.decision_preserves :=
  @Effect4.Program.Typed.decision_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.typedState_reachable :=
  @Effect4.Program.Typed.typedState_reachable
-- `M6Ledger`'s report: every goal proved.
#typed_state_obligations Effect4.Program.Typed.M6Ledger ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])

#obligation_proved Effect4.Program.Typed.M7.exits_typed :=
  fun root rootTy fuel tape => (Effect4.Program.Typed.m7_proved root rootTy fuel tape).1
#obligation_proved Effect4.Program.Typed.M7.stores_typed :=
  fun root rootTy fuel tape => (Effect4.Program.Typed.m7_proved root rootTy fuel tape).2.1
#obligation_proved Effect4.Program.Typed.M7.never_halts :=
  fun root rootTy fuel tape => (Effect4.Program.Typed.m7_proved root rootTy fuel tape).2.2
-- `M7`'s report: a–c proved; scope-handle validity (`exitHandles_valid`) open.
#typed_state_obligations Effect4.Program.Typed.M7 ceiling 1
  using aesop (rule_sets := [Effect4.TypedState])
