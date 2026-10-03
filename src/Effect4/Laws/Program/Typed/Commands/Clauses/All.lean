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

/-!
# Laws.Program.Typed.Commands.Clauses.All — the evaluator's clauses, assembled

Concept 4 (`step-deliver-preserves`, `step-loop-preserves`): every fiber clause and every store
clause by name, so `M6Ledger.step_deliver` and `step_loop` follow from `deliver_preserves_of_clauses`
and `loop_preserves_of_clauses` (`Commands/Evaluate.lean`) with the walk (`walkKeeps`). Every store
clause is proved (`storeClauses`); the fiber clauses not yet proved are this file's premises,
stated exactly: `closeIter` at the parallel strategy and the generator producer's obligation
`GenProtocol`. Each premise is discharged where its clause lands.

Not established: the premises; `decision_preserves`, `typedState_reachable`.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **Every fiber clause**, from the proved ones and the two open rows. -/
theorem fiberClauses_of (root : ProgramSource) (rootTy : EffTy)
    (closeIter : ∀ o e, FiberClauseKeeps root rootTy (.closeIter .parallel o e))
    (gen : GenProtocol root) :
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
    | parallel => exact closeIter order ex
  | frontier reason p => exact clause_frontier root rootTy reason p
  | guard_ kind => exact clause_guard_ root rootTy kind
  | unguard ex => exact clause_unguard root rootTy ex
  | finishFinalizer ex => exact clause_finishFinalizer root rootTy ex
  | suspend p => exact clause_suspend root rootTy p
  | sync v => exact clause_sync root rootTy v
  | gen p => exact clause_gen_of root rootTy gen p
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

/-- **`deliver` keeps `I`**, from the open clauses. -/
theorem deliver_preserves_of_open (root : ProgramSource) (rootTy : EffTy)
    (closeIter : ∀ o e, FiberClauseKeeps root rootTy (.closeIter .parallel o e))
    (gen : GenProtocol root)
    (id : FiberId) (y : Bool) : StepPreserves root rootTy (.deliver id y) :=
  deliver_preserves_of_clauses root rootTy (fiberClauses_of root rootTy closeIter gen)
    (storeClauses root rootTy) (walkKeeps root rootTy) id y

/-- **`loop` keeps `I`**, from the open clauses. -/
theorem loop_preserves_of_open (root : ProgramSource) (rootTy : EffTy)
    (closeIter : ∀ o e, FiberClauseKeeps root rootTy (.closeIter .parallel o e))
    (gen : GenProtocol root)
    (id : FiberId) (y : Bool) : StepPreserves root rootTy (.loop id y) :=
  LoopPrefix.loop_preserves_of_clauses root rootTy (fiberClauses_of root rootTy closeIter gen)
    (storeClauses root rootTy) (walkKeeps root rootTy) id y

end Effect4.Program.Typed
