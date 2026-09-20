import Effect4.Laws.Program.Typed.Vocabulary

/-!
# Typed/Sources — the typing source of every value-holding position

The one hand-written input of the typed-state invariant
(`docs/research/2026-09-18-position-census-design.md` §2B). `#position_census` derives the
positions from the types reachable from `RState`, `RCmd`, `RInterp` and `RIter`
(`Test/Audit/PositionCensus.lean`); this table says, for each, where its type comes from and
what the invariant states there (`Typed/Vocabulary.lean`). The totality gate refuses a
position without a row and a row without a position, so adding a field to any state structure
fails the build until it is sourced here. Edge rows name a field that reaches a structure: the
expectation a child is typed at (`nested`), a predicate over the whole field (`custom`), a
subtree that is the journal, a subtree that is named debt. The gate reads this list as an
expression (`Laws/Auto/TypedSources.lean`), so it stays plain data.
-/

namespace Effect4.Program.Typed

/-- The reference state, the command residue and the step result. -/
def stateSources : List Row := [
  -- edge rows: the expectation a child is typed at, a predicate over a whole field, a subtree
  -- that is the journal, a subtree that is named debt
  ("Effect4.Machine.RunFiber.frame", .nested (.fiber "x.id")),
  ("Effect4.Program.Sched.RSaved.stack", .custom "StackOk"),
  ("Effect4.Machine.RunFiber.pending", .custom "PendingOk"),
  ("Effect4.Machine.RunFiber.context", .custom "ServiceOk"),
  ("Effect4.Machine.Capture.ctx", .custom "ServiceOk"),
  ("Effect4.Machine.RunMachine.races", .custom "RaceOk"),
  ("Effect4.Machine.RunMachine.trace", .journal),
  ("Effect4.Machine.Stores.externals", .refused "external rows are the table-aware slice (DI-57); the reference parks them forever"),
  -- the fiber's saved frame: the residual program at the fiber's type, the stack as one typed
  -- context, the interrupt cause admitted by every column
  ("Effect4.Program.Sched.RSaved.current", .program .inherited),
  ("Effect4.Program.Sched.ScopeFrame.resume.next", .custom "StackOk"),
  ("Effect4.Program.Sched.ScopeFrame.answer.next", .custom "StackOk"),
  ("Effect4.Program.Sched.ScopeFrame.loop.cursor", .custom "StackOk"),
  ("Effect4.Program.Sched.RSaved.interruptedCause", .custom "InterruptOnly"),
  -- Captured continuation names are a recursive carrier, covered by the enclosing
  -- stack/pending predicate. They were absent from the original census.
  ("Effect4.Program.Sched.ScopeFrame.asyncFinalizer.name", .custom "StackOk"),
  ("Effect4.Program.Sched.ScopeFrame.iter.generator", .custom "StackOk"),
  ("Effect4.Program.Sched.ScopeFrame.loop.loop", .custom "StackOk"),
  ("Effect4.Machine.Resume.continueWith.name", .custom "PendingOk"),
  -- the fiber record
  ("Effect4.Machine.Pending.collected", .custom "PendingOk"),
  ("Effect4.Machine.RunFiber.finalizing", .exit (.fiber "x.id")),
  ("Effect4.Machine.RunFiber.exit", .exit (.fiber "x.id")),
  ("Effect4.Machine.Task.resume.answer", .custom "ResumeOk"),
  ("Effect4.Machine.Env.Service.value", .custom "ServiceOk"),
  -- races: one predicate over the record, at the race's type
  ("Effect4.Supervision.RaceAllState.failures", .custom "RaceOk"),
  ("Effect4.Supervision.RaceAllState.winner", .custom "RaceOk"),
  ("Effect4.Supervision.RaceAllState.accepted", .custom "RaceOk"),
  ("Effect4.Supervision.WaitState.result", .custom "RaceOk"),
  ("Effect4.Machine.Race.programs", .custom "RaceOk"),
  -- the store's columns
  ("Effect4.Machine.Stores.refs", .column "HeapNat"),
  ("Effect4.Machine.DeferredCell.completion", .column "PromiseTable"),
  ("Effect4.Machine.Owed.code", .column "PromiseTable"),
  ("Effect4.Machine.MemoEntry.effect", .column "PromiseTable"),
  ("Effect4.Machine.Completion.ofExit.exit", .column "PromiseTable"),
  ("Effect4.Machine.Capture.env", .custom "CaptureOk"),
  ("Effect4.ScopeState.closed.exit",
    .refused "DI-94 fixes the release type at Exit<unknown, unknown>; connecting stored scope exits to the invariant remains open"),
  -- the journal
  ("Effect4.Machine.RunEvent.finalizerProgram.finalizer", .journal),
  ("Effect4.Machine.RunEvent.resumedWith.answer", .journal),
  ("Effect4.Machine.RunEvent.finalizerProgram.exit", .journal),
  ("Effect4.Machine.RunEvent.raceSettled.exit", .journal),
  ("Effect4.Machine.RunEvent.callback.exit", .journal),
  ("Effect4.Machine.RunEvent.exited.exit", .journal),
  -- the command residue
  ("Effect4.Machine.Cmd.finish.exit", .exit (.fiber "fiber")),
  ("Effect4.Machine.Cmd.resume.answer", .custom "ResumeOk"),
  ("Effect4.Machine.Cmd.observe.exit", .exit (.fiber "fiber")),
  -- the step result
  ("Effect4.Machine.Outcome.finished.exit", .exit .inherited)
]

/-- The interpreter's code- and value-valued hooks: each typed at what its consumer installs
it as. The consumer is the definition of the shared machine or the reference evaluator that
calls it; `none` is a hook the reference never calls (`RSTATE-FB-EVALUATOR-FIELD`). -/
def hookSources : List Row := [
  ("Effect4.PrimInterp.contA", .hook none),
  ("Effect4.PrimInterp.contE", .hook none),
  ("Effect4.PrimInterp.syncValue", .hook none),
  ("Effect4.PrimInterp.suspendBody", .hook (some "Effect4.Program.Sched.bodyR")),
  ("Effect4.PrimInterp.finalizerExit", .hook (some "Effect4.Machine.exitFiber")),
  ("Effect4.PrimInterp.reifyExit", .hook (some "Effect4.Machine.fireObserver")),
  ("Effect4.PrimInterp.iterNext", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.IterStep.done.value", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.IterStep.halt.cause", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.IterStep.resume.continueAs", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.IterStep.resume.next", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.LoopNext.continue.cursor", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.LoopNext.continue.body", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.LoopNext.finish.code", .hook (some "Effect4.Program.Sched.popR")),
  ("Effect4.PrimInterp.cancelThenFail", .hook (some "Effect4.Machine.settle")),
  ("Effect4.Machine.RunInterp.parkOf", .hook none),
  ("Effect4.Machine.RunInterp.parkCode", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.interruptCode", .hook (some "Effect4.Machine.exitFiber")),
  ("Effect4.Machine.RunInterp.interruptAsCode", .hook (some "Effect4.Machine.exitFiber")),
  ("Effect4.Machine.RunInterp.interruptAllCode", .hook (some "Effect4.Machine.exitFiber")),
  ("Effect4.Machine.WithFiberAction.fork.program", .hook none),
  ("Effect4.Machine.WithFiberAction.forkIn.program", .hook none),
  ("Effect4.Machine.WithFiberAction.forkScoped.program", .hook none),
  ("Effect4.Machine.WithFiberAction.raceAll.entrants", .hook none),
  ("Effect4.Machine.WithFiberAction.setInterruptible.body", .hook none),
  ("Effect4.Machine.WithFiberAction.closeScope.exit", .hook none),
  ("Effect4.Machine.WithFiberAction.closePar.finalizers", .hook none),
  ("Effect4.Machine.WithFiberAction.refuse.cause", .hook none),
  ("Effect4.Machine.RunInterp.syncState", .hook none),
  ("Effect4.Machine.RunInterp.registerAsync", .hook (some "Effect4.Program.Sched.evaluateFiberR")),
  ("Effect4.Machine.RunInterp.cancelName", .hook (some "Effect4.Machine.exitFiber")),
  ("Effect4.Machine.RunInterp.abortName", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.parkCancelName", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.raceCancelName", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.restoreName", .hook (some "Effect4.Machine.fireObserver")),
  ("Effect4.Machine.RunInterp.mergeName", .hook (some "Effect4.Machine.fireObserver")),
  ("Effect4.Machine.RunInterp.closeDoneName", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.answerCode", .hook (some "Effect4.Machine.replayEval")),
  ("Effect4.Machine.RunInterp.raceSettle", .hook (some "Effect4.Machine.driveStep")),
  ("Effect4.Machine.RunInterp.finalizerProgram", .hook (some "Effect4.Machine.fireObserver")),
  ("Effect4.Machine.RunInterp.scopeStatus", .hook (some "Effect4.Machine.linkScope")),
  ("Effect4.Machine.RunInterp.closeScope", .hook (some "Effect4.Machine.FiberAction.closeScope")),
  ("Effect4.Machine.RunInterp.contextValue", .hook (some "Effect4.Machine.FiberAction.getContext")),
  ("Effect4.Machine.RunInterp.exitValue", .hook (some "Effect4.Machine.fireObserver")),
  ("Effect4.Machine.RunInterp.fiberValue", .hook (some "Effect4.Machine.FiberAction.fork")),
  ("Effect4.Machine.RunInterp.fiberIdValue", .hook (some "Effect4.Machine.FiberAction.getId")),
  ("Effect4.Machine.RunInterp.fibersValue", .hook (some "Effect4.Machine.FiberAction.snapshotChildren")),
  ("Effect4.Machine.RunInterp.exitsValue", .hook (some "Effect4.Machine.countdownPark")),
  ("Effect4.Machine.RunInterp.voidValue", .hook (some "Effect4.Program.Sched.evaluateFiberR")),
  ("Effect4.Machine.RunInterp.scopeValue", .hook (some "Effect4.Machine.FiberAction.ambientScope")),
  ("Effect4.Machine.RunInterp.prepareAnswer", .hook none)
]

/-- Every row. -/
def sources : List Row := stateSources ++ hookSources

end Effect4.Program.Typed
