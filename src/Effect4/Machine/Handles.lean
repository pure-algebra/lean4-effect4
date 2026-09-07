import Effect4.Machine.Clauses
import Effect4.Machine.StoresLaws
import Effect4.Machine.Approximation

/-!
# Collected handles name allocated objects

Packet: `Test/contracts/machine-handles.contract.md`. Node C13 (`handles_minted`, G5) of
`docs/research/2026-09-05-runtime-proof-graph.md`; the worksheet is
`docs/research/2026-09-05-first-slice-worksheets.md` §W3.

A handle is a fiber id, a Ref key, a Deferred key or a scope key. This module collects the
handles that occur in every carrier of the frame-instance machine — values, exits, contexts,
store operations, names and thunks, code by structural recursion, a fiber's frame, pending
parks, observers, children, dispatcher tasks and exit, a race's host, live entrants and
unforked programs, the store's heap, Deferred completions and owed resumes, and the scope
store's finalizer names — and states `MintedAt nk sk m`: every collected handle names a
fiber of `m.fibers`, a heap index, a Deferred cell or a scope entry of `m.state`. The
predicate is decidable. The trace is excluded.

The alphabet of names and thunks is a parameter (`nk`, `sk`): the stores' own alphabet and
the compile's native alphabet are two instances of one invariant. What the interpreter's
hooks may answer is `KeyBounded`: every hook's output names only handles its inputs named,
an explicit ambient list for source callbacks, or ones the store just minted (`syncState`,
`registerAsync`, `scopeLinkFiber`, `closeScope`, `dueResumes`). Ambient handles must exist
in the machine at evaluation. The stores' interpreter is proved `KeyBounded` here (`stores_keyBounded`); the
compile's `interpOf root` is proved in `Effect4.Program.Handles`, where `Minted` on
`Api.Machine` and the top theorem `handles_minted` live.

What is proved: the frame machine's `step` and every helper `drive` reaches (`spawn`,
`start`, `injectYield`, `evaluatePrim` and its `withFiber` arms, `exitFiber`,
`fireObserver`, `launchEntrant`, `linkScope`, `interruptRecord`, `interruptEach`,
`countdownPark`, `settle`, `driveStep`), then `driveState`, `fire`, `flushAll`, `flushRoot`,
`stepDecision` and `replayEval` keep the invariant, under the tape premise `AnswersValidAt`:
every `answerAsync` on the tape names handles that exist in the machine it is answered
against (the C15 `TapeAddressed` reading, the ruling of 2026-09-06 on `E4-HANDLE-CE-001`).
Replay admission is not changed.

Excluded positions: numeric interruptor provenance in deferredInterruptWith and
interruptAll, and the interruptor inside a `Cause` (`Cause.interrupt (some id)`,
provenance that nothing dereferences; the tape's `interruptFrom` may name any fiber); the
closing exit a scope entry stores (`linkScope` reads only whether it is present, while
`closeResultOf` returns a void exit); the race's duplicate winner, failure reasons and
bookkeeping fields other than `live` and `accepted`; and Deferred waiter and due-resume
targets. The latter become command targets: `driveStep` ignores unknown resume targets,
while the separately collected completion code is what can enter a frame. `Cmd.keys`
likewise collects resume code and finished exits, not target identifiers. The predicate
does not certify every identifier stored anywhere in the machine.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4

/-! ## Handles and their occurrences -/

/-- What a value can name that must have been minted. -/
inductive Handle
  | fiber (id : FiberId)
  | cell (key : RefKey)
  | promise (key : DeferredKey)
  | scope (key : Nat)
deriving DecidableEq, Repr

/-- The one handle a context holds: its ambient scope. -/
def Ctx.keys (ctx : Ctx) : List Handle :=
  match ctx.ambientScope with
  | some s => [Handle.scope s]
  | none => []

/-- The handles of a value: the five handle arms, a context, and the reified exit and list
arms, which carry values. A reified failed exit carries a cause only. -/
def Val.keys : Val → List Handle
  | Val.fiber id => [Handle.fiber id]
  | Val.fibers ids => ids.map Handle.fiber
  | Val.cell key => [Handle.cell key]
  | Val.promise key => [Handle.promise key]
  | Val.scopeHandle key => [Handle.scope key]
  | Val.context ctx => ctx.keys
  | Val.exitOk v => v.keys
  | Val.exitCons h t => h.keys ++ t.keys
  | _ => []

/-- The handles of an exit: its success value's. `Err` and `Defect` carry no value. -/
def exitKeys : ExitV → List Handle
  | Exit.success v => v.keys
  | Exit.failure _ => []

/-- The handles of an optional exit. -/
def optExitKeys : Option ExitV → List Handle
  | some exit => exitKeys exit
  | none => []

/-- The handles an external completion names. -/
def Completion.keys : Completion Val Err Defect FiberId Ann → List Handle
  | Completion.ofExit exit => exitKeys exit
  | Completion.ofRefGet cell => [Handle.cell cell]

/-- The handles of a park: the joined fiber. -/
def ParkKind.keys : ParkKind → List Handle
  | ParkKind.join target _ => [Handle.fiber target]
  -- a race identity is a lookup key, not a dereferenced handle (D6a)
  | ParkKind.race _ => []
  | ParkKind.awaitAll targets => targets.map Handle.fiber

/-- The handles a finalizer name carries. -/
def FinName.keys : FinName → List Handle
  | FinName.interruptFiber fiber _ => [Handle.fiber fiber]
  | FinName.closeChildScope scope => [Handle.scope scope]
  | FinName.detachFromParent parent _ => [Handle.scope parent]
  | FinName.release _ _ => []
  | FinName.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | FinName.parkThen _ => []

/-- The handles of a store operation: its keys and the values it writes. -/
def SyncOp.keys : SyncOp → List Handle
  | SyncOp.refMake initial => initial.keys
  | SyncOp.refGet cell => [Handle.cell cell]
  | SyncOp.refSet cell value => Handle.cell cell :: value.keys
  | SyncOp.refGetAndSet cell value => Handle.cell cell :: value.keys
  | SyncOp.refSetAndGet cell value => Handle.cell cell :: value.keys
  | SyncOp.refUpdate cell _ => [Handle.cell cell]
  | SyncOp.refGetAndUpdate cell _ => [Handle.cell cell]
  | SyncOp.refUpdateAndGet cell _ => [Handle.cell cell]
  | SyncOp.refUpdateSome cell _ => [Handle.cell cell]
  | SyncOp.refGetAndUpdateSome cell _ => [Handle.cell cell]
  | SyncOp.refUpdateSomeAndGet cell _ => [Handle.cell cell]
  | SyncOp.refModify cell _ => [Handle.cell cell]
  | SyncOp.refModifySome cell _ => [Handle.cell cell]
  | SyncOp.deferredMake => []
  | SyncOp.deferredIsDone cell => [Handle.promise cell]
  | SyncOp.deferredPoll cell => [Handle.promise cell]
  | SyncOp.deferredCompleteWith cell completion => Handle.promise cell :: completion.keys
  | SyncOp.deferredInterruptWith cell _ => [Handle.promise cell]
  | SyncOp.deferredAwaitCleanup cell waiter _ => [Handle.promise cell, Handle.fiber waiter]
  | SyncOp.scopeMake _ => []
  | SyncOp.scopeAdd scope _ finalizer => Handle.scope scope :: finalizer.keys
  | SyncOp.scopeRemove scope _ => [Handle.scope scope]
  | SyncOp.scopeIsClosed scope => [Handle.scope scope]

/-- The handles of a declared program name, through its bodies. -/
def ProgName.keys : ProgName → List Handle
  | ProgName.value v => v.keys
  | ProgName.failCause _ => []
  | ProgName.syncOp op => op.keys
  | ProgName.yieldNow _ => []
  | ProgName.park _ => []
  | ProgName.awaitDeferred cell => [Handle.promise cell]
  | ProgName.intoDeferred body cell => Handle.promise cell :: body.keys
  | ProgName.intoBody body cell => Handle.promise cell :: body.keys
  | ProgName.maskedPark _ => []
  | ProgName.awaitFibers targets => targets.map Handle.fiber
  | ProgName.finalizerOf fin exit => fin.keys ++ exitKeys exit
  | ProgName.interruptDeferred cell => [Handle.promise cell]
  | ProgName.onExitOf body fin _ => body.keys ++ fin.keys
  | ProgName.seqOf first second => first.keys ++ second.keys
  | ProgName.forkThen child _ _ => child.keys
  | ProgName.forkOnly child _ => child.keys
  | ProgName.forkInScope child _ scope => Handle.scope scope :: child.keys
  | ProgName.runInScope target scope => [Handle.fiber target, Handle.scope scope]
  | ProgName.forkScopedOf child _ => child.keys
  | ProgName.raceOf _ => []
  | ProgName.closeScopeOf scope exit => Handle.scope scope :: exitKeys exit
  | ProgName.awaitAllNew body => body.keys
  | ProgName.interruptFibers targets => targets.map Handle.fiber
  | ProgName.joinFiber target _ => [Handle.fiber target]
  | ProgName.cancelRace _ => []
  | ProgName.closeWalk _ order exit => order.flatMap FinName.keys ++ exitKeys exit

/-- The handles of a continuation, registration or cancel name of the stores' alphabet. -/
def Name.keys : Name → List Handle
  | Name.restore exit => exitKeys exit
  | Name.merge exit => exitKeys exit
  | Name.seq next => next.keys
  | Name.joinOn _ => []
  | Name.interruptWith cell => [Handle.promise cell]
  | Name.doneInto cell => [Handle.promise cell]
  | Name.constant value => value.keys
  | Name.exitOfValue => []
  | Name.snapshotThen body => body.keys
  | Name.registerAwait cell => [Handle.promise cell]
  | Name.cancelAwait cell => [Handle.promise cell]
  | Name.externalRegister _ => []
  | Name.abortController => []
  | Name.cancelPark => []
  | Name.cancelRace _ => []
  | Name.withWaiter base waiter _ => Handle.fiber waiter :: base.keys
  | Name.reFail _ => []
  | Name.finalizerName fin => fin.keys
  | Name.closeSeq remaining exit _ => remaining.flatMap FinName.keys ++ exitKeys exit
  | Name.closeParDone => []

/-- The handles of a `withFiber` action name. -/
def ActionName.keys : ActionName → List Handle
  | ActionName.fork program _ => program.keys
  | ActionName.forkIn program _ scope => Handle.scope scope :: program.keys
  | ActionName.forkScoped program _ => program.keys
  | ActionName.ambientScope => []
  | ActionName.runIn target scope => [Handle.fiber target, Handle.scope scope]
  | ActionName.interrupt target => [Handle.fiber target]
  -- the interruptor is cause data, not a dereferenced handle (`E4-HANDLE-CE-002`)
  | ActionName.interruptAs target _ => [Handle.fiber target]
  | ActionName.interruptScoped target => [Handle.fiber target]
  | ActionName.interruptAll targets _ => targets.map Handle.fiber
  | ActionName.awaitAll targets => targets.map Handle.fiber
  | ActionName.snapshotChildren => []
  | ActionName.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | ActionName.raceAll _ => []
  | ActionName.setContext context => context.keys
  | ActionName.getContext => []
  | ActionName.getId => []
  | ActionName.closeScope scope exit => Handle.scope scope :: exitKeys exit
  | ActionName.setInterruptible body _ => body.keys
  | ActionName.refuse _ => []
  | ActionName.dropObservers _ => []
  | ActionName.cancelRace _ => []
  | ActionName.closePar order exit => order.flatMap FinName.keys ++ exitKeys exit

/-- The handles of a thunk of the stores' alphabet. -/
def Thunk.keys : Thunk → List Handle
  | Thunk.park kind => kind.keys
  | Thunk.act action => action.keys
  | Thunk.op operation => operation.keys
  | Thunk.body program => program.keys

/-! ## Code, at any name and thunk alphabet -/

variable {ν σ : Type}

/-- The handles of a primitive: the value leaves, the names, the thunks, and the bodies. A
cause contributes nothing (`Cause.interrupt`'s interruptor is provenance, not a handle). -/
def primKeys (nk : ν → List Handle) (sk : σ → List Handle) :
    Prim ν σ Val Err Defect FiberId Ann → List Handle
  | Prim.success value => value.keys
  | Prim.failure _ => []
  | Prim.sync thunk => sk thunk
  | Prim.suspend thunk => sk thunk
  | Prim.withFiber thunk => sk thunk
  | Prim.yieldableError _ => []
  | Prim.iterator generator cursor => nk generator ++ cursor.keys
  | Prim.onSuccess body onValue => primKeys nk sk body ++ nk onValue
  | Prim.onSuccessConst body next => primKeys nk sk body ++ primKeys nk sk next
  | Prim.onFailure body onCause => primKeys nk sk body ++ nk onCause
  | Prim.onSuccessAndFailure body onValue onCause =>
    primKeys nk sk body ++ nk onValue ++ nk onCause
  | Prim.exitFrame body => primKeys nk sk body
  | Prim.onExit body finalizer _ => primKeys nk sk body ++ nk finalizer
  | Prim.setInterruptible _ => []
  | Prim.whileLoop loop cursor => nk loop ++ cursor.keys
  | Prim.yieldNowWith _ => []
  | Prim.async register _ cancel => nk register ++ (cancel.map nk).getD []
  | Prim.asyncFinalizer onInterrupt => nk onInterrupt

/-- The handles of a program of the stores' alphabet. -/
def programKeys : Program → List Handle := primKeys Name.keys Thunk.keys

/-- The handles a `withFiber` action carries. -/
def WithFiberAction.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    WithFiberAction ν σ Val Err Defect FiberId Ann Ctx → List Handle
  | WithFiberAction.fork program _ => primKeys nk sk program
  | WithFiberAction.forkIn program _ scope => Handle.scope scope :: primKeys nk sk program
  | WithFiberAction.forkScoped program _ => primKeys nk sk program
  | WithFiberAction.ambientScope => []
  | WithFiberAction.runIn target scope => [Handle.fiber target, Handle.scope scope]
  | WithFiberAction.interrupt target => [Handle.fiber target]
  | WithFiberAction.interruptAs target _ => [Handle.fiber target]
  | WithFiberAction.interruptScoped target => [Handle.fiber target]
  | WithFiberAction.interruptAll targets _ => targets.map Handle.fiber
  | WithFiberAction.awaitAll targets => targets.map Handle.fiber
  | WithFiberAction.awaitAllFailFast targets => targets.map Handle.fiber
  | WithFiberAction.snapshotChildren => []
  | WithFiberAction.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | WithFiberAction.raceAll entrants => entrants.flatMap (primKeys nk sk)
  | WithFiberAction.setInterruptible body _ => primKeys nk sk body
  | WithFiberAction.setContext context => context.keys
  | WithFiberAction.getContext => []
  | WithFiberAction.getId => []
  | WithFiberAction.closeScope scope exit => Handle.scope scope :: exitKeys exit
  | WithFiberAction.refuse _ => []
  | WithFiberAction.dropObservers _ => []
  | WithFiberAction.cancelRace _ => []
  | WithFiberAction.closePar finalizers => finalizers.flatMap (primKeys nk sk)

/-- The handles a frame holds: its current primitive and its stack. -/
def frameKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (f : FrameFiber ν σ Val Err Defect FiberId Ann) : List Handle :=
  primKeys nk sk f.current ++ f.stack.flatMap (primKeys nk sk)

/-- The handles a countdown's continuation names. -/
def Resume.keys (nk : ν → List Handle) : Resume ν → List Handle
  | Resume.exitsValue => []
  | Resume.void => []
  | Resume.continueWith name => nk name

/-- The handles of an outstanding park: the target observed, the targets left, the exits
collected and the continuation. -/
def Pending.keys (nk : ν → List Handle) (p : Pending ν Val Err Defect FiberId Ann) :
    List Handle :=
  (p.waitingOn.map Handle.fiber).toList ++ p.remaining.map Handle.fiber ++
    p.collected.flatMap exitKeys ++ p.resumeWith.keys nk

/-- The handles an observer names: the fiber it resumes, the parent it untracks, the scope
whose finalizer it drops. -/
def Observer.keys : Observer → List Handle
  | Observer.resumeAwait waiter _ _ => [Handle.fiber waiter]
  | Observer.untrackChild parent => [Handle.fiber parent]
  | Observer.dropScopeFinalizer scope _ => [Handle.scope scope]
  | Observer.countdown waiter _ => [Handle.fiber waiter]
  | Observer.raceCallback _ => []
  | Observer.callback _ => []

/-- The handles of a dispatcher task: the fiber it starts or resumes, and the resume's code. -/
def Task.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    Task ν σ Val Err Defect FiberId Ann → List Handle
  | Task.start child => [Handle.fiber child]
  | Task.resume target _ answer => Handle.fiber target :: primKeys nk sk answer

/-- The handles of every task a dispatcher holds. -/
def Dispatcher.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (d : Dispatcher ν σ Val Err Defect FiberId Ann) : List Handle :=
  d.buckets.flatMap fun b => b.tasks.flatMap (Task.keys nk sk)

/-- The handles a fiber holds: its frame, its parks, the exit it is finalizing and the exit it
stored, its observers, its children, its dispatcher and its context. -/
def RunFiber.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) : List Handle :=
  frameKeys nk sk f.frame ++ f.pending.flatMap (Pending.keys nk) ++
    optExitKeys f.finalizing ++ optExitKeys f.exit ++
    f.observers.flatMap Observer.keys ++ f.children.map Handle.fiber ++
    f.dispatcher.keys nk sk ++ f.context.keys

/-- The handles a race holds: its host, its live entrants, the exit it accepted (what
`raceSettle` resumes the host with), and the entrants not yet forked. -/
def Race.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (r : Race ν σ Val Err Defect FiberId Ann) : List Handle :=
  Handle.fiber r.host :: r.state.live.map Handle.fiber ++ optExitKeys r.state.accepted ++
    r.programs.flatMap (primKeys nk sk)

/-- The handles a command carries into a fiber: a resume's answer, a finish's or an
observer's exit, the fibers an interrupt walk or a tracking names, and an await park's
targets (D6b). -/
def Cmd.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    Cmd ν σ Val Err Defect FiberId Ann → List Handle
  | Cmd.resume _ _ answer => primKeys nk sk answer
  | Cmd.finish _ exit => exitKeys exit
  | Cmd.interruptTarget target _ _ => [Handle.fiber target]
  | Cmd.afterInterrupt host _ kind => Handle.fiber host :: kind.keys
  | Cmd.raceCancel _ host _ remaining visited =>
    Handle.fiber host :: (remaining ++ visited).map Handle.fiber
  | Cmd.trackChild parent child => [Handle.fiber parent, Handle.fiber child]
  | Cmd.observe fiber exit observer => Handle.fiber fiber :: exitKeys exit ++ observer.keys
  | Cmd.exitDone fiber => [Handle.fiber fiber]
  | Cmd.closeParAwait host _ fibers => Handle.fiber host :: fibers.map Handle.fiber
  | _ => []

/-- The handles of every command of a list. -/
def cmdsKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (cmds : List (Cmd ν σ Val Err Defect FiberId Ann)) : List Handle :=
  cmds.flatMap (Cmd.keys nk sk)

/-- The handles an iteration's outcome carries: a finished exit. -/
def Outcome.keys : Outcome ν σ Val Err Defect FiberId Ann → List Handle
  | Outcome.finished exit => exitKeys exit
  | _ => []

/-! ## The stores -/

/-- The handles a Deferred cell holds: its stored completion. -/
def DeferredCell.keys (c : DeferredCell) : List Handle :=
  match c.completion with
  | some program => programKeys program
  | none => []

/-- The handles of the Deferred store: every cell's completion and every owed resume's code. -/
def DeferredStore.keys (d : DeferredStore) : List Handle :=
  d.cells.flatMap DeferredCell.keys ++ d.due.flatMap fun r => programKeys r.2.2

/-- The handles a scope entry holds: its registered finalizer names. -/
def ScopeEntry.keys (e : ScopeEntry) : List Handle :=
  e.scope.finalizers.flatMap fun kf => FinName.keys kf.2

/-- The handles of the scope store. -/
def ScopeStore.keys (s : ScopeStore) : List Handle :=
  s.entries.flatMap ScopeEntry.keys

/-- The handles the stores hold: the heap's values, the Deferred store, the scope store. -/
def Stores.keys (s : Stores) : List Handle :=
  s.refs.flatMap Val.keys ++ s.deferreds.keys ++ s.scopes.keys

/-- The handles the machine holds: every fiber's, every race's, the armed queue, the stores. -/
def RunMachine.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : List Handle :=
  m.fibers.flatMap (RunFiber.keys nk sk) ++ m.races.flatMap (Race.keys nk sk) ++
    m.armed.map Handle.fiber ++ m.state.keys

/-- The handles an iteration leaves: its machine's, its fiber's, its nested commands' and its
finished exit's. -/
def iterKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) : List Handle :=
  it.machine.keys nk sk ++ it.fiber.keys nk sk ++ cmdsKeys nk sk it.nested ++ it.outcome.keys

/-- The machine at the frame instance, for ascriptions. -/
abbrev NM (ν σ : Type) := RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores

/-! ### The fields the machine's operations leave alone -/

section Projections

variable {m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores}

theorem races_update (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) : (m.update f).races = m.races := rfl
theorem armed_update (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) : (m.update f).armed = m.armed := rfl
theorem state_update (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) : (m.update f).state = m.state := rfl
theorem fibers_updateRace (r : Race ν σ Val Err Defect FiberId Ann) : (m.updateRace r).fibers = m.fibers := rfl
theorem armed_updateRace (r : Race ν σ Val Err Defect FiberId Ann) : (m.updateRace r).armed = m.armed := rfl
theorem state_updateRace (r : Race ν σ Val Err Defect FiberId Ann) : (m.updateRace r).state = m.state := rfl
theorem fibers_arm (owner : FiberId) : (m.arm owner).fibers = m.fibers := rfl
theorem races_arm (owner : FiberId) : (m.arm owner).races = m.races := rfl
theorem state_arm (owner : FiberId) : (m.arm owner).state = m.state := rfl
theorem fibers_disarm (owner : FiberId) : (m.disarm owner).fibers = m.fibers := rfl
theorem races_disarm (owner : FiberId) : (m.disarm owner).races = m.races := rfl
theorem state_disarm (owner : FiberId) : (m.disarm owner).state = m.state := rfl

theorem races_modify (id : FiberId)
    (k : RunFiber ν σ Val Err Defect FiberId Ann Ctx → RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.modify id k).races = m.races := by
  unfold RunMachine.modify; split <;> rfl
theorem armed_modify (id : FiberId)
    (k : RunFiber ν σ Val Err Defect FiberId Ann Ctx → RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.modify id k).armed = m.armed := by
  unfold RunMachine.modify; split <;> rfl
theorem state_modify (id : FiberId)
    (k : RunFiber ν σ Val Err Defect FiberId Ann Ctx → RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.modify id k).state = m.state := by
  unfold RunMachine.modify; split <;> rfl

end Projections

/-! ## Existence -/

/-- What handles are checked against: the fiber ids the machine holds and its stores. -/
structure World where
  ids : List FiberId
  state : Stores

/-- The world of a machine. -/
def RunMachine.world (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : World :=
  ⟨m.fibers.map RunFiber.id, m.state⟩

/-- Whether a handle names something that exists: a fiber the machine holds, a heap index, a
Deferred cell, a scope entry (`Val.validIn`'s three store arms, `StoresLaws.lean`). -/
def Handle.existsIn (w : World) : Handle → Bool
  | Handle.fiber id => decide (id ∈ w.ids)
  | Handle.cell key => decide (key.index < w.state.refs.length)
  | Handle.promise key => decide (key.index < w.state.deferreds.cells.length)
  | Handle.scope key => (w.state.scopes.entryAt key).isSome

/-- Every handle of a list exists in a world. -/
def Ok (w : World) (hs : List Handle) : Prop := ∀ h ∈ hs, h.existsIn w = true

instance (w : World) (hs : List Handle) : Decidable (Ok w hs) :=
  inferInstanceAs (Decidable (∀ h ∈ hs, h.existsIn w = true))

/-- Every handle of a list exists in a machine. -/
def MintedIn (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (hs : List Handle) :
    Prop := Ok m.world hs

instance (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (hs : List Handle) :
    Decidable (MintedIn m hs) :=
  inferInstanceAs (Decidable (Ok m.world hs))

/-- Every collected handle names something the machine or its stores minted. -/
def MintedAt (nk : ν → List Handle) (sk : σ → List Handle)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  MintedIn m (m.keys nk sk)

instance (nk : ν → List Handle) (sk : σ → List Handle)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : Decidable (MintedAt nk sk m) :=
  inferInstanceAs (Decidable (MintedIn m (m.keys nk sk)))

/-- A world grows: the fibers it holds and the stores' allocations only increase. -/
def World.le (w w' : World) : Prop :=
  (∀ id ∈ w.ids, id ∈ w'.ids) ∧ w.state.le w'.state

/-! ## What an interpreter may answer

Each hook of `RunInterp` may name only handles its inputs named. The six source callback
services may additionally read an explicit ambient list, justified at evaluation; store
steps may mint, with the answer and resulting store checked in that store. -/

/-- The hooks name only their inputs, the explicit ambient callback view, or fresh store
allocations. Empty ambient retains the original static interpreter contract. -/
structure KeyBounded (nk : ν → List Handle) (sk : σ → List Handle)
    (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (ambient : List Handle := []) : Prop where
  contA : ∀ n v, primKeys nk sk (interp.contA n v) ⊆ ambient ++ (nk n ++ v.keys)
  contE : ∀ n c, primKeys nk sk (interp.contE n c) ⊆ ambient ++ (nk n)
  syncValue : ∀ t, (interp.syncValue t).keys ⊆ sk t
  suspendBody : ∀ t, primKeys nk sk (interp.suspendBody t) ⊆ ambient ++ (sk t)
  reifyExit : ∀ e, (interp.reifyExit e).keys ⊆ exitKeys e
  iterNext_done : ∀ n v r, (interp.iterNext n v).2 = IterStep.done r → r.keys ⊆ ambient ++ (nk n ++ v.keys)
  iterNext_resume : ∀ n v next n', (interp.iterNext n v).2 = IterStep.resume next n' →
    primKeys nk sk next ++ nk n' ⊆ ambient ++ (nk n ++ v.keys)
  loopBody : ∀ n c, primKeys nk sk (interp.loopBody n c) ⊆ ambient ++ (nk n ++ c.keys)
  loopStep : ∀ n c v, (interp.loopStep n c v).keys ⊆ nk n ++ c.keys ++ v.keys
  loopDone : ∀ n, (interp.loopDone n).keys ⊆ nk n
  cancelThenFail : ∀ n c, primKeys nk sk (interp.cancelThenFail n c) ⊆ nk n
  parkOf : ∀ code target mode, interp.parkOf code = some (Except.ok (ParkKind.join target mode)) →
    Handle.fiber target ∈ primKeys nk sk code
  parkCode : ∀ kind, primKeys nk sk (interp.parkCode kind) ⊆ kind.keys
  /-- An await-all park names its targets (D6b). -/
  parkOfAwaitAll : ∀ code targets, interp.parkOf code = some (Except.ok (ParkKind.awaitAll targets)) →
    targets.map Handle.fiber ⊆ primKeys nk sk code
  /-- The interrupt programs name their target; the interruptor is cause data (D6b). -/
  interruptCode : ∀ target, primKeys nk sk (interp.interruptCode target) ⊆ [Handle.fiber target]
  interruptAsCode : ∀ target who,
    primKeys nk sk (interp.interruptAsCode target who) ⊆ [Handle.fiber target]
  interruptAllCode : ∀ targets,
    primKeys nk sk (interp.interruptAllCode targets) ⊆ targets.map Handle.fiber
  withFiberOf : ∀ t a, interp.withFiberOf t = some a → a.keys nk sk ⊆ sk t
  syncState : ∀ t s s' v ids, interp.syncState t s = some (s', v) →
    Ok ⟨ids, s⟩ (sk t ++ s.keys) → s.le s' ∧ Ok ⟨ids, s'⟩ (v.keys ++ s'.keys)
  registerAsync : ∀ n fiber token s ids, Ok ⟨ids, s⟩ (nk n ++ s.keys) →
    s.le (interp.registerAsync n fiber token s).1 ∧
      Ok ⟨ids, (interp.registerAsync n fiber token s).1⟩
        ((interp.registerAsync n fiber token s).1.keys ++
          ((interp.registerAsync n fiber token s).2.map (primKeys nk sk)).getD [])
  answerCode : ∀ c, primKeys nk sk (interp.answerCode c) ⊆ c.keys
  dueResumes : ∀ s ids, Ok ⟨ids, s⟩ s.keys →
    s.le (interp.dueResumes s).2 ∧
      Ok ⟨ids, (interp.dueResumes s).2⟩
        ((interp.dueResumes s).2.keys ++ (interp.dueResumes s).1.flatMap fun d => primKeys nk sk d.2.2)
  cancelName : ∀ base fiber token, nk (interp.cancelName base fiber token) ⊆ Handle.fiber fiber :: nk base
  abortName : nk interp.abortName = []
  parkCancelName : nk interp.parkCancelName = []
  raceCancelName : ∀ race, nk (interp.raceCancelName race) = []
  raceSettle : ∀ race cleanupNeeded exit,
    primKeys nk sk (interp.raceSettle race cleanupNeeded exit) ⊆ exitKeys exit
  finalizerProgram : ∀ n e p, interp.finalizerProgram n e = some p →
    primKeys nk sk p ⊆ ambient ++ (nk n ++ exitKeys e)
  restoreName : ∀ e, nk (interp.restoreName e) ⊆ exitKeys e
  mergeName : ∀ e, nk (interp.mergeName e) ⊆ exitKeys e
  scopeStatus : ∀ scope s, (interp.scopeStatus scope s).isSome = true →
    (s.scopes.entryAt scope).isSome = true
  scopeLinkFiber : ∀ mode scope fiber s s' key ids,
    interp.scopeLinkFiber mode scope fiber s = some (s', key) →
    Ok ⟨ids, s⟩ (Handle.fiber fiber :: s.keys) → s.le s' ∧ Ok ⟨ids, s'⟩ s'.keys
  dropFinalizer : ∀ scope key s s' ids, interp.dropFinalizer scope key s = some s' →
    Ok ⟨ids, s⟩ s.keys → s.le s' ∧ Ok ⟨ids, s'⟩ s'.keys
  closeScope : ∀ scope exit flag closer s s' p ids,
    interp.closeScope scope exit flag closer s = some (s', p) →
    Ok ⟨ids, s⟩ (Handle.fiber closer :: exitKeys exit ++ s.keys) →
      s.le s' ∧ Ok ⟨ids, s'⟩ (primKeys nk sk p ++ s'.keys)
  emptyContext : interp.emptyContext.keys = []
  contextValue : ∀ ctx, (interp.contextValue ctx).keys ⊆ ctx.keys
  exitValue : ∀ e mode, primKeys nk sk (interp.exitValue e mode) ⊆ exitKeys e
  fiberValue : ∀ id, (interp.fiberValue id).keys ⊆ [Handle.fiber id]
  fiberIdValue : ∀ id, (interp.fiberIdValue id).keys ⊆ [Handle.fiber id]
  fibersValue : ∀ ids, (interp.fibersValue ids).keys ⊆ ids.map Handle.fiber
  exitsValue : ∀ exits, (interp.exitsValue exits).keys ⊆ exits.flatMap exitKeys
  voidValue : interp.voidValue.keys = []
  /-- A scope handle value names its scope (§20). -/
  scopeValue : ∀ scope, (interp.scopeValue scope).keys ⊆ [Handle.scope scope]
  /-- The parallel close's generator name is closed (§20). -/
  closeDoneName : nk interp.closeDoneName = []
  /-- The ambient scope a context answers is one the context names (§20). -/
  ambientScope : ∀ ctx scope, interp.ambientScope ctx = some scope → Handle.scope scope ∈ ctx.keys

/-! ## Existence: the lemmas -/

theorem Ok_nil (w : World) : Ok w [] := fun _ h => nomatch h

theorem Ok_cons {w : World} {h : Handle} {hs : List Handle} :
    Ok w (h :: hs) ↔ h.existsIn w = true ∧ Ok w hs := by
  constructor
  · intro ok
    exact ⟨ok h (List.mem_cons_self), fun x hx => ok x (List.mem_cons_of_mem _ hx)⟩
  · intro ⟨hh, ok⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh
    · exact ok x hx

theorem Ok_append {w : World} {a b : List Handle} : Ok w (a ++ b) ↔ Ok w a ∧ Ok w b := by
  constructor
  · intro ok
    exact ⟨fun x hx => ok x (List.mem_append_left _ hx),
      fun x hx => ok x (List.mem_append_right _ hx)⟩
  · intro ⟨ha, hb⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ha x hx
    · exact hb x hx

theorem Ok_of_subset {w : World} {a b : List Handle} (hsub : a ⊆ b) (ok : Ok w b) : Ok w a :=
  fun x hx => ok x (hsub hx)

theorem Ok_flatMap {w : World} {γ : Type} {l : List γ} {f : γ → List Handle} :
    Ok w (l.flatMap f) ↔ ∀ x ∈ l, Ok w (f x) := by
  constructor
  · intro ok x hx h hh
    exact ok h (List.mem_flatMap.mpr ⟨x, hx, hh⟩)
  · intro ok h hh
    obtain ⟨x, hx, hh⟩ := List.mem_flatMap.mp hh
    exact ok x hx h hh

theorem Ok_map {w : World} {γ : Type} {l : List γ} {f : γ → Handle} :
    Ok w (l.map f) ↔ ∀ x ∈ l, (f x).existsIn w = true := by
  constructor
  · intro ok x hx
    exact ok (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro ok h hh
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hh
    exact ok x hx

theorem World.le_refl (w : World) : w.le w := ⟨fun _ h => h, Stores.le_refl _⟩

theorem World.le_trans {a b c : World} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  ⟨fun id h => h₂.1 id (h₁.1 id h), Stores.le_trans h₁.2 h₂.2⟩

/-- A handle that exists keeps existing as the world grows: fibers are never removed and the
stores only grow (`Stores.le`). -/
theorem Handle.existsIn_mono {w w' : World} (hle : w.le w') (h : Handle)
    (hh : h.existsIn w = true) : h.existsIn w' = true := by
  cases h with
  | fiber id =>
    simp only [Handle.existsIn, decide_eq_true_eq] at hh ⊢
    exact hle.1 id hh
  | cell key =>
    simp only [Handle.existsIn, decide_eq_true_eq] at hh ⊢
    exact Nat.lt_of_lt_of_le hh hle.2.1
  | promise key =>
    simp only [Handle.existsIn, decide_eq_true_eq] at hh ⊢
    exact Nat.lt_of_lt_of_le hh hle.2.2.1
  | scope key =>
    simp only [Handle.existsIn] at hh ⊢
    exact hle.2.2.2.1 key hh

theorem Ok_mono {w w' : World} (hle : w.le w') {hs : List Handle} (ok : Ok w hs) : Ok w' hs :=
  fun h hh => Handle.existsIn_mono hle h (ok h hh)

/-- The same fibers over a store that grew. -/
theorem World.le_of_state {ids : List FiberId} {s s' : Stores} (h : s.le s') :
    World.le ⟨ids, s⟩ ⟨ids, s'⟩ :=
  ⟨fun _ hh => hh, h⟩

/-! ### The subset and membership searches

`sub_tac` proves `A ⊆ B` when `A` and `B` are trees of `++`, `::` and `[]` over atoms and every
atom of `A` is an atom of `B` or a hypothesis names it: the key traversals of the machine's
carriers are unfolded to the same depth on both sides, membership is unfolded over the tree,
the hypothesis is split into its cases, and each case is found among the goal's disjuncts.
`mem_tac` proves `a ∈ B` the same way. Neither chain ends in an `exact` on a name that might
not exist, and the search is linear in the tree. -/

syntax "or_search" : tactic
macro_rules
  | `(tactic| or_search) => `(tactic| first
      | assumption
      | exact Or.inl ‹_›
      | (apply Or.inr; or_search))

/-- The key traversals unfolded to one depth, and membership unfolded over the tree. The optional
list adds the unfoldings a section needs beyond the machine's own carriers. -/
syntax "keys_mem_norm" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| keys_mem_norm) => `(tactic| keys_mem_norm [])
  | `(tactic| keys_mem_norm [$extra,*]) => `(tactic|
      simp only [RunMachine.keys, RunMachine.emit, RunMachine.halt, races_update, armed_update, state_update,
        fibers_updateRace, armed_updateRace, state_updateRace, fibers_arm, races_arm, state_arm, fibers_disarm,
        races_disarm, state_disarm, races_modify, armed_modify, state_modify, WithFiberAction.keys,
        RunFiber.keys, RunFiber.park, frameKeys, Race.keys, iterKeys, cmdsKeys,
        Cmd.keys, Outcome.keys, Pending.keys, Task.keys, Observer.keys, Resume.keys, optExitKeys, Stores.keys,
        primKeys, exitKeys, Val.keys, Supervision.RaceAllState.initial,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.map_append, List.map_cons, List.map_nil,
        List.append_nil, List.nil_append, List.append_assoc, Option.map, Option.toList, Option.getD_some,
        Option.getD_none, List.mem_append,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_assoc, true_or, or_true, false_or, or_false,
        eq_self_iff_true, $extra,*])

/-- The same normalisation at a hypothesis. -/
syntax "keys_mem_norm_at" ident (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| keys_mem_norm_at $h:ident) => `(tactic| keys_mem_norm_at $h [])
  | `(tactic| keys_mem_norm_at $h:ident [$extra,*]) => `(tactic|
      simp only [RunMachine.keys, RunMachine.emit, RunMachine.halt, races_update, armed_update, state_update,
        fibers_updateRace, armed_updateRace, state_updateRace, fibers_arm, races_arm, state_arm, fibers_disarm,
        races_disarm, state_disarm, races_modify, armed_modify, state_modify, WithFiberAction.keys,
        RunFiber.keys, RunFiber.park, frameKeys, Race.keys, iterKeys, cmdsKeys,
        Cmd.keys, Outcome.keys, Pending.keys, Task.keys, Observer.keys, Resume.keys, optExitKeys, Stores.keys,
        primKeys, exitKeys, Val.keys, Supervision.RaceAllState.initial,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.map_append, List.map_cons, List.map_nil,
        List.append_nil, List.nil_append, List.append_assoc, Option.map, Option.toList, Option.getD_some,
        Option.getD_none, List.mem_append,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_assoc, true_or, or_true, false_or, or_false,
        eq_self_iff_true, $extra,*] at $h:ident)

syntax "mem_tac" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| mem_tac) => `(tactic| mem_tac [])
  | `(tactic| mem_tac [$extra,*]) => `(tactic| (
      try keys_mem_norm [$extra,*]
      first | done | trivial | or_search))

/-- Close a membership goal from the case hypothesis `h`: the goal is already normalised, so
rewriting with `h` is tried first (syntactic, cheap), an equation left by `subst` next, and
the linear search last. -/
syntax "close_mem" ident (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| close_mem $h:ident) => `(tactic| close_mem $h [])
  | `(tactic| close_mem $h:ident [$extra,*]) => `(tactic| first
      | done
      | trivial
      | (simp only [$h:ident, true_or, or_true]; done)
      | (simp only [eq_self_iff_true, true_or, or_true]; done)
      | mem_tac [$extra,*])

syntax "sub_tac" (" using " term,+)? (" norm " "[" (Lean.Parser.Tactic.simpStar <|>
  Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| sub_tac) => `(tactic| sub_tac norm [])
  | `(tactic| sub_tac using $hs:term,*) => `(tactic| sub_tac using $hs,* norm [])
  | `(tactic| sub_tac norm [$extra,*]) => `(tactic| (
      intro x hx
      try keys_mem_norm_at hx [$extra,*]
      try keys_mem_norm [$extra,*]
      repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
      all_goals (try subst hx)
      all_goals close_mem hx [$extra,*]))
  | `(tactic| sub_tac using $hs:term,* norm [$extra,*]) => `(tactic| (
      intro x hx
      try keys_mem_norm_at hx [$extra,*]
      try keys_mem_norm [$extra,*]
      repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
      all_goals (try subst hx)
      -- a case not among the goal's atoms is carried through the facts, at most three deep
      all_goals (first
        | close_mem hx [$extra,*]
        | (first $[| replace hx := $hs hx]*
           try keys_mem_norm_at hx [$extra,*]
           repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
           all_goals (first
             | close_mem hx [$extra,*]
             | (first $[| replace hx := $hs hx]*
                try keys_mem_norm_at hx [$extra,*]
                repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
                all_goals (first
                  | close_mem hx [$extra,*]
                  | (first $[| replace hx := $hs hx]*
                     try keys_mem_norm_at hx [$extra,*]
                     repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
                     all_goals close_mem hx [$extra,*]))))))))

/-! ### Small facts about the key traversals -/

theorem primKeys_ofExit (nk : ν → List Handle) (sk : σ → List Handle) (e : ExitV) :
    primKeys nk sk (Prim.ofExit e) = exitKeys e := by
  cases e <;> rfl

theorem exitKeys_restoreAfterFinalizer (e : ExitV) (f : VoidExitV) :
    exitKeys (Exit.restoreAfterFinalizer e f) ⊆ exitKeys e := by
  unfold Exit.restoreAfterFinalizer
  split
  · exact List.Subset.refl _
  · exact List.nil_subset _

theorem optExitKeys_getD_success (provided : Option ExitV) (v : Val) :
    exitKeys (provided.getD (Exit.success v)) ⊆ v.keys ++ optExitKeys provided := by
  cases provided with
  | none => exact List.subset_append_left _ _
  | some e => exact List.subset_append_right _ _

theorem optExitKeys_getD_failure (provided : Option ExitV) (c : CauseV) :
    exitKeys (provided.getD (Exit.failure c)) ⊆ optExitKeys provided := by
  cases provided with
  | none => exact List.nil_subset _
  | some e => exact List.Subset.refl _

/-! ## The frame machine keeps its handles

`FrameFiber.step` builds every new frame from the frames it popped, the current primitive and
the hooks' answers, so under `KeyBounded` the fiber it leaves names only what the fiber it
took named. -/

variable (nk : ν → List Handle) (sk : σ → List Handle)

/-- The handles of a pop's answer. -/
def contAnswerKeys : ContAnswer ν σ Val Err Defect FiberId Ann → List Handle
  | ContAnswer.deferred _ => []
  | ContAnswer.replacement next => primKeys nk sk next
  | ContAnswer.frame frame => primKeys nk sk frame
  | ContAnswer.empty => []

/-- The handles of an optional replacement. -/
def optPrimKeys : Option (Prim ν σ Val Err Defect FiberId Ann) → List Handle
  | some p => primKeys nk sk p
  | none => []

/-- The handles a pop leaves: its answer's and its fiber's. -/
def popKeys (pop : FramePop ν σ Val Err Defect FiberId Ann) : List Handle :=
  contAnswerKeys nk sk pop.answer ++ frameKeys nk sk pop.fiber

/-- The handles a step leaves: the running fiber's, or the exit's. -/
def stepKeys : FrameStep ν σ Val Err Defect FiberId Ann → List Handle
  | FrameStep.running f => frameKeys nk sk f
  | FrameStep.finished e => exitKeys e

theorem ensure_fst_keys (frame : Prim ν σ Val Err Defect FiberId Ann)
    (fiber : FrameFiber ν σ Val Err Defect FiberId Ann) :
    frameKeys nk sk (frame.ensure fiber).1 ⊆ frameKeys nk sk fiber := by
  cases frame <;> simp only [Prim.ensure] <;> (repeat' split) <;>
    simp only [frameKeys, List.flatMap_cons, primKeys, List.nil_append] <;> sub_tac

theorem ensure_snd_keys (frame : Prim ν σ Val Err Defect FiberId Ann)
    (fiber : FrameFiber ν σ Val Err Defect FiberId Ann) :
    optPrimKeys nk sk (frame.ensure fiber).2 = [] := by
  cases frame <;> simp only [Prim.ensure] <;> (repeat' split) <;> rfl

theorem answerOf_keys (frame : Prim ν σ Val Err Defect FiberId Ann) (demand : Arm)
    (replacement : Option (Prim ν σ Val Err Defect FiberId Ann))
    (ans : ContAnswer ν σ Val Err Defect FiberId Ann)
    (h : frame.answerOf demand replacement = some ans) :
    contAnswerKeys nk sk ans ⊆ primKeys nk sk frame ++ optPrimKeys nk sk replacement := by
  unfold Prim.answerOf at h
  split at h
  · cases h
    exact List.subset_append_right _ _
  · split at h
    · cases h
      exact List.subset_append_left _ _
    · cases h

theorem passPushed_keys (demand : Arm) (skip : Bool)
    (fiber : FrameFiber ν σ Val Err Defect FiberId Ann) :
    popKeys nk sk (FrameFiber.passPushed demand skip fiber) ⊆ frameKeys nk sk fiber := by
  unfold FrameFiber.passPushed
  split
  · next hstack =>
    simp only [popKeys, contAnswerKeys, List.nil_append]
    exact List.Subset.refl _
  · next pushed below hstack =>
    simp only [popKeys]
    have hfib : frameKeys nk sk fiber =
        primKeys nk sk fiber.current ++ (pushed :: below).flatMap (primKeys nk sk) := by
      simp only [frameKeys, hstack]
    rw [hfib]
    simp only [List.flatMap_cons]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · split
      · next ans hans =>
        split
        · exact List.nil_subset _
        · have := answerOf_keys nk sk pushed demand _ ans hans
          rw [ensure_snd_keys, List.append_nil] at this
          refine List.Subset.trans this ?_
          sub_tac
      · exact List.nil_subset _
    · refine List.Subset.trans (ensure_fst_keys nk sk pushed _) ?_
      simp only [frameKeys]
      sub_tac

theorem joinPushed_keys (demand : Arm) (skip : Bool)
    (afterHook : FrameFiber ν σ Val Err Defect FiberId Ann)
    (rest : List (Prim ν σ Val Err Defect FiberId Ann))
    (tail : FramePop ν σ Val Err Defect FiberId Ann) :
    popKeys nk sk (FrameFiber.joinPushed demand skip afterHook rest tail) ⊆
      frameKeys nk sk afterHook ++ rest.flatMap (primKeys nk sk) ++ popKeys nk sk tail := by
  have hpp := passPushed_keys nk sk demand skip afterHook
  unfold FrameFiber.joinPushed
  split
  · simp only [popKeys] at hpp ⊢
    sub_tac
  · simp only [popKeys, frameKeys, List.flatMap_append] at hpp ⊢
    simp only [List.append_subset] at hpp
    refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
    · refine List.Subset.trans hpp.1 ?_; sub_tac
    · refine List.Subset.trans hpp.2.1 ?_; sub_tac
    · refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans hpp.2.2 ?_; sub_tac
      · sub_tac

theorem popFrom_keys (demand : Arm) (skip : Bool) :
    ∀ (frames : List (Prim ν σ Val Err Defect FiberId Ann))
      (fiber : FrameFiber ν σ Val Err Defect FiberId Ann),
      popKeys nk sk (FrameFiber.popFrom demand skip frames fiber) ⊆
        frames.flatMap (primKeys nk sk) ++ frameKeys nk sk fiber
  | [], fiber => by
    simp only [FrameFiber.popFrom, popKeys, contAnswerKeys, List.flatMap_nil, List.nil_append]
    exact List.Subset.refl _
  | frame :: rest, fiber => by
    have hens := ensure_fst_keys nk sk frame fiber
    have hpp := passPushed_keys nk sk demand skip (frame.ensure fiber).1
    have ih := popFrom_keys demand skip rest (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber
    have hjoin := joinPushed_keys nk sk demand skip (frame.ensure fiber).1 rest
      (FrameFiber.popFrom demand skip rest (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber)
    simp only [popKeys] at hpp ih hjoin
    have hpf : frameKeys nk sk (FrameFiber.passPushed demand skip (frame.ensure fiber).1).fiber ⊆
        frameKeys nk sk fiber :=
      List.Subset.trans (List.append_subset.mp hpp).2 hens
    simp only [FrameFiber.popFrom, List.flatMap_cons]
    split
    · next ans hans =>
      split
      · simp only [FrameFiber.passOn, popKeys]
        refine List.Subset.trans hjoin ?_
        refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
        · refine List.Subset.trans hens ?_; sub_tac
        · sub_tac
        · refine List.Subset.trans ih ?_
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · sub_tac
          · refine List.Subset.trans hpf ?_; sub_tac
      · simp only [popKeys]
        have hak := answerOf_keys nk sk frame demand _ ans hans
        rw [ensure_snd_keys, List.append_nil] at hak
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans hak ?_; sub_tac
        · simp only [frameKeys, List.flatMap_append]
          simp only [frameKeys] at hens
          refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
          · refine List.Subset.trans (List.append_subset.mp hens).1 ?_; sub_tac
          · refine List.Subset.trans (List.append_subset.mp hens).2 ?_; sub_tac
          · sub_tac
    · simp only [FrameFiber.passOn, popKeys]
      refine List.Subset.trans hjoin ?_
      refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
      · refine List.Subset.trans hens ?_; sub_tac
      · sub_tac
      · refine List.Subset.trans ih ?_
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · sub_tac
        · refine List.Subset.trans hpf ?_; sub_tac

theorem getCont_keys (self : FrameFiber ν σ Val Err Defect FiberId Ann) (demand : Arm)
    (skip : Bool) : popKeys nk sk (self.getCont demand skip) ⊆ frameKeys nk sk self := by
  unfold FrameFiber.getCont
  split
  · simp only [popKeys, contAnswerKeys, List.nil_append, frameKeys]
    exact List.Subset.refl _
  · refine List.Subset.trans (popFrom_keys nk sk demand skip self.stack _) ?_
    simp only [frameKeys, List.flatMap_nil, List.append_nil]
    sub_tac

/-- A pop that answers with a frame: that frame's handles and the popped fiber's are the
fiber's. -/
theorem getCont_answer_frame_keys (self : FrameFiber ν σ Val Err Defect FiberId Ann) (demand : Arm)
    (skip : Bool) (frame : Prim ν σ Val Err Defect FiberId Ann)
    (h : (self.getCont demand skip).answer = ContAnswer.frame frame) :
    primKeys nk sk frame ⊆ frameKeys nk sk self ∧
      frameKeys nk sk (self.getCont demand skip).fiber ⊆ frameKeys nk sk self := by
  have := getCont_keys nk sk self demand skip
  simp only [popKeys, h, contAnswerKeys, List.append_subset] at this
  exact this

variable {interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores}
variable {ambient : List Handle}

theorem armA_keys_with_ambient (hb : KeyBounded nk sk interp ambient) (frame : Prim ν σ Val Err Defect FiberId Ann)
    (value : Val) (provided : Option ExitV) (next : Prim ν σ Val Err Defect FiberId Ann)
    (pushed : List (Prim ν σ Val Err Defect FiberId Ann))
    (h : frame.armA interp.toPrimInterp value provided = some (next, pushed)) :
    primKeys nk sk next ++ pushed.flatMap (primKeys nk sk) ⊆
      ambient ++ (primKeys nk sk frame ++ value.keys ++ optExitKeys provided) := by
  cases frame with
  | onSuccess body onValue =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.contA onValue value) ?_
    sub_tac
  | onSuccessConst body saved =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    sub_tac
  | onSuccessAndFailure body onValue onCause =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.contA onValue value) ?_
    sub_tac
  | exitFrame body =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.reifyExit _) ?_
    refine List.Subset.trans (optExitKeys_getD_success provided value) ?_
    sub_tac
  | onExit body finalizer flag =>
    simp only [Prim.armA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys_ofExit]
    refine List.Subset.trans (exitKeys_restoreAfterFinalizer _ _) ?_
    refine List.Subset.trans (optExitKeys_getD_success provided value) ?_
    sub_tac
  | whileLoop loop cursor =>
    simp only [Prim.armA] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, primKeys]
      have hstep := hb.loopStep loop cursor value
      refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
      · refine List.Subset.trans (hb.loopBody loop _) ?_
        sub_tac using hstep
      · sub_tac
      · refine List.Subset.trans hstep ?_; sub_tac
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.flatMap_nil, List.append_nil, primKeys]
      refine List.Subset.trans (hb.loopDone loop) ?_
      sub_tac
  | iterator generator cursor =>
    simp only [Prim.armA] at h
    split at h
    · next result hiter =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.flatMap_nil, List.append_nil, primKeys]
      refine List.Subset.trans (hb.iterNext_done generator value result hiter) ?_
      sub_tac
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.flatMap_nil, List.append_nil, primKeys]
      exact List.nil_subset _
    · next next' continueAs hiter =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, primKeys]
      have hres := hb.iterNext_resume generator value next' continueAs hiter
      simp only [List.append_subset] at hres
      refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
      · refine List.Subset.trans hres.1 ?_; sub_tac
      · refine List.Subset.trans hres.2 ?_; sub_tac
      · sub_tac
  | success _ | failure _ | sync _ | suspend _ | withFiber _ | yieldableError _ | onFailure _ _
  | setInterruptible _ | yieldNowWith _ | async _ _ _ | asyncFinalizer _ =>
    simp only [Prim.armA] at h
    cases h

theorem armE_keys_with_ambient (hb : KeyBounded nk sk interp ambient) (frame : Prim ν σ Val Err Defect FiberId Ann)
    (cause : CauseV) (provided : Option ExitV) (next : Prim ν σ Val Err Defect FiberId Ann)
    (pushed : List (Prim ν σ Val Err Defect FiberId Ann))
    (h : frame.armE interp.toPrimInterp cause provided = some (next, pushed)) :
    primKeys nk sk next ++ pushed.flatMap (primKeys nk sk) ⊆
      ambient ++ (primKeys nk sk frame ++ optExitKeys provided) := by
  cases frame with
  | onFailure body onCause =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.contE onCause cause) ?_
    sub_tac
  | onSuccessAndFailure body onValue onCause =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.contE onCause cause) ?_
    sub_tac
  | exitFrame body =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    refine List.Subset.trans (hb.reifyExit _) ?_
    refine List.Subset.trans (optExitKeys_getD_failure provided cause) ?_
    sub_tac
  | onExit body finalizer flag =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys_ofExit]
    refine List.Subset.trans (exitKeys_restoreAfterFinalizer _ _) ?_
    refine List.Subset.trans (optExitKeys_getD_failure provided cause) ?_
    sub_tac
  | asyncFinalizer onInterrupt =>
    simp only [Prim.armE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.flatMap_nil, List.append_nil, primKeys]
    split
    · refine List.Subset.trans (hb.cancelThenFail onInterrupt cause) ?_
      sub_tac
    · simp only [primKeys]
      exact List.nil_subset _
  | success _ | failure _ | sync _ | suspend _ | withFiber _ | yieldableError _ | iterator _ _
  | onSuccess _ _ | onSuccessConst _ _ | setInterruptible _ | whileLoop _ _ | yieldNowWith _ | async _ _ _ =>
    simp only [Prim.armE] at h
    cases h

theorem resumeValue_keys_with_ambient (hb : KeyBounded nk sk interp ambient)
    (self : FrameFiber ν σ Val Err Defect FiberId Ann) (value : Val) (provided : Option ExitV) :
    stepKeys nk sk (self.resumeValue interp.toPrimInterp value provided).1 ⊆
      ambient ++ (frameKeys nk sk self ++ value.keys ++ optExitKeys provided) := by
  have hg := getCont_keys nk sk self Arm.contA false
  simp only [popKeys] at hg
  unfold FrameFiber.resumeValue
  split
  · next heq =>
    simp only [stepKeys]
    refine List.Subset.trans (optExitKeys_getD_success provided value) ?_
    sub_tac
  · next cause heq =>
    rw [heq] at hg
    simp only [contAnswerKeys, List.nil_append] at hg
    simp only [stepKeys, frameKeys, primKeys, List.nil_append]
    simp only [frameKeys] at hg
    refine List.Subset.trans (List.append_subset.mp hg).2 ?_
    sub_tac
  · next next heq =>
    rw [heq] at hg
    simp only [contAnswerKeys] at hg
    simp only [stepKeys, frameKeys]
    simp only [frameKeys, List.append_subset] at hg
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans hg.1 ?_; sub_tac
    · refine List.Subset.trans hg.2.2 ?_; sub_tac
  · next frame heq =>
    rw [heq] at hg
    simp only [contAnswerKeys, frameKeys, List.append_subset] at hg
    split
    · next next pushed harm =>
      have ha := armA_keys_with_ambient nk sk hb frame value provided next pushed harm
      simp only [List.append_subset] at ha
      simp only [stepKeys, frameKeys, List.flatMap_append]
      refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
      · refine List.Subset.trans ha.1 ?_
        sub_tac using hg.1
      · refine List.Subset.trans ha.2 ?_
        sub_tac using hg.1
      · refine List.Subset.trans hg.2.2 ?_; sub_tac
    · simp only [stepKeys]
      refine List.Subset.trans (optExitKeys_getD_success provided value) ?_
      sub_tac

theorem resumeCause_keys_with_ambient (hb : KeyBounded nk sk interp ambient)
    (self : FrameFiber ν σ Val Err Defect FiberId Ann) (cause : CauseV) (provided : Option ExitV) :
    stepKeys nk sk (self.resumeCause interp.toPrimInterp cause provided).1 ⊆
      ambient ++ (frameKeys nk sk self ++ optExitKeys provided) := by
  have hg := getCont_keys nk sk self Arm.contE true
  simp only [popKeys] at hg
  unfold FrameFiber.resumeCause
  split
  · next heq =>
    simp only [stepKeys]
    refine List.Subset.trans (optExitKeys_getD_failure provided cause) ?_
    sub_tac
  · next cause' heq =>
    rw [heq] at hg
    simp only [contAnswerKeys, List.nil_append] at hg
    simp only [stepKeys, frameKeys, primKeys, List.nil_append]
    simp only [frameKeys] at hg
    refine List.Subset.trans (List.append_subset.mp hg).2 ?_
    sub_tac
  · next next heq =>
    rw [heq] at hg
    simp only [contAnswerKeys] at hg
    simp only [stepKeys, frameKeys]
    simp only [frameKeys, List.append_subset] at hg
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans hg.1 ?_; sub_tac
    · refine List.Subset.trans hg.2.2 ?_; sub_tac
  · next frame heq =>
    rw [heq] at hg
    simp only [contAnswerKeys, frameKeys, List.append_subset] at hg
    split
    · next next pushed harm =>
      have ha := armE_keys_with_ambient nk sk hb frame cause provided next pushed harm
      simp only [List.append_subset] at ha
      simp only [stepKeys, frameKeys, List.flatMap_append]
      refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
      · refine List.Subset.trans ha.1 ?_
        sub_tac using hg.1
      · refine List.Subset.trans ha.2 ?_
        sub_tac using hg.1
      · refine List.Subset.trans hg.2.2 ?_; sub_tac
    · simp only [stepKeys]
      refine List.Subset.trans (optExitKeys_getD_failure provided cause) ?_
      sub_tac

/-- A frame step uses only its input handles and the explicitly allowed callback view. -/
theorem step_keys_with_ambient (hb : KeyBounded nk sk interp ambient) (self : FrameFiber ν σ Val Err Defect FiberId Ann) :
    stepKeys nk sk (self.step interp.toPrimInterp).1 ⊆ ambient ++ frameKeys nk sk self := by
  have hfk : frameKeys nk sk self =
      primKeys nk sk self.current ++ self.stack.flatMap (primKeys nk sk) := rfl
  unfold FrameFiber.step
  split
  · next value heq =>
    refine List.Subset.trans (resumeValue_keys_with_ambient nk sk hb self value _) ?_
    rw [hfk, heq]
    simp only [optExitKeys, exitKeys, primKeys]
    sub_tac
  · next cause heq =>
    refine List.Subset.trans (resumeCause_keys_with_ambient nk sk hb self cause _) ?_
    simp only [optExitKeys, exitKeys, List.append_nil]
    exact List.Subset.refl _
  · next thunk heq =>
    refine List.Subset.trans (resumeValue_keys_with_ambient nk sk hb self _ none) ?_
    rw [hfk, heq]
    simp only [optExitKeys, primKeys, List.append_nil]
    sub_tac using (hb.syncValue thunk)
  · next thunk heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (hb.suspendBody thunk) ?_; sub_tac
    · sub_tac
  · next thunk heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (hb.suspendBody thunk) ?_; sub_tac
    · sub_tac
  · next error heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.nil_append]
    sub_tac
  · next generator cursor heq =>
    rw [hfk, heq]
    split
    · next next pushed harm =>
      have ha := armA_keys_with_ambient nk sk hb _ cursor none next pushed harm
      simp only [optExitKeys, List.append_nil, List.append_subset, primKeys] at ha
      simp only [stepKeys, frameKeys, List.flatMap_append, primKeys]
      refine List.append_subset.mpr ⟨?_, List.append_subset.mpr ⟨?_, ?_⟩⟩
      · refine List.Subset.trans ha.1 ?_; sub_tac
      · refine List.Subset.trans ha.2 ?_; sub_tac
      · sub_tac
    · simp only [stepKeys, frameKeys, heq, primKeys]
      sub_tac
  · next body onValue heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next body saved heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next body onCause heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next body onValue onCause heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next body heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next body finalizer flag heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
    sub_tac
  · next flag heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.nil_append]
    sub_tac
  · next onInterrupt heq =>
    rw [hfk, heq]
    simp only [stepKeys, frameKeys, primKeys, List.nil_append]
    sub_tac
  · next priority heq =>
    simp only [stepKeys]
    sub_tac
  · next register withSignal cancel heq =>
    simp only [stepKeys]
    sub_tac
  · next loop cursor heq =>
    rw [hfk, heq]
    split
    · simp only [stepKeys, frameKeys, primKeys, List.flatMap_cons]
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans (hb.loopBody loop cursor) ?_; sub_tac
      · sub_tac
    · simp only [stepKeys, frameKeys, primKeys]
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans (hb.loopDone loop) ?_; sub_tac
      · sub_tac

/-! ## The machine's operations

Emitting, halting, arming, disarming and replacing a fiber never change the world; replacing
adds at most the new fiber's handles. -/

section Ops

variable {m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores}

theorem keys_emit (ev : List (RunEvent ν σ Val Err Defect FiberId Ann Ctx)) :
    (m.emit ev).keys nk sk = m.keys nk sk := rfl

theorem world_emit (ev : List (RunEvent ν σ Val Err Defect FiberId Ann Ctx)) :
    (m.emit ev).world = m.world := rfl

theorem keys_halt (why : Stuck) : (m.halt why).keys nk sk = m.keys nk sk := rfl

theorem world_halt (why : Stuck) : (m.halt why).world = m.world := rfl

theorem world_arm (owner : FiberId) : (m.arm owner).world = m.world := rfl

theorem keys_arm_subset (owner : FiberId) :
    (m.arm owner).keys nk sk ⊆ Handle.fiber owner :: m.keys nk sk := by
  simp only [RunMachine.keys, RunMachine.arm]
  split
  · sub_tac
  · simp only [List.map_append, List.map_cons, List.map_nil]
    sub_tac

theorem world_disarm (owner : FiberId) : (m.disarm owner).world = m.world := rfl

theorem map_filter_subset {γ ζ : Type} (f : γ → ζ) (p : γ → Bool) (l : List γ) :
    (l.filter p).map f ⊆ l.map f :=
  List.map_subset f fun _ h => (List.mem_filter.mp h).1

theorem flatMap_filter_subset {γ ζ : Type} (f : γ → List ζ) (p : γ → Bool) (l : List γ) :
    (l.filter p).flatMap f ⊆ l.flatMap f := fun x hx => by
  obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, (List.mem_filter.mp ha).1, hxa⟩

theorem keys_disarm_subset (owner : FiberId) : (m.disarm owner).keys nk sk ⊆ m.keys nk sk := by
  simp only [RunMachine.keys, RunMachine.disarm]
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · sub_tac
  · sub_tac
  · refine List.Subset.trans (map_filter_subset Handle.fiber _ m.armed) ?_; sub_tac
  · sub_tac

theorem fibers_update_ids (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.update f).fibers.map RunFiber.id = m.fibers.map RunFiber.id := by
  simp only [RunMachine.update, List.map_map]
  apply List.map_congr_left
  intro g _
  simp only [Function.comp]
  split
  · next h => exact h.symm
  · rfl

theorem world_update (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.update f).world = m.world := by
  unfold RunMachine.world
  rw [fibers_update_ids]
  rfl

theorem world_fibers_append (c : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (n : Nat)
    (ev : List (RunEvent ν σ Val Err Defect FiberId Ann Ctx)) :
    (({ m with fibers := m.fibers ++ [c], nextId := n } : NM ν σ).emit ev).world =
      ⟨m.fibers.map RunFiber.id ++ [c.id], m.state⟩ := by
  simp only [RunMachine.world, RunMachine.emit, List.map_append, List.map_cons, List.map_nil]

theorem keys_fibers_append (c : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (n : Nat)
    (ev : List (RunEvent ν σ Val Err Defect FiberId Ann Ctx)) :
    (({ m with fibers := m.fibers ++ [c], nextId := n } : NM ν σ).emit ev).keys nk sk =
      m.fibers.flatMap (RunFiber.keys nk sk) ++ c.keys nk sk ++ m.races.flatMap (Race.keys nk sk) ++
        m.armed.map Handle.fiber ++ m.state.keys := by
  simp only [RunMachine.keys, RunMachine.emit, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem keys_update_subset (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.update f).keys nk sk ⊆ m.keys nk sk ++ f.keys nk sk := by
  have hf : (m.update f).fibers.flatMap (RunFiber.keys nk sk) ⊆
      m.fibers.flatMap (RunFiber.keys nk sk) ++ f.keys nk sk := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    simp only [RunMachine.update] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    split at hxg
    · exact List.mem_append_right _ hxg
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g0, hg0, hxg⟩)
  have hr : (m.update f).races = m.races := rfl
  have ha : (m.update f).armed = m.armed := rfl
  have hs : (m.update f).state = m.state := rfl
  simp only [RunMachine.keys]
  rw [hr, ha, hs]
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine List.Subset.trans hf ?_; sub_tac
  · sub_tac
  · sub_tac
  · sub_tac

/-- The replaced fiber list's handles, for the membership search. -/
theorem keys_update_fibers_subset (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.update f).fibers.flatMap (RunFiber.keys nk sk) ⊆
      m.fibers.flatMap (RunFiber.keys nk sk) ++ f.keys nk sk := by
  intro x hx
  obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
  simp only [RunMachine.update] at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  split at hxg
  · exact List.mem_append_right _ hxg
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g0, hg0, hxg⟩)

theorem world_eq_of_fields {m' : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores}
    (hf : m'.fibers = m.fibers) (hs : m'.state = m.state) : m'.world = m.world := by
  unfold RunMachine.world
  rw [hf, hs]

theorem world_map_observers (P : Observer → Bool) :
    ({ m with fibers := m.fibers.map fun g => { g with observers := g.observers.filter P } } : NM ν σ).world =
      m.world := by
  unfold RunMachine.world
  simp only [List.map_map]
  try rfl

theorem keys_map_observers_subset (P : Observer → Bool) :
    (m.fibers.map fun g => { g with observers := g.observers.filter P }).flatMap (RunFiber.keys nk sk) ⊆
      m.fibers.flatMap (RunFiber.keys nk sk) := by
  intro x hx
  obtain ⟨g', hg', hxg⟩ := List.mem_flatMap.mp hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
  refine List.mem_flatMap.mpr ⟨g, hg, ?_⟩
  have : ({ g with observers := g.observers.filter P } : RunFiber ν σ Val Err Defect FiberId Ann Ctx).keys nk sk ⊆
      g.keys nk sk := by
    have hobs : (g.observers.filter P).flatMap Observer.keys ⊆ g.observers.flatMap Observer.keys :=
      fun y hy => by
        obtain ⟨o, ho, hyo⟩ := List.mem_flatMap.mp hy
        exact List.mem_flatMap.mpr ⟨o, (List.mem_filter.mp ho).1, hyo⟩
    simp only [RunFiber.keys]
    sub_tac using hobs
  exact this hxg

theorem primKeys_getD (o : Option (Prim ν σ Val Err Defect FiberId Ann)) (body : Prim ν σ Val Err Defect FiberId Ann) :
    primKeys nk sk (o.getD body) ⊆ optPrimKeys nk sk o ++ primKeys nk sk body := by
  cases o with
  | none => exact List.subset_append_right _ _
  | some p => exact List.subset_append_left _ _

theorem fiber?_mem {id : FiberId} {f : RunFiber ν σ Val Err Defect FiberId Ann Ctx}
    (h : m.fiber? id = some f) : f ∈ m.fibers :=
  List.mem_of_find?_eq_some h

theorem fiber?_id {id : FiberId} {f : RunFiber ν σ Val Err Defect FiberId Ann Ctx}
    (h : m.fiber? id = some f) : f.id = id := by
  have := List.find?_some h
  simpa using this

theorem fiber?_keys_subset {id : FiberId} {f : RunFiber ν σ Val Err Defect FiberId Ann Ctx}
    (h : m.fiber? id = some f) : f.keys nk sk ⊆ m.keys nk sk := by
  intro x hx
  simp only [RunMachine.keys]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_flatMap.mpr ⟨f, fiber?_mem h, hx⟩

/-- Captured completed exits contain only handles already collected from the machine.
The fiber identifiers used to select exits are comparison keys, not dereferences. -/
theorem RunMachine.completedExits_keys (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) :
    m.completedExits.flatMap (fun entry => exitKeys entry.2) ⊆ m.keys nk sk := by
  intro handle h
  obtain ⟨entry, hentry, h⟩ := List.mem_flatMap.mp h
  obtain ⟨f, hf, hentry⟩ := List.mem_filterMap.mp hentry
  cases hexit : f.exit with
  | none => simp only [hexit, Option.map_none, reduceCtorEq] at hentry
  | some exit =>
    simp only [hexit, Option.map_some, Option.some.injEq] at hentry
    cases hentry
    have he : optExitKeys f.exit = exitKeys exit := by rw [hexit]; rfl
    have hfk : handle ∈ f.keys nk sk := by
      have hopt : handle ∈ optExitKeys f.exit := he.symm ▸ h
      mem_tac
    have hm : handle ∈ m.fibers.flatMap (RunFiber.keys nk sk) :=
      List.mem_flatMap.mpr ⟨f, hf, hfk⟩
    mem_tac

theorem fiber?_exists {id : FiberId} {f : RunFiber ν σ Val Err Defect FiberId Ann Ctx}
    (h : m.fiber? id = some f) : (Handle.fiber f.id).existsIn m.world = true := by
  show decide (f.id ∈ m.fibers.map RunFiber.id) = true
  exact decide_eq_true (List.mem_map.mpr ⟨f, fiber?_mem h, rfl⟩)

theorem fiber?_id_exists {id : FiberId} {f : RunFiber ν σ Val Err Defect FiberId Ann Ctx}
    (h : m.fiber? id = some f) : (Handle.fiber id).existsIn m.world = true := by
  rw [← fiber?_id h]
  exact fiber?_exists h

theorem world_modify (id : FiberId)
    (k : RunFiber ν σ Val Err Defect FiberId Ann Ctx → RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (m.modify id k).world = m.world := by
  unfold RunMachine.modify
  split
  · rfl
  · exact world_update _

theorem keys_modify_subset (id : FiberId)
    (k : RunFiber ν σ Val Err Defect FiberId Ann Ctx → RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (extra : List Handle) (hk : ∀ g, (k g).keys nk sk ⊆ g.keys nk sk ++ extra) :
    (m.modify id k).keys nk sk ⊆ m.keys nk sk ++ extra := by
  unfold RunMachine.modify
  split
  · sub_tac
  · next f hf =>
    refine List.Subset.trans (keys_update_subset nk sk (k f)) ?_
    have hfm := fiber?_keys_subset nk sk hf
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · sub_tac
    · refine List.Subset.trans (hk f) ?_
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans hfm ?_; sub_tac
      · sub_tac

theorem world_updateRace (r : Race ν σ Val Err Defect FiberId Ann) :
    (m.updateRace r).world = m.world := rfl

theorem keys_updateRace_subset (r : Race ν σ Val Err Defect FiberId Ann) :
    (m.updateRace r).keys nk sk ⊆ m.keys nk sk ++ r.keys nk sk := by
  have hr : (m.updateRace r).races.flatMap (Race.keys nk sk) ⊆
      m.races.flatMap (Race.keys nk sk) ++ r.keys nk sk := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
    simp only [RunMachine.updateRace] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    split at hxg
    · exact List.mem_append_right _ hxg
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g0, hg0, hxg⟩)
  have hf : (m.updateRace r).fibers = m.fibers := rfl
  have ha : (m.updateRace r).armed = m.armed := rfl
  have hs : (m.updateRace r).state = m.state := rfl
  simp only [RunMachine.keys]
  rw [hf, ha, hs]
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · sub_tac
  · refine List.Subset.trans hr ?_; sub_tac
  · sub_tac
  · sub_tac

theorem race?_keys_subset {id : Nat} {r : Race ν σ Val Err Defect FiberId Ann}
    (h : m.race? id = some r) : r.keys nk sk ⊆ m.keys nk sk := by
  intro x hx
  simp only [RunMachine.keys]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  exact List.mem_flatMap.mpr ⟨r, List.mem_of_find?_eq_some h, hx⟩

theorem Dispatcher.insert_keys_subset (priority : Nat) (task : Task ν σ Val Err Defect FiberId Ann) :
    ∀ bs : List (Bucket ν σ Val Err Defect FiberId Ann),
      (Dispatcher.insert priority task bs).flatMap (fun b => b.tasks.flatMap (Task.keys nk sk)) ⊆
        bs.flatMap (fun b => b.tasks.flatMap (Task.keys nk sk)) ++ task.keys nk sk
  | [] => by
    simp only [Dispatcher.insert, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nil_append]
    exact List.Subset.refl _
  | b :: rest => by
    simp only [Dispatcher.insert]
    split
    · simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
      sub_tac
    · split
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        sub_tac
      · simp only [List.flatMap_cons]
        have ih := Dispatcher.insert_keys_subset priority task rest
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · sub_tac
        · refine List.Subset.trans ih ?_; sub_tac

theorem Dispatcher.keys_enqueue_subset (d : Dispatcher ν σ Val Err Defect FiberId Ann)
    (priority : Nat) (task : Task ν σ Val Err Defect FiberId Ann) :
    (d.enqueue priority task).keys nk sk ⊆ d.keys nk sk ++ task.keys nk sk := by
  simp only [Dispatcher.keys, Dispatcher.enqueue]
  exact Dispatcher.insert_keys_subset nk sk priority task d.buckets

theorem Dispatcher.keys_empty : (Dispatcher.empty : Dispatcher ν σ Val Err Defect FiberId Ann).keys nk sk = [] := rfl

theorem keys_park (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (p : Pending ν Val Err Defect FiberId Ann) :
    (f.park p).keys nk sk ⊆ f.keys nk sk ++ p.keys nk := by
  simp only [RunFiber.keys, RunFiber.park, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  sub_tac

end Ops

/-! ## The helpers keep their handles

Each helper's receipt: the world grew, and the handles the helper leaves behind (its
machine's, its fiber's, its commands') exist in the world it leaves. -/

theorem make_keys_subset (id : FiberId) (program : Prim ν σ Val Err Defect FiberId Ann) (flag : Bool)
    (budget : Nat × Bool) (ctx : Ctx) :
    (RunFiber.make id program flag budget ctx : RunFiber ν σ Val Err Defect FiberId Ann Ctx).keys nk sk ⊆
      primKeys nk sk program ++ ctx.keys := by
  show primKeys nk sk program ++ [] ++ [] ++ [] ++ [] ++ [] ++ [] ++ [] ++ ctx.keys ⊆ _
  simp only [List.append_nil]
  exact List.Subset.refl _

theorem keys_set_observers (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (obs : List Observer) :
    ({ f with observers := obs } : RunFiber ν σ Val Err Defect FiberId Ann Ctx).keys nk sk ⊆
      f.keys nk sk ++ obs.flatMap Observer.keys := by
  simp only [RunFiber.keys]
  sub_tac

theorem spawnChild_keys_subset (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (parent : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (options : Supervision.ForkOptions) :
    (spawnChild interp m parent program options).keys nk sk ⊆
      Handle.fiber parent.id :: primKeys nk sk program ++ parent.context.keys := by
  unfold spawnChild
  try dsimp only
  refine List.Subset.trans (make_keys_subset nk sk _ _ _ _ _) ?_
  sub_tac

theorem spawn_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (parent : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (options : Supervision.ForkOptions)
    (hm : MintedIn m (Handle.fiber parent.id :: m.keys nk sk ++ parent.keys nk sk ++ primKeys nk sk program)) :
    m.world.le (spawn interp m parent program options).1.world ∧
      MintedIn (spawn interp m parent program options).1
        (Handle.fiber (spawn interp m parent program options).2.2 ::
          (spawn interp m parent program options).1.keys nk sk ++
          (spawn interp m parent program options).2.1.keys nk sk) := by
  rw [spawn_eq]
  have hcid : (spawnChild interp m parent program options).id = ⟨m.nextId⟩ :=
    (spawnChild_fields interp m parent program options).1
  have hle : m.world.le ⟨m.fibers.map RunFiber.id ++ [⟨m.nextId⟩], m.state⟩ :=
    ⟨fun id h => List.mem_append_left _ h, Stores.le_refl _⟩
  refine ⟨by rw [world_fibers_append, hcid]; exact hle, ?_⟩
  simp only [MintedIn]
  rw [world_fibers_append, hcid]
  have hchild : (Handle.fiber ⟨m.nextId⟩).existsIn ⟨m.fibers.map RunFiber.id ++ [⟨m.nextId⟩], m.state⟩ = true :=
    decide_eq_true (List.mem_append_right _ (List.mem_singleton_self _))
  have hsc := spawnChild_keys_subset nk sk interp m parent program options
  refine Ok_of_subset ?_ (Ok_cons.mpr ⟨hchild, Ok_append.mpr ⟨Ok_mono hle hm, Ok_of_subset hsc
    (Ok_of_subset (by simp only [RunFiber.keys]; sub_tac) (Ok_mono hle hm))⟩⟩)
  rw [keys_fibers_append]
  sub_tac

theorem start_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (parent : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (child : FiberId) (immediately : Bool)
    (hm : MintedIn m (Handle.fiber parent.id :: Handle.fiber child :: m.keys nk sk ++ parent.keys nk sk)) :
    m.world.le (start m parent child immediately).1.world ∧
      MintedIn (start m parent child immediately).1
        ((start m parent child immediately).1.keys nk sk ++
          (start m parent child immediately).2.1.keys nk sk ++
          cmdsKeys nk sk (start m parent child immediately).2.2) := by
  unfold start
  split
  · refine ⟨World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    simp only [cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil]
    sub_tac
  · refine ⟨by rw [world_emit, world_arm]; exact World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    rw [keys_emit]
    simp only [cmdsKeys, List.flatMap_nil, List.append_nil]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (keys_arm_subset nk sk parent.id) ?_; sub_tac
    · simp only [RunFiber.keys]
      refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
      · sub_tac
      · refine List.Subset.trans (Dispatcher.keys_enqueue_subset nk sk _ _ _) ?_
        simp only [Task.keys]
        sub_tac
      · sub_tac

theorem interruptRecord_keys_subset (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (interruptor : Option FiberId) (extra : ReasonAnnotations Ann)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    (interruptRecord interp interruptor extra f).1.keys nk sk ⊆ f.keys nk sk := by
  unfold interruptRecord
  try dsimp only
  (repeat' split) <;> first
    | exact List.Subset.refl _
    | (simp only [RunFiber.keys, frameKeys, primKeys, List.flatMap_nil, List.nil_append]
       sub_tac)

theorem interruptEach_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (who : FiberId) (extra : ReasonAnnotations Ann) (targets : List FiberId) :
    ∀ acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann),
      MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2) →
      acc.1.world.le (interruptEach interp who extra targets acc).1.world ∧
        MintedIn (interruptEach interp who extra targets acc).1
          ((interruptEach interp who extra targets acc).1.keys nk sk ++
            cmdsKeys nk sk (interruptEach interp who extra targets acc).2) := by
  induction targets with
  | nil => intro acc hm; exact ⟨World.le_refl _, hm⟩
  | cons t ts ih =>
    intro acc hm
    rw [interruptEach_cons]
    split
    · exact ih acc hm
    · next g hg =>
      try dsimp only
      have hstep : MintedIn ((acc.1.update (interruptRecord interp (some who) extra g).1).emit
            [RunEvent.interruptRecorded (some who) t])
          (((acc.1.update (interruptRecord interp (some who) extra g).1).emit
            [RunEvent.interruptRecorded (some who) t]).keys nk sk ++
            cmdsKeys nk sk (acc.2 ++ if (interruptRecord interp (some who) extra g).2 then
              [Cmd.evaluate t] else [])) := by
        simp only [MintedIn]
        rw [world_emit, world_update]
        refine Ok_of_subset ?_ hm
        rw [keys_emit]
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans (keys_update_subset nk sk _) ?_
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · sub_tac
          · refine List.Subset.trans (interruptRecord_keys_subset nk sk interp _ _ g) ?_
            refine List.Subset.trans (fiber?_keys_subset nk sk hg) ?_
            sub_tac
        · simp only [cmdsKeys, List.flatMap_append]
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · sub_tac
          · split <;> simp only [List.flatMap_cons, List.flatMap_nil, Cmd.keys] <;> sub_tac
      obtain ⟨hle, hok⟩ := ih ((acc.1.update (interruptRecord interp (some who) extra g).1).emit
        [RunEvent.interruptRecorded (some who) t],
        acc.2 ++ if (interruptRecord interp (some who) extra g).2 then [Cmd.evaluate t] else []) hstep
      rw [world_emit, world_update] at hle
      exact ⟨hle, hok⟩

theorem countdownWalk_keys (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) :
    ∀ (targets : List FiberId) (exits : List ExitV),
      (countdownWalk m targets exits).1.flatMap exitKeys ⊆ exits.flatMap exitKeys ++ m.keys nk sk ∧
      (∀ t rest, (countdownWalk m targets exits).2 = some (t, rest) → t ∈ targets ∧ rest ⊆ targets)
  | [], exits => by
    simp only [countdownWalk]
    exact ⟨List.subset_append_left _ _, fun _ _ h => nomatch h⟩
  | t :: rest, exits => by
    simp only [countdownWalk]
    split
    · refine (countdownWalk_keys m rest exits).imp id fun h t' rest' h' => ?_
      obtain ⟨h1, h2⟩ := h t' rest' h'
      exact ⟨List.mem_cons_of_mem _ h1, List.subset_cons_of_subset _ h2⟩
    · next g hg =>
      split
      · next exit hexit =>
        refine (countdownWalk_keys m rest (exits ++ [exit])).imp (fun h => ?_) fun h t' rest' h' => ?_
        · refine List.Subset.trans h ?_
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
          · sub_tac
          · have hfk := fiber?_keys_subset nk sk hg
            simp only [RunFiber.keys, hexit, optExitKeys] at hfk
            refine List.subset_append_of_subset_right _ ?_
            refine List.Subset.trans ?_ hfk
            sub_tac
          · sub_tac
        · obtain ⟨h1, h2⟩ := h t' rest' h'
          exact ⟨List.mem_cons_of_mem _ h1, List.subset_cons_of_subset _ h2⟩
      · refine ⟨List.subset_append_left _ _, fun t' rest' h' => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact ⟨List.mem_cons_self, List.subset_cons_of_subset _ (List.Subset.refl _)⟩

theorem resumePrim_keys (hb : KeyBounded nk sk interp ambient) (resumeWith : Resume ν) (exits : List ExitV) :
    primKeys nk sk (countdownPark.resumePrim (core := frameCore) interp resumeWith exits) ⊆
      resumeWith.keys nk ++ exits.flatMap exitKeys := by
  cases resumeWith with
  | exitsValue =>
    simp only [countdownPark.resumePrim, FiberCore.success, primKeys, Resume.keys, List.nil_append]
    exact hb.exitsValue exits
  | void =>
    simp only [countdownPark.resumePrim, FiberCore.success, primKeys, Resume.keys, List.nil_append,
      hb.voidValue]
    exact List.nil_subset _
  | continueWith name =>
    simp only [countdownPark.resumePrim, FiberCore.success, FiberCore.onSuccess, primKeys, Resume.keys]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (hb.exitsValue exits) ?_; sub_tac
    · sub_tac

theorem countdownPark_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (targets : List FiberId) (resumeWith : Resume ν)
    (failFast : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ targets.map Handle.fiber ++
      resumeWith.keys nk)) :
    m.world.le (countdownPark interp m f targets resumeWith failFast).1.world ∧
      MintedIn (countdownPark interp m f targets resumeWith failFast).1
        ((countdownPark interp m f targets resumeWith failFast).1.keys nk sk ++
          (countdownPark interp m f targets resumeWith failFast).2.1.keys nk sk) := by
  unfold countdownPark
  have hwalk := countdownWalk_keys nk sk { m with nextToken := m.nextToken + 1 } targets []
  have hkeq : ({ m with nextToken := m.nextToken + 1 } : NM ν σ).keys nk sk = m.keys nk sk := rfl
  have hweq : ({ m with nextToken := m.nextToken + 1 } : NM ν σ).world = m.world := rfl
  try dsimp only
  split
  · next exits hwalk' =>
    rw [hwalk'] at hwalk
    simp only [List.flatMap_nil, List.nil_append, hkeq] at hwalk
    refine ⟨World.le_refl _, ?_⟩
    have hres : Ok m.world
        (primKeys nk sk (countdownPark.resumePrim (core := frameCore) interp resumeWith exits)) := by
      refine Ok_of_subset (resumePrim_keys nk sk hb resumeWith exits) ?_
      exact Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hm,
        Ok_of_subset hwalk.1 (Ok_of_subset (by sub_tac) hm)⟩
    simp only [MintedIn, hweq]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hres⟩)
    rw [hkeq]
    simp only [RunFiber.keys, frameKeys]
    sub_tac
  · next exits target remaining hwalk' =>
    rw [hwalk'] at hwalk
    simp only [List.flatMap_nil, List.nil_append, hkeq] at hwalk
    obtain ⟨hexits, hrest⟩ := hwalk
    obtain ⟨htarget, hremaining⟩ := hrest target remaining rfl
    refine ⟨by rw [world_emit, world_modify]; exact World.le_refl _, ?_⟩
    have hname : nk (interp.cancelName interp.parkCancelName f.id m.nextToken) ⊆ [Handle.fiber f.id] := by
      refine List.Subset.trans (hb.cancelName _ _ _) ?_
      rw [hb.parkCancelName]
      exact List.Subset.refl _
    have hall : Ok m.world (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ targets.map Handle.fiber ++
        resumeWith.keys nk ++ (Handle.fiber target :: remaining.map Handle.fiber ++ exits.flatMap exitKeys ++
        nk (interp.cancelName interp.parkCancelName f.id m.nextToken))) := by
      refine Ok_append.mpr ⟨hm, ?_⟩
      refine Ok_cons.mpr ⟨?_, Ok_append.mpr ⟨Ok_append.mpr ⟨?_, ?_⟩, ?_⟩⟩
      · have : Handle.fiber target ∈ targets.map Handle.fiber := List.mem_map.mpr ⟨target, htarget, rfl⟩
        exact hm _ (by mem_tac)
      · exact Ok_of_subset (List.map_subset Handle.fiber hremaining) (Ok_of_subset (by sub_tac) hm)
      · exact Ok_of_subset hexits (Ok_of_subset (by sub_tac) hm)
      · exact Ok_of_subset hname (Ok_of_subset (by sub_tac) hm)
    simp only [MintedIn]
    rw [world_emit, world_modify, hweq]
    refine Ok_of_subset ?_ hall
    rw [keys_emit]
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (keys_modify_subset nk sk target _ [Handle.fiber f.id] fun g => ?_) ?_
      · simp only [RunFiber.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Observer.keys,
          List.append_nil]
        sub_tac
      · rw [hkeq]; sub_tac
    · refine List.Subset.trans (keys_park nk sk _ _) ?_
      simp only [RunFiber.keys, frameKeys, List.flatMap_cons, primKeys, Pending.keys, Option.map,
        Option.toList]
      sub_tac

theorem launchEntrant_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (host : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (program : Prim ν σ Val Err Defect FiberId Ann)
    (hm : MintedIn m (Handle.fiber host.id :: m.keys nk sk ++ host.keys nk sk ++ primKeys nk sk program)) :
    m.world.le (launchEntrant interp raceId m host program).1.world ∧
      MintedIn (launchEntrant interp raceId m host program).1
        (Handle.fiber (launchEntrant interp raceId m host program).2 ::
          (launchEntrant interp raceId m host program).1.keys nk sk) := by
  unfold launchEntrant
  obtain ⟨hle, hsp⟩ := spawn_minted nk sk interp m host program
    ⟨true, true, Supervision.MaskMode.interruptible⟩ hm
  exact ⟨hle, Ok_of_subset (by sub_tac) hsp⟩

theorem linkScope_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann)
    (hm : MintedIn m (m.keys nk sk)) :
    m.world.le (linkScope interp m mode scope target interruptor extra).1.world ∧
      MintedIn (linkScope interp m mode scope target interruptor extra).1
        ((linkScope interp m mode scope target interruptor extra).1.keys nk sk ++
          cmdsKeys nk sk (linkScope interp m mode scope target interruptor extra).2) := by
  unfold linkScope
  split
  · refine ⟨by rw [world_halt]; exact World.le_refl _, ?_⟩
    simp only [MintedIn, world_halt, keys_halt, cmdsKeys, List.flatMap_nil, List.append_nil]
    exact hm
  · next hstatus =>
    split
    · refine ⟨by rw [world_halt]; exact World.le_refl _, ?_⟩
      simp only [MintedIn, world_halt, keys_halt, cmdsKeys, List.flatMap_nil, List.append_nil]
      exact hm
    · next t ht =>
      refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit, world_update]
      refine Ok_of_subset ?_ hm
      rw [keys_emit]
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans (keys_update_subset nk sk _) ?_
        refine List.append_subset.mpr ⟨List.Subset.refl _, ?_⟩
        refine List.Subset.trans (interruptRecord_keys_subset nk sk interp _ _ t) ?_
        exact fiber?_keys_subset nk sk ht
      · split <;> simp only [cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys] <;> exact List.nil_subset _
  · next hstatus =>
    split
    · refine ⟨by rw [world_halt]; exact World.le_refl _, ?_⟩
      simp only [MintedIn, world_halt, keys_halt, cmdsKeys, List.flatMap_nil, List.append_nil]
      exact hm
    · next t ht =>
      split
      · exact ⟨World.le_refl _, by simpa [cmdsKeys] using hm⟩
      · split
        · refine ⟨by rw [world_halt]; exact World.le_refl _, ?_⟩
          simp only [MintedIn, world_halt, keys_halt, cmdsKeys, List.flatMap_nil, List.append_nil]
          exact hm
        · next state key hstate =>
          have htid : (Handle.fiber target).existsIn m.world = true := fiber?_id_exists ht
          have hsk : Ok ⟨m.fibers.map RunFiber.id, m.state⟩ (Handle.fiber target :: m.state.keys) := by
            refine Ok_cons.mpr ⟨htid, ?_⟩
            refine Ok_of_subset ?_ hm
            simp only [RunMachine.keys]
            sub_tac
          obtain ⟨hsle, hsok⟩ := hb.scopeLinkFiber mode scope target m.state state key _ hstate hsk
          have hle : m.world.le ({ m with state := state } : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores).world :=
            ⟨fun _ h => h, hsle⟩
          refine ⟨by rw [world_emit, world_modify]; exact hle, ?_⟩
          simp only [MintedIn]
          rw [world_emit, world_modify]
          have hscope : (Handle.scope scope).existsIn ({ m with state := state } : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores).world = true := by
            have h0 : (m.state.scopes.entryAt scope).isSome = true :=
              hb.scopeStatus scope m.state (by rw [hstatus]; rfl)
            simp only [Handle.existsIn, RunMachine.world]
            exact hsle.2.2.1 scope h0
          have hall : Ok ({ m with state := state } : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores).world
              (Handle.scope scope :: m.keys nk sk ++ state.keys) :=
            Ok_cons.mpr ⟨hscope, Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩⟩
          refine Ok_of_subset ?_ hall
          rw [keys_emit]
          simp only [cmdsKeys, List.flatMap_nil, List.append_nil]
          refine List.Subset.trans (keys_modify_subset nk sk target _ [Handle.scope scope] fun g => ?_) ?_
          · simp only [RunFiber.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Observer.keys,
              List.append_nil]
            sub_tac
          · simp only [RunMachine.keys]
            sub_tac

theorem injectYield_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) (h : injectYield m f yielding = some it)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk)) :
    m.world.le it.machine.world ∧ MintedIn it.machine (iterKeys nk sk it) := by
  unfold injectYield at h
  split at h
  · cases h
    simp only [iterKeys]
    refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit]
    refine Ok_of_subset ?_ hm
    rw [keys_emit]
    simp only [cmdsKeys, List.flatMap_nil, List.append_nil, Outcome.keys,
      RunFiber.keys, frameKeys, primKeys, List.nil_append]
    sub_tac
  · cases h

/-! ### The exit path -/

theorem raceComplete_live_subset (s : Supervision.RaceAllState Val Err Defect FiberId Ann)
    (child : FiberId) (exit : ExitV) :
    (Supervision.raceComplete s child exit).live ⊆ s.live := by
  unfold Supervision.raceComplete
  split
  · (repeat' split) <;> exact fun _ h => (List.mem_filter.mp h).1
  · exact List.Subset.refl _

theorem raceComplete_accepted_keys (s : Supervision.RaceAllState Val Err Defect FiberId Ann)
    (child : FiberId) (exit : ExitV) :
    optExitKeys (Supervision.raceComplete s child exit).accepted ⊆
      optExitKeys s.accepted ++ exitKeys exit := by
  unfold Supervision.raceComplete
  split
  · split
    · exact List.subset_append_left _ _
    · split
      · simp only [optExitKeys, exitKeys]
        exact List.subset_append_right _ _
      · split
        · simp only [optExitKeys, exitKeys]
          exact List.nil_subset _
        · exact List.subset_append_left _ _
  · exact List.subset_append_left _ _

theorem race_state_keys_subset (r : Race ν σ Val Err Defect FiberId Ann)
    (state : Supervision.RaceAllState Val Err Defect FiberId Ann) (settled : Bool) (extra : List Handle)
    (hlive : state.live ⊆ r.state.live) (hacc : optExitKeys state.accepted ⊆ optExitKeys r.state.accepted ++ extra) :
    ({ r with state := state, settled := settled } : Race ν σ Val Err Defect FiberId Ann).keys nk sk ⊆
      r.keys nk sk ++ extra := by
  simp only [Race.keys]
  refine List.cons_subset.mpr ⟨List.mem_cons_self, ?_⟩
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
  · refine List.Subset.trans (List.map_subset Handle.fiber hlive) ?_; sub_tac
  · refine List.Subset.trans hacc ?_; sub_tac
  · sub_tac

theorem pending_map_keys_subset (ps : List (Pending ν Val Err Defect FiberId Ann)) (token : Nat)
    (g : Pending ν Val Err Defect FiberId Ann → Pending ν Val Err Defect FiberId Ann) (extra : List Handle)
    (hg : ∀ q, (g q).keys nk ⊆ q.keys nk ++ extra) :
    (ps.map fun q => if q.token = token then g q else q).flatMap (Pending.keys nk) ⊆
      ps.flatMap (Pending.keys nk) ++ extra := by
  intro x hx
  obtain ⟨q', hq', hxq⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  split at hxq
  · rcases List.mem_append.mp (hg q hxq) with h | h
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, hq, h⟩)
    · exact List.mem_append_right _ h
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, hq, hxq⟩)

theorem pending_mem_keys_subset {ps : List (Pending ν Val Err Defect FiberId Ann)}
    {p : Pending ν Val Err Defect FiberId Ann} (h : p ∈ ps) :
    p.keys nk ⊆ ps.flatMap (Pending.keys nk) :=
  fun _ hx => List.mem_flatMap.mpr ⟨p, h, hx⟩

/-- The receipt of firing one observer: the world grew, and the machine's handles and the
commands' handles exist afterwards. One lemma per observer shape, then the dispatch. -/
def FiredMinted (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (r : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann)) : Prop :=
  acc.1.world.le r.1.world ∧ MintedIn r.1 (r.1.keys nk sk ++ cmdsKeys nk sk r.2)

theorem fireObserver_resumeAwait_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.resumeAwait waiter token mode).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.resumeAwait waiter token mode)) := by
    unfold FiredMinted
    simp only [fireObserver]
    refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit]
    have hev : Ok acc.1.world (primKeys nk sk (interp.exitValue exit mode)) :=
      Ok_of_subset (hb.exitValue exit mode) (Ok_of_subset (by sub_tac) hm)
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hev⟩)
    rw [keys_emit]
    sub_tac
theorem fireObserver_untrackChild_minted (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (parent : FiberId)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.untrackChild parent).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.untrackChild parent)) := by
    unfold FiredMinted
    simp only [fireObserver]
    refine ⟨by rw [world_modify, world_emit]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_modify, world_emit]
    refine Ok_of_subset ?_ hm
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans (keys_modify_subset nk sk parent _ [] fun g => ?_) ?_
      · sub_tac using (map_filter_subset Handle.fiber _ g.children)
      · rw [keys_emit]; sub_tac
    · sub_tac
theorem fireObserver_dropScopeFinalizer_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (scope key : Nat)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.dropScopeFinalizer scope key).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.dropScopeFinalizer scope key)) := by
    unfold FiredMinted
    simp only [fireObserver]
    split
    · refine ⟨by rw [world_halt, world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_halt, world_emit]
      refine Ok_of_subset ?_ hm
      rw [keys_halt, keys_emit]
      sub_tac
    · next state hstate =>
      have hsk : Ok ⟨acc.1.fibers.map RunFiber.id, acc.1.state⟩ acc.1.state.keys :=
        Ok_of_subset (by sub_tac) hm
      obtain ⟨hsle, hsok⟩ := hb.dropFinalizer scope key acc.1.state state _ hstate hsk
      have hle : acc.1.world.le ({ acc.1.emit [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)]
          with state := state } : NM ν σ).world := ⟨fun _ h => h, hsle⟩
      refine ⟨hle, ?_⟩
      simp only [MintedIn]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩)
      simp only [RunMachine.keys, RunMachine.emit]
      sub_tac
/-- The countdown's last observer fired: the walk found no live target, the waiter's park is
closed and its resume is owed. `R` is the machine and commands after the optional fail-fast
interruption; `hbase` is everything known to exist in that world. -/
theorem countdown_done_minted (hb : KeyBounded nk sk interp ambient)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (waiter : FiberId) (token : Nat) (exit : ExitV) (w : RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (p : Pending ν Val Err Defect FiberId Ann)
    (R : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (exits : List ExitV) (hle : acc.1.world.le R.1.world)
    (hbase : Ok R.1.world (R.1.keys nk sk ++ cmdsKeys nk sk R.2 ++ acc.1.keys nk sk ++
      cmdsKeys nk sk acc.2 ++ exitKeys exit ++ [Handle.fiber waiter] ++ p.keys nk ++ w.keys nk sk))
    (hex1 : exits.flatMap exitKeys ⊆ (p.collected ++ [exit]).flatMap exitKeys ++ R.1.keys nk sk) :
    FiredMinted nk sk acc
      (R.1.update { w with pending := w.pending.map fun q =>
          if q.token = token then { q with waitingOn := none, remaining := [], collected := exits } else q },
        acc.2 ++ R.2 ++ [Cmd.resume waiter token
          (countdownPark.resumePrim (core := frameCore) interp p.resumeWith exits)]) := by
  unfold FiredMinted
  have hcol : (p.collected ++ [exit]).flatMap exitKeys ⊆ p.keys nk ++ exitKeys exit := by
    simp only [Pending.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    sub_tac
  have hex : exits.flatMap exitKeys ⊆ p.keys nk ++ exitKeys exit ++ R.1.keys nk sk := by
    refine List.Subset.trans hex1 ?_
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans hcol ?_; sub_tac
    · sub_tac
  have hexits : Ok R.1.world (exits.flatMap exitKeys) :=
    Ok_of_subset hex (Ok_of_subset (by sub_tac) hbase)
  have hres : Ok R.1.world
      (primKeys nk sk (countdownPark.resumePrim (core := frameCore) interp p.resumeWith exits)) :=
    Ok_of_subset (resumePrim_keys nk sk hb p.resumeWith exits)
      (Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hbase, hexits⟩)
  have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨hbase, hexits⟩, hres⟩
  have hpm := pending_map_keys_subset nk w.pending token
    (fun q => { q with waitingOn := none, remaining := [], collected := exits })
    (exits.flatMap exitKeys) (fun q => by sub_tac)
  refine ⟨by rw [world_update]; exact hle, ?_⟩
  simp only [MintedIn]
  rw [world_update]
  refine Ok_of_subset ?_ hall
  refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _)
    (List.append_subset.mpr ⟨by sub_tac, ?_⟩), by sub_tac⟩
  sub_tac using hpm

/-- The countdown moves to its next live target: that target gets the observer and the
waiter's park records where the walk stands. -/
theorem countdown_next_minted
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (waiter : FiberId) (token : Nat) (exit : ExitV) (w : RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (p : Pending ν Val Err Defect FiberId Ann)
    (R : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (exits : List ExitV) (next : FiberId) (rest : List FiberId) (hle : acc.1.world.le R.1.world)
    (hbase : Ok R.1.world (R.1.keys nk sk ++ cmdsKeys nk sk R.2 ++ acc.1.keys nk sk ++
      cmdsKeys nk sk acc.2 ++ exitKeys exit ++ [Handle.fiber waiter] ++ p.keys nk ++ w.keys nk sk))
    (hex1 : exits.flatMap exitKeys ⊆ (p.collected ++ [exit]).flatMap exitKeys ++ R.1.keys nk sk)
    (hnext : next ∈ p.remaining) (hrest : rest ⊆ p.remaining) :
    FiredMinted nk sk acc
      ((R.1.modify next fun g => { g with observers := g.observers ++ [Observer.countdown waiter token] }).update
        { w with pending := w.pending.map fun q =>
          if q.token = token then { q with waitingOn := some next, remaining := rest, collected := exits } else q },
        acc.2 ++ R.2) := by
  unfold FiredMinted
  have hcol : (p.collected ++ [exit]).flatMap exitKeys ⊆ p.keys nk ++ exitKeys exit := by
    simp only [Pending.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    sub_tac
  have hex : exits.flatMap exitKeys ⊆ p.keys nk ++ exitKeys exit ++ R.1.keys nk sk := by
    refine List.Subset.trans hex1 ?_
    refine List.append_subset.mpr ⟨?_, ?_⟩
    · refine List.Subset.trans hcol ?_; sub_tac
    · sub_tac
  have hexits : Ok R.1.world (exits.flatMap exitKeys) :=
    Ok_of_subset hex (Ok_of_subset (by sub_tac) hbase)
  have hrem : Ok R.1.world (p.remaining.map Handle.fiber) := Ok_of_subset (by sub_tac) hbase
  have hnextk : Ok R.1.world [Handle.fiber next] :=
    Ok_of_subset (List.cons_subset.mpr ⟨List.mem_map.mpr ⟨next, hnext, rfl⟩, List.nil_subset _⟩) hrem
  have hrestk : Ok R.1.world (rest.map Handle.fiber) :=
    Ok_of_subset (List.map_subset Handle.fiber hrest) hrem
  have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨hbase, hexits⟩, hnextk⟩, hrestk⟩
  have hpm := pending_map_keys_subset nk w.pending token
    (fun q => { q with waitingOn := some next, remaining := rest, collected := exits })
    (Handle.fiber next :: rest.map Handle.fiber ++ exits.flatMap exitKeys) (fun q => by sub_tac)
  have hM2 := keys_modify_subset nk sk (m := R.1) next
    (fun g => { g with observers := g.observers ++ [Observer.countdown waiter token] })
    [Handle.fiber waiter] (fun g => by sub_tac)
  have hM2w := world_modify (m := R.1) next
    (fun g => { g with observers := g.observers ++ [Observer.countdown waiter token] })
  generalize hM2def : R.1.modify next
    (fun g => { g with observers := g.observers ++ [Observer.countdown waiter token] }) = M2 at hM2 hM2w ⊢
  refine ⟨by rw [world_update, hM2w]; exact hle, ?_⟩
  simp only [MintedIn]
  rw [world_update, hM2w]
  refine Ok_of_subset ?_ hall
  refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _)
    (List.append_subset.mpr ⟨List.Subset.trans hM2 (by sub_tac), ?_⟩), by sub_tac⟩
  sub_tac using hpm

theorem fireObserver_countdown_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (waiter : FiberId) (token : Nat)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.countdown waiter token).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.countdown waiter token)) := by
    unfold FiredMinted
    simp only [fireObserver]
    split
    · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      refine Ok_of_subset ?_ hm
      rw [keys_emit]
      sub_tac
    · next w hw =>
      split
      · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
        simp only [MintedIn]
        rw [world_emit]
        refine Ok_of_subset ?_ hm
        rw [keys_emit]
        sub_tac
      · next p hp =>
        have hpw : p ∈ w.pending := List.mem_of_find?_eq_some hp
        have hpk : p.keys nk ⊆ acc.1.keys nk sk := by
          refine List.Subset.trans (pending_mem_keys_subset nk hpw) ?_
          refine List.Subset.trans ?_ (fiber?_keys_subset nk sk hw)
          simp only [RunFiber.keys]
          sub_tac
        have hwid : (Handle.fiber waiter).existsIn acc.1.world = true := fiber?_id_exists hw
        -- the machine and commands after the optional fail-fast interruption
        have hR : ∀ R : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann),
            (R = interruptEach interp waiter (interp.stackAnnotations waiter) p.remaining
              (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], []) ∨
             R = (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], [])) →
            acc.1.world.le R.1.world ∧ MintedIn R.1 (R.1.keys nk sk ++ cmdsKeys nk sk R.2) := by
          intro R hR
          rcases hR with rfl | rfl
          · have := interruptEach_minted nk sk interp waiter (interp.stackAnnotations waiter) p.remaining
              (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], [])
              (by simp only [MintedIn]; rw [world_emit]; refine Ok_of_subset ?_ hm; rw [keys_emit]; sub_tac)
            rw [world_emit] at this
            exact this
          · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
            simp only [MintedIn]
            rw [world_emit]
            refine Ok_of_subset ?_ hm
            rw [keys_emit]
            sub_tac
        generalize hRdef : (if p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess then
            interruptEach interp waiter (interp.stackAnnotations waiter) p.remaining
              (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], [])
          else (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)], [])) = R
        have hRok : acc.1.world.le R.1.world ∧ MintedIn R.1 (R.1.keys nk sk ++ cmdsKeys nk sk R.2) := by
          refine hR R ?_
          rw [← hRdef]
          split
          · exact Or.inl rfl
          · exact Or.inr rfl
        obtain ⟨hle, hRm⟩ := hRok
        have hwalk := countdownWalk_keys nk sk R.1 p.remaining (p.collected ++ [exit])
        have hwk : w.keys nk sk ⊆ acc.1.keys nk sk := fiber?_keys_subset nk sk hw
        -- everything known to exist in the world after the interruption, as one bag
        have hbase : Ok R.1.world (R.1.keys nk sk ++ cmdsKeys nk sk R.2 ++ acc.1.keys nk sk ++
            cmdsKeys nk sk acc.2 ++ exitKeys exit ++ [Handle.fiber waiter] ++ p.keys nk ++ w.keys nk sk) :=
          Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr
            ⟨hRm, Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩,
            Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩,
            Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩,
            Ok_mono hle (Ok_cons.mpr ⟨hwid, Ok_nil _⟩)⟩,
            Ok_mono hle (Ok_of_subset hpk (Ok_of_subset (by sub_tac) hm))⟩,
            Ok_mono hle (Ok_of_subset hwk (Ok_of_subset (by sub_tac) hm))⟩
        split
        · next exits hwalk' =>
          rw [hwalk'] at hwalk
          exact countdown_done_minted nk sk hb acc waiter token exit w p R exits hle hbase hwalk.1
        · next exits next rest hwalk' =>
          rw [hwalk'] at hwalk
          obtain ⟨hnext, hrest⟩ := hwalk.2 next rest rfl
          exact countdown_next_minted nk sk acc waiter token exit w p R exits next rest hle hbase hwalk.1
            hnext hrest

theorem fireObserver_raceCallback_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (raceId : Nat)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.raceCallback raceId).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.raceCallback raceId)) := by
    unfold FiredMinted
    simp only [fireObserver]
    split
    · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      refine Ok_of_subset ?_ hm
      rw [keys_emit]
      sub_tac
    · next race hrace =>
      have hrk : race.keys nk sk ⊆ acc.1.keys nk sk := race?_keys_subset nk sk hrace
      have hrk' : ({ race with state := Supervision.raceComplete race.state id exit } :
          Race ν σ Val Err Defect FiberId Ann).keys nk sk ⊆ race.keys nk sk ++ exitKeys exit :=
        race_state_keys_subset nk sk race _ race.settled (exitKeys exit) (raceComplete_live_subset _ _ _)
          (raceComplete_accepted_keys _ _ _)
      have hrk'' : ({ race with state := Supervision.raceComplete race.state id exit, settled := true } :
          Race ν σ Val Err Defect FiberId Ann).keys nk sk ⊆ race.keys nk sk ++ exitKeys exit :=
        race_state_keys_subset nk sk race _ true (exitKeys exit) (raceComplete_live_subset _ _ _)
          (raceComplete_accepted_keys _ _ _)
      split
      · next accepted hacc hsettled =>
        refine ⟨by rw [world_emit, world_updateRace, world_updateRace, world_emit]; exact World.le_refl _, ?_⟩
        simp only [MintedIn]
        rw [world_emit, world_updateRace, world_updateRace, world_emit]
        have hsettle : primKeys nk sk (interp.raceSettle raceId
            (Supervision.raceComplete race.state id exit).cleanupNeeded accepted) ⊆
            race.keys nk sk ++ exitKeys exit := by
          refine List.Subset.trans (hb.raceSettle _ _ _) ?_
          have := raceComplete_accepted_keys race.state id exit
          rw [hacc] at this
          simp only [optExitKeys] at this
          refine List.Subset.trans this ?_
          simp only [Race.keys]; sub_tac
        have hall : Ok acc.1.world (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++ race.keys nk sk) :=
          Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hm, Ok_of_subset hrk (Ok_of_subset (by sub_tac) hm)⟩
        refine Ok_of_subset ?_ hall
        rw [keys_emit]
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans (keys_updateRace_subset nk sk _) ?_
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · refine List.Subset.trans (keys_updateRace_subset nk sk _) ?_
            rw [keys_emit]
            refine List.append_subset.mpr ⟨?_, ?_⟩
            · sub_tac
            · refine List.Subset.trans hrk' ?_; sub_tac
          · refine List.Subset.trans hrk'' ?_; sub_tac
        · split
          · simp only [cmdsKeys, List.append_nil]
            sub_tac
          · simp only [cmdsKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Cmd.keys,
              List.append_nil]
            refine List.append_subset.mpr ⟨?_, ?_⟩
            · sub_tac
            · refine List.Subset.trans hsettle ?_; sub_tac
      · refine ⟨by rw [world_updateRace, world_emit]; exact World.le_refl _, ?_⟩
        simp only [MintedIn]
        rw [world_updateRace, world_emit]
        have hall : Ok acc.1.world (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++ race.keys nk sk) :=
          Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hm, Ok_of_subset hrk (Ok_of_subset (by sub_tac) hm)⟩
        refine Ok_of_subset ?_ hall
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans (keys_updateRace_subset nk sk _) ?_
          rw [keys_emit]
          refine List.append_subset.mpr ⟨?_, ?_⟩
          · sub_tac
          · refine List.Subset.trans hrk' ?_; sub_tac
        · sub_tac
theorem fireObserver_callback_minted (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (key : Nat)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
      (Observer.callback key).keys)) :
    FiredMinted nk sk acc (fireObserver interp id exit acc (Observer.callback key)) := by
  unfold FiredMinted
  simp only [fireObserver]
  refine ⟨by rw [world_emit, world_emit]; exact World.le_refl _, ?_⟩
  simp only [MintedIn]
  rw [world_emit, world_emit]
  refine Ok_of_subset ?_ hm
  rw [keys_emit, keys_emit]
  sub_tac

theorem fireObserver_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (observer : Observer)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++ observer.keys)) :
    acc.1.world.le (fireObserver interp id exit acc observer).1.world ∧
      MintedIn (fireObserver interp id exit acc observer).1
        ((fireObserver interp id exit acc observer).1.keys nk sk ++
          cmdsKeys nk sk (fireObserver interp id exit acc observer).2) := by
  cases observer with
  | resumeAwait waiter token mode =>
    exact fireObserver_resumeAwait_minted nk sk hb id exit acc waiter token mode hm
  | untrackChild parent => exact fireObserver_untrackChild_minted nk sk id exit acc parent hm
  | dropScopeFinalizer scope key =>
    exact fireObserver_dropScopeFinalizer_minted nk sk hb id exit acc scope key hm
  | countdown waiter token => exact fireObserver_countdown_minted nk sk hb id exit acc waiter token hm
  | raceCallback raceId => exact fireObserver_raceCallback_minted nk sk hb id exit acc raceId hm
  | callback key => exact fireObserver_callback_minted nk sk id exit acc key hm

theorem fireObserver_fold_minted (hb : KeyBounded nk sk interp ambient) (id : FiberId) (exit : ExitV)
    (observers : List Observer) :
    ∀ acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann),
      MintedIn acc.1 (acc.1.keys nk sk ++ cmdsKeys nk sk acc.2 ++ exitKeys exit ++
        observers.flatMap Observer.keys) →
      acc.1.world.le (observers.foldl (fireObserver interp id exit) acc).1.world ∧
        MintedIn (observers.foldl (fireObserver interp id exit) acc).1
          ((observers.foldl (fireObserver interp id exit) acc).1.keys nk sk ++
            cmdsKeys nk sk (observers.foldl (fireObserver interp id exit) acc).2) := by
  induction observers with
  | nil =>
    intro acc hm
    exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  | cons o os ih =>
    intro acc hm
    rw [List.foldl_cons]
    obtain ⟨hle, hok⟩ := fireObserver_minted nk sk hb id exit acc o (Ok_of_subset (by sub_tac) hm)
    obtain ⟨hle', hok'⟩ := ih (fireObserver interp id exit acc o)
      (Ok_append.mpr ⟨Ok_append.mpr ⟨hok, Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩,
        Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩)
    exact ⟨World.le_trans hle hle', hok'⟩

/-- The keys of the observer commands the exit path issues (D6b). -/
theorem cmdsKeys_observe_map (id : FiberId) (exit : ExitV) :
    ∀ os : List Observer,
      cmdsKeys nk sk (os.map (Cmd.observe id exit)) ⊆
        Handle.fiber id :: exitKeys exit ++ os.flatMap Observer.keys
  | [] => by simp only [List.map_nil, cmdsKeys, List.flatMap_nil]; exact List.nil_subset _
  | o :: os => by
    have ih := cmdsKeys_observe_map id exit os
    simp only [cmdsKeys] at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, Cmd.keys]
    sub_tac using ih

/-- The keys of an interrupt-all's target commands are the targets (D6b). -/
theorem cmdsKeys_interruptTargets (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ∀ targets : List FiberId,
      cmdsKeys nk sk (targets.map fun t => Cmd.interruptTarget t who extra) = targets.map Handle.fiber
  | [] => rfl
  | t :: ts => by
    have ih := cmdsKeys_interruptTargets who extra ts
    simp only [cmdsKeys] at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, Cmd.keys, ih, List.singleton_append]

theorem exitInterruptChildren_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (exit : ExitV)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ exitKeys exit)) :
    m.world.le (exitFiber.exitInterruptChildren interp m f exit).1.world ∧
      MintedIn (exitFiber.exitInterruptChildren interp m f exit).1
        ((exitFiber.exitInterruptChildren interp m f exit).1.keys nk sk ++
          cmdsKeys nk sk (exitFiber.exitInterruptChildren interp m f exit).2) := by
  rw [exitInterruptChildren_eq]
  -- the middleware's program names the children and the exit (D6b)
  have hcode : primKeys nk sk
      (Prim.onSuccess (interp.interruptAllCode f.children) (interp.restoreName exit)) ⊆
        f.children.map Handle.fiber ++ exitKeys exit := by
    simp only [primKeys]
    exact List.append_subset.mpr
      ⟨List.Subset.trans (hb.interruptAllCode _) (List.subset_append_left _ _),
        List.Subset.trans (hb.restoreName _) (List.subset_append_right _ _)⟩
  have hc : Ok m.world (primKeys nk sk
      (Prim.onSuccess (interp.interruptAllCode f.children) (interp.restoreName exit))) :=
    Ok_of_subset hcode (Ok_of_subset (by sub_tac) hm)
  refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
  simp only [MintedIn]
  rw [world_emit, world_update]
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hc⟩)
  rw [keys_emit]
  refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) ?_, ?_⟩
  · simp only [RunFiber.keys, frameKeys, optExitKeys]
    sub_tac
  · simp only [cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil]
    exact List.nil_subset _

theorem exitStore_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (exit : ExitV)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ exitKeys exit)) :
    m.world.le (exitFiber.exitStore interp m f exit).1.world ∧
      MintedIn (exitFiber.exitStore interp m f exit).1
        ((exitFiber.exitStore interp m f exit).1.keys nk sk ++
          cmdsKeys nk sk (exitFiber.exitStore interp m f exit).2) := by
  have hpub : (f.publish exit).keys nk sk ⊆ f.keys nk sk ++ exitKeys exit := by
    simp only [RunFiber.publish, RunFiber.keys, frameKeys, optExitKeys, FiberCore.setDeferred,
      List.flatMap_nil, List.append_nil]
    sub_tac
  have hclr : ((f.publish exit).cleared interp).keys nk sk ⊆ f.keys nk sk ++ exitKeys exit := by
    simp only [RunFiber.cleared, RunFiber.publish, RunFiber.keys, frameKeys, optExitKeys,
      FiberCore.setDeferred, FiberCore.clearStack, hb.emptyContext, List.flatMap_nil, List.map_nil,
      List.append_nil]
    sub_tac
  have hobsk : f.observers.flatMap Observer.keys ⊆ f.keys nk sk := by
    simp only [RunFiber.keys]; sub_tac
  have hP : Ok m.world ((f.publish exit).keys nk sk) :=
    Ok_of_subset hpub (Ok_of_subset (by sub_tac) hm)
  rcases hobs : f.observers with _ | ⟨o, os⟩
  · rw [exitStore_no_observers interp m f exit hobs]
    refine ⟨by rw [world_update, world_emit, world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update, world_emit, world_update]
    have hC : Ok m.world (((f.publish exit).cleared interp).keys nk sk) :=
      Ok_of_subset hclr (Ok_of_subset (by sub_tac) hm)
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, Ok_append.mpr ⟨hP, hC⟩⟩)
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) ?_, ?_⟩
    · rw [keys_emit]
      refine List.append_subset.mpr
        ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
    · simp only [cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil]
      exact List.nil_subset _
  · rw [exitStore_observers interp m f exit o os hobs]
    refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit, world_update]
    have hoc := cmdsKeys_observe_map nk sk f.id exit (o :: os)
    have hobs' : (o :: os).flatMap Observer.keys ⊆ f.keys nk sk := by
      rw [← hobs]; exact hobsk
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hP⟩)
    rw [keys_emit]
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), ?_⟩
    simp only [cmdsKeys, List.flatMap_append] at hoc ⊢
    refine List.append_subset.mpr ⟨List.Subset.trans hoc ?_, ?_⟩
    · exact List.cons_subset.mpr ⟨by simp, List.append_subset.mpr
        ⟨by sub_tac, List.Subset.trans hobs' (by sub_tac)⟩⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil]
      sub_tac

theorem exitFiber_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (exit : ExitV)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ exitKeys exit)) :
    m.world.le (exitFiber interp m f exit).1.world ∧
      MintedIn (exitFiber interp m f exit).1
        ((exitFiber interp m f exit).1.keys nk sk ++ cmdsKeys nk sk (exitFiber interp m f exit).2) := by
  rw [exitFiber_eq]
  split
  · exact exitInterruptChildren_minted nk sk hb m f exit hm
  · exact exitStore_minted nk sk hb m f exit hm

/-! ### `evaluatePrim` and its arms -/

/-- The receipt of an iteration: the world grew, and every handle the iteration leaves exists. -/
def IterMinted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  m.world.le it.machine.world ∧ MintedIn it.machine (iterKeys nk sk it)

theorem uninterruptible_keys (fr : FrameFiber ν σ Val Err Defect FiberId Ann) :
    frameKeys nk sk fr.uninterruptible ⊆ frameKeys nk sk fr := by
  unfold FrameFiber.uninterruptible
  split
  · simp only [frameKeys, List.flatMap_cons, primKeys, List.nil_append]
    exact List.Subset.refl _
  · exact List.Subset.refl _

theorem interruptibleRegion_keys (fr : FrameFiber ν σ Val Err Defect FiberId Ann) :
    frameKeys nk sk fr.interruptibleRegion.1 ⊆ frameKeys nk sk fr ∧
      optPrimKeys nk sk fr.interruptibleRegion.2 = [] := by
  unfold FrameFiber.interruptibleRegion
  split
  · exact ⟨List.Subset.refl _, rfl⟩
  · unfold FrameFiber.setFiberInterruptible
    refine ⟨?_, ?_⟩
    · simp only [frameKeys, List.flatMap_cons, primKeys, List.nil_append]
      exact List.Subset.refl _
    · split <;> rfl

/-- A finished frame keeps only handles already in its input pop. -/
theorem frameExitState_keys (frame : FrameFiber ν σ Val Err Defect FiberId Ann) :
    frameKeys nk sk (frameExitState frame) ⊆ frameKeys nk sk frame := by
  unfold frameExitState
  split
  · exact (List.append_subset.mp (getCont_keys nk sk frame Arm.contE true)).2
  · exact (List.append_subset.mp (getCont_keys nk sk frame Arm.contA false)).2

theorem finishFrame_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (next : FrameStep ν σ Val Err Defect FiberId Ann) (events : List (FrameEvent ν σ Val Err Defect FiberId Ann))
    (nested : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ f.keys nk sk ++ stepKeys nk sk next ++ cmdsKeys nk sk nested)) :
    IterMinted nk sk m (evaluatePrim.finishFrame m f yielding next events nested) := by
  unfold IterMinted evaluatePrim.finishFrame
  try dsimp only
  split
  · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit]
    refine Ok_of_subset ?_ hm
    simp only [stepKeys]
    sub_tac
  · refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit]
    refine Ok_of_subset ?_ hm
    simp only [stepKeys]
    have hpop := frameExitState_keys nk sk f.frame
    simp only [frameKeys, List.append_subset] at hpop
    sub_tac using hpop.1, hpop.2

theorem stepFrame_minted_with_ambient (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (ambient ++ (m.keys nk sk ++ f.keys nk sk))) :
    IterMinted nk sk m (evaluatePrim.stepFrame interp m f yielding) := by
  unfold evaluatePrim.stepFrame
  try dsimp only
  refine finishFrame_minted nk sk m f yielding _ _ [] ?_
  have hstep := step_keys_with_ambient nk sk hb f.frame
  refine Ok_of_subset ?_ hm
  simp only [cmdsKeys, List.flatMap_nil, List.append_nil]
  sub_tac using hstep

theorem finalizerOr_minted_with_ambient (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (hm : MintedIn m (ambient ++ (m.keys nk sk ++ f.keys nk sk ++ exitKeys exit))) :
    IterMinted nk sk m (evaluatePrim.finalizerOr interp m f yielding exit) := by
  obtain ⟨ha, hm⟩ := Ok_append.mp hm
  unfold evaluatePrim.finalizerOr
  try dsimp only
  split
  · next body fin flag hpop =>
    split
    · next program hprog =>
      have hg := getCont_answer_frame_keys nk sk f.frame _ _ _ hpop
      simp only [primKeys, List.append_subset] at hg
      have hF : Ok m.world (frameKeys nk sk f.frame) := Ok_of_subset (by sub_tac) hm
      have hfin : Ok m.world (primKeys nk sk program) :=
        Ok_of_subset (hb.finalizerProgram fin exit program hprog)
          (Ok_append.mpr ⟨ha, Ok_append.mpr ⟨Ok_of_subset hg.1.2 hF,
            Ok_of_subset (by sub_tac) hm⟩⟩)
      have hres : Ok m.world (nk (interp.restoreName exit)) :=
        Ok_of_subset (hb.restoreName exit) (Ok_of_subset (by sub_tac) hm)
      have hmerge : Ok m.world (nk (interp.mergeName exit)) :=
        Ok_of_subset (hb.mergeName exit) (Ok_of_subset (by sub_tac) hm)
      have hpopf := Ok_of_subset hg.2 hF
      have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨hm, hfin⟩, hres⟩, hmerge⟩, hpopf⟩
      unfold IterMinted
      refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      refine Ok_of_subset ?_ hall
      cases exit <;> simp only [finalizerCode] <;> sub_tac
    · exact stepFrame_minted_with_ambient nk sk hb m f yielding
          (Ok_append.mpr ⟨ha, Ok_of_subset (by sub_tac) hm⟩)
  · exact stepFrame_minted_with_ambient nk sk hb m f yielding
          (Ok_append.mpr ⟨ha, Ok_of_subset (by sub_tac) hm⟩)

/-- `fiberInterruptAs` records and delegates (D6b): the target's run and the return that names
the host and the target are the commands. -/
theorem interruptAs_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (target who : FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: Handle.fiber target :: m.keys nk sk ++ f.keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.interruptAs interp m f yielding target who) := by
  unfold IterMinted evaluatePrim.interruptAs
  try dsimp only
  split
  · refine ⟨World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    sub_tac
  · next t ht =>
    have hir := interruptRecord_keys_subset nk sk interp (some who) (interp.stackAnnotations f.id) t
    have htk := fiber?_keys_subset nk sk ht
    have hX : Ok m.world ((interruptRecord interp (some who) (interp.stackAnnotations f.id) t).1.keys nk sk) :=
      Ok_of_subset (List.Subset.trans hir htk) (Ok_of_subset (by sub_tac) hm)
    have hup := keys_update_fibers_subset nk sk (m := m)
      (interruptRecord interp (some who) (interp.stackAnnotations f.id) t).1
    refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn, iterKeys, Outcome.keys]
    rw [world_emit, world_update]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hX⟩)
    rw [keys_emit]
    split <;>
      simp only [cmdsKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Cmd.keys,
        ParkKind.keys, List.append_nil, List.nil_append] <;>
      sub_tac using hup

/-! #### The `withFiber` arms, one lemma each -/

/-- The fork arms share one shape: spawn, start, answer the child's handle. `M` is the machine
the arm forks in (the fork arm may have set the middleware latch first, so its world is `m`'s),
`S` and `T` name the spawn and the start, and the iteration `it` is whatever the arm built
from them: its machine is `T.1`, its fiber names nothing beyond the started parent's handles and
the child's, its commands nothing beyond the start's, and its outcome nothing. -/
theorem fork_arm_minted (hb : KeyBounded nk sk interp ambient)
    (m M : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (hMw : M.world = m.world)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    (S : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × RunFiber ν σ Val Err Defect FiberId Ann Ctx × FiberId)
    (T : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × RunFiber ν σ Val Err Defect FiberId Ann Ctx ×
      List (Cmd ν σ Val Err Defect FiberId Ann))
    (hS : spawn interp M f program options = S) (hT : start S.1 S.2.1 S.2.2 options.startImmediately = T)
    (hm : MintedIn M (Handle.fiber f.id :: M.keys nk sk ++ f.keys nk sk ++ primKeys nk sk program))
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) (hmach : it.machine = T.1)
    (hfib : it.fiber.keys nk sk ⊆ T.2.1.keys nk sk ++ (interp.fiberValue S.2.2).keys)
    (hnest : cmdsKeys nk sk it.nested ⊆
      cmdsKeys nk sk T.2.2 ++ [Handle.fiber f.id, Handle.fiber S.2.2])
    (hout : it.outcome.keys = []) :
    IterMinted nk sk m it := by
  unfold IterMinted
  obtain ⟨hle1, h1⟩ := spawn_minted nk sk interp M f program options hm
  have hid : (spawn interp M f program options).2.1.id = f.id := rfl
  rw [hS] at hle1 h1 hid
  have h1' : MintedIn S.1 (Handle.fiber S.2.1.id :: Handle.fiber S.2.2 :: S.1.keys nk sk ++ S.2.1.keys nk sk) := by
    rw [hid]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨h1, Ok_mono hle1 hm⟩)
    sub_tac
  obtain ⟨hle2, h2⟩ := start_minted nk sk S.1 S.2.1 S.2.2 options.startImmediately h1'
  rw [hT] at hle2 h2
  have hchild : Ok T.1.world [Handle.fiber S.2.2] := Ok_mono hle2 (Ok_of_subset (by sub_tac) h1)
  have hv : Ok T.1.world (interp.fiberValue S.2.2).keys := Ok_of_subset (hb.fiberValue _) hchild
  -- the tracking command names the parent too (D6b)
  have hparent : Ok T.1.world [Handle.fiber f.id] :=
    Ok_mono hle2 (Ok_mono hle1 (Ok_of_subset (by sub_tac) hm))
  rw [hMw] at hle1
  refine ⟨by rw [hmach]; exact World.le_trans hle1 hle2, ?_⟩
  simp only [MintedIn, iterKeys, hmach, hout]
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨h2, hv⟩, Ok_append.mpr ⟨hparent, hchild⟩⟩)
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨List.append_subset.mpr ⟨by sub_tac, ?_⟩, ?_⟩,
    List.nil_subset _⟩
  · refine List.Subset.trans hfib ?_; sub_tac
  · refine List.Subset.trans hnest ?_; sub_tac

theorem withFiber_fork_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.fork program options).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.fork program options)) := by
  simp only [evaluatePrim.withFiber]
  try dsimp only
  have hM : ∀ M : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores,
      (if options.daemon then m else { m with middlewareInstalled := true }) = M →
      M.world = m.world ∧ M.keys nk sk = m.keys nk sk := by
    intro M hM
    subst hM
    split <;> exact ⟨rfl, rfl⟩
  generalize hMdef : (if options.daemon then m else { m with middlewareInstalled := true }) = M
  obtain ⟨hMw, hMk⟩ := hM M hMdef
  have hm' : MintedIn M (Handle.fiber f.id :: M.keys nk sk ++ f.keys nk sk ++ primKeys nk sk program) := by
    simp only [MintedIn]
    rw [hMw, hMk]
    exact Ok_of_subset (by sub_tac) hm
  generalize hS : spawn interp M f program options = S
  generalize hT : start S.1 S.2.1 S.2.2 options.startImmediately = T
  refine fork_arm_minted nk sk hb m M hMw f program options S T hS hT hm' _ rfl ?_ ?_ rfl
  · sub_tac
  · -- the start's commands, then the tracking command unless daemon (D6b)
    simp only [cmdsKeys, List.flatMap_append]
    split <;> simp only [cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil] <;> sub_tac

theorem withFiber_forkIn_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions) (scope : Nat)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.forkIn program options scope).keys nk sk)) :
    IterMinted nk sk m
      (evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkIn program options scope)) := by
  simp only [evaluatePrim.withFiber]
  try dsimp only
  generalize hS : spawn interp m f program { options with daemon := true } = S
  generalize hT : start S.1 S.2.1 S.2.2 options.startImmediately = T
  refine fork_arm_minted nk sk hb m m rfl f program { options with daemon := true } S T hS hT
    (Ok_of_subset (by sub_tac) hm) _ rfl ?_ ?_ rfl
  · sub_tac
  · sub_tac

theorem withFiber_forkScoped_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (program : Prim ν σ Val Err Defect FiberId Ann) (options : Supervision.ForkOptions)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.forkScoped program options).keys nk sk)) :
    IterMinted nk sk m
      (evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options)) := by
  simp only [evaluatePrim.withFiber]
  try dsimp only
  split
  · next scope _ =>
    generalize hS : spawn interp m f program { options with daemon := true } = S
    generalize hT : start S.1 S.2.1 S.2.2 options.startImmediately = T
    refine fork_arm_minted nk sk hb m m rfl f program { options with daemon := true } S T hS hT
      (Ok_of_subset (by sub_tac) hm) _ rfl ?_ ?_ rfl
    · sub_tac
    · sub_tac
  · unfold IterMinted
    refine ⟨World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    sub_tac

theorem withFiber_runIn_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (target : FiberId) (scope : Nat)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.runIn target scope).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.runIn target scope)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  obtain ⟨hle, hok⟩ := linkScope_minted nk sk hb m Supervision.ScopeMode.fiberRunIn scope target
    (some target) ReasonAnnotations.empty (Ok_of_subset (by sub_tac) hm)
  generalize hL : linkScope interp m Supervision.ScopeMode.fiberRunIn scope target (some target)
    ReasonAnnotations.empty = L at hle hok ⊢
  refine ⟨hle, ?_⟩
  simp only [MintedIn]
  have hv : Ok L.1.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hok, Ok_mono hle hm⟩, hv⟩)
  (repeat' split) <;> sub_tac

theorem withFiber_interrupt_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (target : FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.interrupt target).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.interrupt target)) := by
  simp only [evaluatePrim.withFiber]
  unfold IterMinted
  refine ⟨World.le_refl _, ?_⟩
  -- the returned `fiberInterruptAs` program names the target (D6b)
  have hc : Ok m.world (primKeys nk sk (interp.interruptAsCode target f.id)) :=
    Ok_of_subset (hb.interruptAsCode _ _) (Ok_of_subset (by sub_tac) hm)
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hc⟩)
  sub_tac

theorem withFiber_interruptAs_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (target who : FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.interruptAs target who).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAs target who)) := by
  simp only [evaluatePrim.withFiber]
  exact interruptAs_minted nk sk hb m f yielding target who (Ok_of_subset (by sub_tac) hm)

theorem withFiber_interruptScoped_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (target : FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.interruptScoped target).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptScoped target)) := by
  simp only [evaluatePrim.withFiber]
  split
  · unfold IterMinted
    refine ⟨World.le_refl _, ?_⟩
    have hv : Ok m.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
    sub_tac
  · unfold IterMinted
    refine ⟨World.le_refl _, ?_⟩
    -- the returned public interrupt program names the target (D6b)
    have hc : Ok m.world (primKeys nk sk (interp.interruptCode target)) :=
      Ok_of_subset (hb.interruptCode _) (Ok_of_subset (by sub_tac) hm)
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hc⟩)
    sub_tac

/-- The countdown arms share one shape: an optional interrupt fold, then the park. -/
theorem countdown_arm_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (targets : List FiberId)
    (resumeWith : Resume ν) (failFast : Bool)
    (I : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann))
    (hle : m.world.le I.1.world) (hI : MintedIn I.1 (I.1.keys nk sk ++ cmdsKeys nk sk I.2))
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ targets.map Handle.fiber ++
      resumeWith.keys nk)) :
    IterMinted nk sk m
      ⟨(countdownPark interp I.1 f targets resumeWith failFast).1,
        (countdownPark interp I.1 f targets resumeWith failFast).2.1, yielding,
        (match (countdownPark interp I.1 f targets resumeWith failFast).1.stuck with
          | some why => Outcome.stuck why
          | none => if (countdownPark interp I.1 f targets resumeWith failFast).2.2 then Outcome.parked
            else Outcome.continue_), I.2⟩ := by
  unfold IterMinted
  have hin : MintedIn I.1 (Handle.fiber f.id :: I.1.keys nk sk ++ f.keys nk sk ++ targets.map Handle.fiber ++
      resumeWith.keys nk) :=
    Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hI, Ok_mono hle hm⟩)
  obtain ⟨hle2, hok⟩ := countdownPark_minted nk sk hb I.1 f targets resumeWith failFast hin
  generalize hP : countdownPark interp I.1 f targets resumeWith failFast = P at hle2 hok ⊢
  refine ⟨World.le_trans hle hle2, ?_⟩
  simp only [MintedIn]
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hok, Ok_mono hle2 hI⟩)
  (repeat' split) <;> sub_tac

theorem withFiber_interruptAll_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (targets : List FiberId)
    (interruptor : Option FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.interruptAll targets interruptor).keys nk sk)) :
    IterMinted nk sk m
      (evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAll targets interruptor)) := by
  simp only [evaluatePrim.withFiber]
  unfold IterMinted
  refine ⟨World.le_refl _, ?_⟩
  refine Ok_of_subset ?_ hm
  -- the commands name the targets and the host (D6b)
  have h := cmdsKeys_interruptTargets nk sk (some (interruptor.getD f.id)) (interp.stackAnnotations f.id) targets
  simp only [iterKeys, Outcome.keys, cmdsKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    Cmd.keys, ParkKind.keys, List.append_nil] at h ⊢
  rw [h]
  sub_tac

theorem withFiber_awaitAll_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (targets : List FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.awaitAll targets).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.awaitAll targets)) := by
  simp only [evaluatePrim.withFiber]
  exact countdown_arm_minted nk sk hb m f yielding targets Resume.exitsValue false (m, []) (World.le_refl _)
    (Ok_of_subset (by sub_tac) hm) (Ok_of_subset (by sub_tac) hm)

theorem withFiber_awaitAllFailFast_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (targets : List FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.awaitAllFailFast targets).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.awaitAllFailFast targets)) := by
  simp only [evaluatePrim.withFiber]
  exact countdown_arm_minted nk sk hb m f yielding targets Resume.exitsValue true (m, []) (World.le_refl _)
    (Ok_of_subset (by sub_tac) hm) (Ok_of_subset (by sub_tac) hm)

theorem withFiber_snapshotChildren_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.snapshotChildren).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding WithFiberAction.snapshotChildren) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  refine ⟨World.le_refl _, ?_⟩
  have hv : Ok m.world (interp.fibersValue f.children).keys :=
    Ok_of_subset (hb.fibersValue _) (Ok_of_subset (by sub_tac) hm)
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
  sub_tac

theorem withFiber_awaitNewChildren_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (snapshot : List FiberId)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.awaitNewChildren snapshot).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.awaitNewChildren snapshot)) := by
  simp only [evaluatePrim.withFiber]
  have hfresh : (f.children.filter fun c => !(snapshot.contains c)).map Handle.fiber ⊆ f.keys nk sk := by
    refine List.Subset.trans (map_filter_subset Handle.fiber _ f.children) ?_
    simp only [RunFiber.keys]
    sub_tac
  exact countdown_arm_minted nk sk hb m f yielding _ Resume.void false (m, []) (World.le_refl _)
    (Ok_of_subset (by sub_tac) hm)
    (Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, Ok_of_subset hfresh (Ok_of_subset (by sub_tac) hm)⟩))

theorem withFiber_raceAll_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (entrants : List (Prim ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.raceAll entrants).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.raceAll entrants)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber, beginRace]
  -- the registration code names no handle: a race identity is a lookup key (D6a)
  have hpark : Ok m.world (primKeys nk sk (interp.parkCode (ParkKind.race m.nextRace))) :=
    Ok_of_subset (hb.parkCode _) (by simp only [ParkKind.keys]; exact Ok_nil _)
  -- the counters and the appended race leave the world as it was (definitionally)
  refine ⟨⟨fun _ h => h, Stores.le_refl _⟩, ?_⟩
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hpark⟩)
  sub_tac

theorem withFiber_setInterruptible_minted
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (body : Prim ν σ Val Err Defect FiberId Ann) (flag : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.setInterruptible body flag).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.setInterruptible body flag)) := by
  unfold IterMinted
  cases flag with
  | false =>
    simp only [evaluatePrim.withFiber]
    refine ⟨World.le_refl _, ?_⟩
    have hfr : Ok m.world (frameKeys nk sk f.frame.uninterruptible) :=
      Ok_of_subset (uninterruptible_keys nk sk f.frame) (Ok_of_subset (by sub_tac) hm)
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hfr⟩)
    sub_tac
  | true =>
    simp only [evaluatePrim.withFiber]
    try dsimp only
    refine ⟨World.le_refl _, ?_⟩
    obtain ⟨hfr, himm⟩ := interruptibleRegion_keys nk sk f.frame
    have hfr' : Ok m.world (frameKeys nk sk f.frame.interruptibleRegion.1) :=
      Ok_of_subset hfr (Ok_of_subset (by sub_tac) hm)
    have hcur : Ok m.world (primKeys nk sk (f.frame.interruptibleRegion.2.getD body)) := by
      refine Ok_of_subset (primKeys_getD nk sk _ body) ?_
      rw [himm]
      exact Ok_of_subset (by sub_tac) hm
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hm, hfr'⟩, hcur⟩)
    sub_tac

theorem withFiber_setContext_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (context : Ctx)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.setContext context).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.setContext context)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  try dsimp only
  refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
  simp only [MintedIn]
  rw [world_emit]
  have hv : Ok m.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
  sub_tac

/-- The `Scope` service read (§20) answers a handle the context names, or dies. -/
theorem withFiber_ambientScope_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.ambientScope).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding WithFiberAction.ambientScope) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  split
  · next scope hscope =>
    refine ⟨World.le_refl _, ?_⟩
    have hs : Ok m.world [Handle.scope scope] := by
      refine Ok_of_subset ?_ hm
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      have hmem := hb.ambientScope f.context scope hscope
      simp only [RunFiber.keys, List.mem_cons, List.mem_append, hmem, or_true, true_or]
    have hv : Ok m.world (interp.scopeValue scope).keys := Ok_of_subset (hb.scopeValue scope) hs
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
    sub_tac
  · refine ⟨World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    sub_tac

/-- The parallel close's forks (§20): each spawn mints its child; the closer is unchanged. -/
theorem forkFinalizers_minted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores)
    (host : RunFiber ν σ Val Err Defect FiberId Ann Ctx) :
    ∀ (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
      (programs : List (Prim ν σ Val Err Defect FiberId Ann)),
      MintedIn m (Handle.fiber host.id :: m.keys nk sk ++ host.keys nk sk ++
        programs.flatMap (primKeys nk sk)) →
      m.world.le (forkFinalizers interp m host programs).1.world ∧
        MintedIn (forkFinalizers interp m host programs).1
          ((forkFinalizers interp m host programs).2.map Handle.fiber ++
            (forkFinalizers interp m host programs).1.keys nk sk ++ host.keys nk sk)
  | m, [], hm => by
    simp only [forkFinalizers, List.map_nil, List.nil_append]
    exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  | m, program :: rest, hm => by
    unfold forkFinalizers
    try dsimp only
    obtain ⟨hle1, h1⟩ := spawn_minted nk sk interp m host program ⟨true, true, Supervision.MaskMode.inherit⟩
      (Ok_of_subset (by simp only [List.flatMap_cons]; sub_tac) hm)
    rw [spawn_untracked] at h1
    generalize hS : spawn interp m host program ⟨true, true, Supervision.MaskMode.inherit⟩ = S at hle1 h1 ⊢
    have hrest : MintedIn S.1 (Handle.fiber host.id :: S.1.keys nk sk ++ host.keys nk sk ++
        rest.flatMap (primKeys nk sk)) := by
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨h1, Ok_mono hle1 hm⟩)
      simp only [List.flatMap_cons]
      sub_tac
    obtain ⟨hle2, h2⟩ := forkFinalizers_minted interp host S.1 rest hrest
    generalize hT : forkFinalizers interp S.1 host rest = T at hle2 h2 ⊢
    refine ⟨World.le_trans hle1 hle2, ?_⟩
    simp only [List.map_cons]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle2 h1, h2⟩)
    sub_tac

theorem evaluate_cmds_keys : ∀ ids : List FiberId,
    (ids.map Cmd.evaluate).flatMap (Cmd.keys nk sk) = []
  | [] => rfl
  | id :: ids => by
    simp only [List.map_cons, List.flatMap_cons, Cmd.keys, List.nil_append, evaluate_cmds_keys ids]

/-- The parallel walk's step (§20): the daemons it forks are minted, and its commands name
them and the closer. -/
theorem withFiber_closePar_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (finalizers : List (Prim ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.closePar finalizers).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.closePar finalizers)) := by
  have _ := hb
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  try dsimp only
  obtain ⟨hle, hF⟩ := forkFinalizers_minted nk sk interp f m finalizers
    (Ok_of_subset (by simp only [WithFiberAction.keys]; sub_tac) hm)
  generalize hFdef : forkFinalizers interp m f finalizers = F at hle hF ⊢
  obtain ⟨M, children⟩ := F
  simp only at hle hF ⊢
  refine ⟨hle, ?_⟩
  simp only [MintedIn, iterKeys, Outcome.keys, cmdsKeys, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Cmd.keys, evaluate_cmds_keys, List.append_nil, List.nil_append]
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hF, Ok_mono hle hm⟩)
  sub_tac

theorem withFiber_getContext_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.getContext).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding WithFiberAction.getContext) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  refine ⟨World.le_refl _, ?_⟩
  have hv : Ok m.world (interp.contextValue f.context).keys :=
    Ok_of_subset (hb.contextValue _) (Ok_of_subset (by sub_tac) hm)
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
  sub_tac

theorem withFiber_getId_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ (WithFiberAction.getId).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding WithFiberAction.getId) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  refine ⟨World.le_refl _, ?_⟩
  have hv : Ok m.world (interp.fiberIdValue f.id).keys :=
    Ok_of_subset (hb.fiberIdValue _) (Ok_of_subset (by sub_tac) hm)
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
  sub_tac

theorem withFiber_closeScope_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (scope : Nat) (exit : ExitV)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.closeScope scope exit).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.closeScope scope exit)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  split
  · refine ⟨World.le_refl _, ?_⟩
    refine Ok_of_subset ?_ hm
    sub_tac
  · next state program hclose =>
    have hsk : Ok ⟨m.fibers.map RunFiber.id, m.state⟩ (Handle.fiber f.id :: exitKeys exit ++ m.state.keys) :=
      Ok_of_subset (by sub_tac) hm
    obtain ⟨hsle, hsok⟩ := hb.closeScope scope exit f.frame.interruptible f.id m.state state program _ hclose hsk
    have hle : m.world.le ({ m with state := state } : NM ν σ).world := ⟨fun _ h => h, hsle⟩
    refine ⟨hle, ?_⟩
    simp only [MintedIn]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩)
    sub_tac

theorem withFiber_refuse_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (cause : CauseV)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.refuse cause).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.refuse cause)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  refine ⟨World.le_refl _, ?_⟩
  refine Ok_of_subset ?_ hm
  sub_tac

theorem withFiber_dropObservers_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (token : Nat)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.dropObservers token).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.dropObservers token)) := by
  unfold IterMinted
  simp only [evaluatePrim.withFiber]
  refine ⟨by rw [world_map_observers]; exact World.le_refl _, ?_⟩
  simp only [MintedIn]
  rw [world_map_observers]
  have hv : Ok m.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
  sub_tac using (keys_map_observers_subset nk sk (m := m) _)

theorem withFiber_cancelRace_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (raceId : Nat)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
      (WithFiberAction.cancelRace raceId).keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding (WithFiberAction.cancelRace raceId)) := by
  simp only [evaluatePrim.withFiber]
  split
  · unfold IterMinted
    refine ⟨World.le_refl _, ?_⟩
    have hv : Ok m.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
    sub_tac
  · next race hrace =>
    unfold IterMinted
    have hrk : race.keys nk sk ⊆ m.keys nk sk := race?_keys_subset nk sk hrace
    have hlive : Ok m.world (race.state.live.map Handle.fiber) :=
      Ok_of_subset (by sub_tac) (Ok_of_subset hrk (Ok_of_subset (by sub_tac) hm))
    refine ⟨World.le_refl _, ?_⟩
    -- the walk command names the host and the entrants live now (D6b)
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hlive⟩)
    simp only [iterKeys, Outcome.keys, cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys,
      List.append_nil, List.map_append, List.map_nil]
    sub_tac

theorem withFiber_minted (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (action : WithFiberAction ν σ Val Err Defect FiberId Ann Ctx)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++ action.keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.withFiber interp m f yielding action) := by
  cases action with
  | fork program options => exact withFiber_fork_minted nk sk hb m f yielding program options hm
  | forkIn program options scope =>
    exact withFiber_forkIn_minted nk sk hb m f yielding program options scope hm
  | forkScoped program options => exact withFiber_forkScoped_minted nk sk hb m f yielding program options hm
  | runIn target scope => exact withFiber_runIn_minted nk sk hb m f yielding target scope hm
  | interrupt target => exact withFiber_interrupt_minted nk sk hb m f yielding target hm
  | interruptAs target who => exact withFiber_interruptAs_minted nk sk hb m f yielding target who hm
  | interruptScoped target => exact withFiber_interruptScoped_minted nk sk hb m f yielding target hm
  | interruptAll targets interruptor =>
    exact withFiber_interruptAll_minted nk sk hb m f yielding targets interruptor hm
  | awaitAll targets => exact withFiber_awaitAll_minted nk sk hb m f yielding targets hm
  | awaitAllFailFast targets => exact withFiber_awaitAllFailFast_minted nk sk hb m f yielding targets hm
  | snapshotChildren => exact withFiber_snapshotChildren_minted nk sk hb m f yielding hm
  | awaitNewChildren snapshot => exact withFiber_awaitNewChildren_minted nk sk hb m f yielding snapshot hm
  | raceAll entrants => exact withFiber_raceAll_minted nk sk hb m f yielding entrants hm
  | setInterruptible body flag => exact withFiber_setInterruptible_minted nk sk m f yielding body flag hm
  | setContext context => exact withFiber_setContext_minted nk sk hb m f yielding context hm
  | getContext => exact withFiber_getContext_minted nk sk hb m f yielding hm
  | getId => exact withFiber_getId_minted nk sk hb m f yielding hm
  | closeScope scope exit => exact withFiber_closeScope_minted nk sk hb m f yielding scope exit hm
  | refuse cause => exact withFiber_refuse_minted nk sk m f yielding cause hm
  | dropObservers token => exact withFiber_dropObservers_minted nk sk hb m f yielding token hm
  | cancelRace raceId => exact withFiber_cancelRace_minted nk sk hb m f yielding raceId hm
  | ambientScope => exact withFiber_ambientScope_minted nk sk hb m f yielding hm
  | closePar finalizers => exact withFiber_closePar_minted nk sk hb m f yielding finalizers hm

/-! #### `evaluatePrim` itself -/

theorem cancel_getD_keys (hb : KeyBounded nk sk interp ambient) (cancel : Option ν) :
    nk (cancel.getD interp.abortName) ⊆ (cancel.map nk).getD [] := by
  cases cancel with
  | none => simp only [Option.getD, Option.map, hb.abortName]; exact List.nil_subset _
  | some c => exact List.Subset.refl _

set_option maxHeartbeats 800000 in
theorem evaluatePrim_minted_with_ambient (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (ambient ++ (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk))) :
    IterMinted nk sk m (evaluatePrim interp m f yielding) := by
  obtain ⟨ha, hm⟩ := Ok_append.mp hm
  have hcur : Ok m.world (primKeys nk sk f.frame.current) := Ok_of_subset (by sub_tac) hm
  unfold evaluatePrim
  try dsimp only
  split
  · -- `yieldNowWith`: the fiber parks behind its own resume task
    rename_i priority _
    unfold IterMinted
    have hweq : ({ m with nextToken := m.nextToken + 1 } : NM ν σ).world = m.world := rfl
    refine ⟨by rw [world_emit, world_arm, hweq]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit, world_arm, hweq]
    have hv : Ok m.world interp.voidValue.keys := by rw [hb.voidValue]; exact Ok_nil _
    have harm : Ok m.world
        (RunMachine.keys nk sk (RunMachine.arm ({ m with nextToken := m.nextToken + 1 } : NM ν σ) f.id)) :=
      Ok_of_subset (keys_arm_subset nk sk (m := { m with nextToken := m.nextToken + 1 }) f.id)
        (Ok_of_subset (by sub_tac) hm)
    have henq : Ok m.world ((f.dispatcher.enqueue priority
        (Task.resume f.id m.nextToken (Prim.success interp.voidValue))).keys nk sk) :=
      Ok_of_subset (Dispatcher.keys_enqueue_subset nk sk _ _ _)
        (Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, hv⟩))
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨hm, hv⟩, harm⟩, henq⟩)
    sub_tac
  · -- `async`: the registration, then a synchronous resume or the park
    rename_i register withSignal cancel heq
    have hreg : Ok m.world (nk register ++ (cancel.map nk).getD []) := by
      rw [heq] at hcur
      simp only [primKeys] at hcur
      exact hcur
    have hsk : Ok ⟨m.fibers.map RunFiber.id, m.state⟩ (nk register ++ m.state.keys) :=
      Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hreg, Ok_of_subset (by sub_tac) hm⟩
    obtain ⟨hsle, hsok⟩ := hb.registerAsync register f.id m.nextToken m.state _ hsk
    have hle : m.world.le
        ({ m with state := (interp.registerAsync register f.id m.nextToken m.state).1, nextToken := m.nextToken + 1 } :
          NM ν σ).world := ⟨fun _ h => h, hsle⟩
    unfold IterMinted
    split
    · rename_i next hnext
      rw [hnext] at hsok
      simp only [Option.map, Option.getD] at hsok
      refine ⟨hle, ?_⟩
      simp only [MintedIn]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩)
      sub_tac
    · refine ⟨by rw [world_emit]; exact hle, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      have hname : nk (interp.cancelName (cancel.getD interp.abortName) f.id m.nextToken) ⊆
          Handle.fiber f.id :: (cancel.map nk).getD [] :=
        List.Subset.trans (hb.cancelName _ _ _) (List.cons_subset.mpr ⟨List.mem_cons_self,
          List.Subset.trans (cancel_getD_keys nk sk hb cancel) (List.subset_cons_of_subset _ (List.Subset.refl _))⟩)
      have hn : Ok m.world (nk (interp.cancelName (cancel.getD interp.abortName) f.id m.nextToken)) :=
        Ok_of_subset hname (Ok_cons.mpr ⟨hm _ List.mem_cons_self, Ok_of_subset (by sub_tac) hreg⟩)
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle (Ok_append.mpr ⟨hm, hn⟩), hsok⟩)
      split <;> sub_tac
  · -- everything else: a join park, a `withFiber`, a stateful `sync`, an exit, or the frame step
    split
    · -- a refused park
      unfold IterMinted
      refine ⟨World.le_refl _, ?_⟩
      refine Ok_of_subset ?_ hm
      sub_tac
    · -- a race's registration (D6a): the race is re-read and marked registering, the host
      -- keeps its code, and the nested commands carry no handle
      next raceId _ =>
      unfold IterMinted
      simp only [registerRace]
      split
      · refine ⟨World.le_refl _, ?_⟩
        refine Ok_of_subset ?_ hm
        sub_tac
      · next race hrace =>
        have hrk : Ok m.world (race.keys nk sk) :=
          Ok_of_subset (race?_keys_subset nk sk hrace) (Ok_of_subset (by sub_tac) hm)
        refine ⟨by rw [world_updateRace]; exact World.le_refl _, ?_⟩
        simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys,
          List.append_nil, Outcome.keys]
        rw [world_updateRace]
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hrk⟩)
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · refine List.Subset.trans (keys_updateRace_subset nk sk _) ?_
          simp only [Race.keys]; sub_tac
        · sub_tac
    · -- the await-all park (D6b): the countdown over the targets the park names
      next targets hpark =>
      unfold IterMinted
      have htargets : Ok m.world (targets.map Handle.fiber) :=
        Ok_of_subset (hb.parkOfAwaitAll f.frame.current targets hpark) hcur
      have hin : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk ++
          targets.map Handle.fiber ++ Resume.exitsValue.keys nk) :=
        Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, htargets⟩)
      obtain ⟨hle, hok⟩ := countdownPark_minted nk sk hb m f targets Resume.exitsValue false hin
      generalize hP : countdownPark interp m f targets Resume.exitsValue false = P at hle hok ⊢
      refine ⟨hle, ?_⟩
      simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_nil, List.append_nil]
      refine Ok_of_subset ?_ hok
      split <;> sub_tac
    · next target mode hpark =>
      have htarget : (Handle.fiber target).existsIn m.world = true :=
        hcur _ (hb.parkOf f.frame.current target mode hpark)
      split
      · unfold IterMinted
        refine ⟨World.le_refl _, ?_⟩
        refine Ok_of_subset ?_ hm
        sub_tac
      · next t ht =>
        have htk : Ok m.world (t.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk ht) (Ok_of_subset (by sub_tac) hm)
        split
        · next exit hexit =>
          unfold IterMinted
          refine ⟨World.le_refl _, ?_⟩
          have hex : Ok m.world (primKeys nk sk (interp.exitValue exit mode)) := by
            refine Ok_of_subset (hb.exitValue exit mode) ?_
            have : optExitKeys t.exit = exitKeys exit := by rw [hexit]; rfl
            rw [← this]
            exact Ok_of_subset (by sub_tac) htk
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hex⟩)
          sub_tac
        · unfold IterMinted
          have hweq : ({ m with nextToken := m.nextToken + 1 } : NM ν σ).world = m.world := rfl
          refine ⟨by rw [world_emit, world_update, hweq]; exact World.le_refl _, ?_⟩
          simp only [MintedIn]
          rw [world_emit, world_update, hweq]
          have hname : nk (interp.cancelName interp.parkCancelName f.id m.nextToken) ⊆ [Handle.fiber f.id] := by
            refine List.Subset.trans (hb.cancelName _ _ _) ?_
            rw [hb.parkCancelName]
            exact List.Subset.refl _
          have hn : Ok m.world (nk (interp.cancelName interp.parkCancelName f.id m.nextToken)) :=
            Ok_of_subset hname (Ok_of_subset (by sub_tac) hm)
          have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨hm, htk⟩, hn⟩,
            Ok_cons.mpr ⟨htarget, Ok_nil _⟩⟩
          refine Ok_of_subset ?_ hall
          sub_tac using (keys_update_fibers_subset nk sk _)
    · split
      · next thunk heq =>
        split
        · next action haction =>
          have hak : Ok m.world (action.keys nk sk) := by
            refine Ok_of_subset (hb.withFiberOf thunk action haction) ?_
            rw [heq] at hcur
            simp only [primKeys] at hcur
            exact hcur
          exact withFiber_minted nk sk hb m f yielding action (Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, hak⟩))
        · exact stepFrame_minted_with_ambient nk sk hb m f yielding
            (Ok_append.mpr ⟨ha, Ok_of_subset (by sub_tac) hm⟩)
      · next thunk heq =>
        have hth : Ok m.world (sk thunk) := by
          rw [heq] at hcur
          simp only [primKeys] at hcur
          exact hcur
        split
        · next state value hstep =>
          have hsk : Ok ⟨m.fibers.map RunFiber.id, m.state⟩ (sk thunk ++ m.state.keys) :=
            Ok_append.mpr ⟨hth, Ok_of_subset (by sub_tac) hm⟩
          obtain ⟨hsle, hsok⟩ := hb.syncState thunk m.state state value _ hstep hsk
          have hle : m.world.le ({ m with state := state } : NM ν σ).world := ⟨fun _ h => h, hsle⟩
          unfold IterMinted
          refine ⟨hle, ?_⟩
          simp only [MintedIn]
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩)
          sub_tac
        · unfold IterMinted
          refine ⟨World.le_refl _, ?_⟩
          have hv : Ok m.world (interp.syncValue thunk).keys := Ok_of_subset (hb.syncValue thunk) hth
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hv⟩)
          sub_tac
      · next value heq =>
        refine finalizerOr_minted_with_ambient nk sk hb m f yielding (Exit.success value)
          (Ok_append.mpr ⟨ha, ?_⟩)
        rw [heq] at hcur
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hcur⟩)
        sub_tac
      · next cause heq =>
        refine finalizerOr_minted_with_ambient nk sk hb m f yielding (Exit.failure cause)
          (Ok_append.mpr ⟨ha, ?_⟩)
        change Ok m.world (m.keys nk sk ++ f.keys nk sk ++ [])
        rw [List.append_nil]
        exact (Ok_cons.mp hm).2
      · exact stepFrame_minted_with_ambient nk sk hb m f yielding
          (Ok_append.mpr ⟨ha, (Ok_cons.mp hm).2⟩)


/-! Empty-ambient specializations retain the original public frame statements. -/

theorem armA_keys (hb : KeyBounded nk sk interp) (frame : Prim ν σ Val Err Defect FiberId Ann)
    (value : Val) (provided : Option ExitV) (next : Prim ν σ Val Err Defect FiberId Ann)
    (pushed : List (Prim ν σ Val Err Defect FiberId Ann))
    (h : frame.armA interp.toPrimInterp value provided = some (next, pushed)) :
    primKeys nk sk next ++ pushed.flatMap (primKeys nk sk) ⊆
      primKeys nk sk frame ++ value.keys ++ optExitKeys provided :=
  armA_keys_with_ambient nk sk hb frame value provided next pushed h

theorem armE_keys (hb : KeyBounded nk sk interp) (frame : Prim ν σ Val Err Defect FiberId Ann)
    (cause : CauseV) (provided : Option ExitV) (next : Prim ν σ Val Err Defect FiberId Ann)
    (pushed : List (Prim ν σ Val Err Defect FiberId Ann))
    (h : frame.armE interp.toPrimInterp cause provided = some (next, pushed)) :
    primKeys nk sk next ++ pushed.flatMap (primKeys nk sk) ⊆
      primKeys nk sk frame ++ optExitKeys provided :=
  armE_keys_with_ambient nk sk hb frame cause provided next pushed h

theorem resumeValue_keys (hb : KeyBounded nk sk interp)
    (self : FrameFiber ν σ Val Err Defect FiberId Ann) (value : Val) (provided : Option ExitV) :
    stepKeys nk sk (self.resumeValue interp.toPrimInterp value provided).1 ⊆
      frameKeys nk sk self ++ value.keys ++ optExitKeys provided :=
  resumeValue_keys_with_ambient nk sk hb self value provided

theorem resumeCause_keys (hb : KeyBounded nk sk interp)
    (self : FrameFiber ν σ Val Err Defect FiberId Ann) (cause : CauseV) (provided : Option ExitV) :
    stepKeys nk sk (self.resumeCause interp.toPrimInterp cause provided).1 ⊆
      frameKeys nk sk self ++ optExitKeys provided :=
  resumeCause_keys_with_ambient nk sk hb self cause provided

theorem step_keys (hb : KeyBounded nk sk interp) (self : FrameFiber ν σ Val Err Defect FiberId Ann) :
    stepKeys nk sk (self.step interp.toPrimInterp).1 ⊆ frameKeys nk sk self :=
  step_keys_with_ambient nk sk hb self

theorem stepFrame_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (m.keys nk sk ++ f.keys nk sk)) :
    IterMinted nk sk m (evaluatePrim.stepFrame interp m f yielding) :=
  stepFrame_minted_with_ambient nk sk hb m f yielding hm

theorem finalizerOr_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (hm : MintedIn m (m.keys nk sk ++ f.keys nk sk ++ exitKeys exit)) :
    IterMinted nk sk m (evaluatePrim.finalizerOr interp m f yielding exit) :=
  finalizerOr_minted_with_ambient nk sk hb m f yielding exit hm

theorem evaluatePrim_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk)) :
    IterMinted nk sk m (evaluatePrim interp m f yielding) :=
  evaluatePrim_minted_with_ambient nk sk hb m f yielding hm

section EvaluatorTransport

variable [evaluator : FiberEvaluator ν σ Val Err Defect FiberId Ann Ctx Stores
  (Prim ν σ Val Err Defect FiberId Ann) (FrameFiber ν σ Val Err Defect FiberId Ann)
  (FrameEvent ν σ Val Err Defect FiberId Ann)]

/-- An evaluator grows the world and returns only handles already allocated there.
The shared command proof uses this premise at the actual machine being evaluated. -/
def EvaluatorMinted (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  ∀ (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool),
    MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk) →
      IterMinted nk sk m (evaluator.evaluate interp m f yielding)

theorem iteration_minted_of_evaluator (hEval : EvaluatorMinted nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk)) :
    IterMinted nk sk m (iteration interp m f yielding) := by
  have hf' : (countOp (runloopTop f)).keys nk sk ⊆ f.keys nk sk := by
    unfold countOp runloopTop
    split
    · simp only [RunFiber.keys, frameKeys, primKeys, List.nil_append]
      sub_tac
    · exact List.Subset.refl _
  have hid : (countOp (runloopTop f)).id = f.id := by
    unfold countOp runloopTop
    split <;> rfl
  have hm' : MintedIn m (Handle.fiber (countOp (runloopTop f)).id :: m.keys nk sk ++
      (countOp (runloopTop f)).keys nk sk) := by
    rw [hid]
    exact Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, Ok_of_subset hf' (Ok_of_subset (by sub_tac) hm)⟩)
  unfold iteration
  try dsimp only
  split
  · next it hit =>
    unfold injectYield at hit
    split at hit
    · cases hit
      let g := countOp (runloopTop f)
      let next : RunFiber ν σ Val Err Defect FiberId Ann Ctx :=
        { g with
          yieldOverride := none
          frame := { g.frame with current := Prim.onSuccessConst (Prim.yieldNowWith 0) g.frame.current } }
      exact hEval
        (m.emit [RunEvent.yieldInjected g.id g.currentOpCount]) next true
        (by simpa only [next, MintedIn, RunMachine.world, RunMachine.emit, RunMachine.keys,
          RunFiber.keys, frameKeys, primKeys, List.nil_append] using hm')
    · cases hit
  · exact hEval m _ yielding hm'

omit evaluator in
theorem settle_minted (id : FiberId) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores)
    (hm : MintedIn it.machine (iterKeys nk sk it ++ cmdsKeys nk sk rest)) :
    it.machine.world.le (settle id rest it).1.world ∧
      MintedIn (settle id rest it).1 ((settle id rest it).1.keys nk sk ++ cmdsKeys nk sk (settle id rest it).2) := by
  unfold settle
  split
  · refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update]
    refine Ok_of_subset ?_ hm
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
  · refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update]
    refine Ok_of_subset ?_ hm
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
  · -- parked: with a deferred interrupt the park is cleared and the entry continues (D6a)
    split
    · refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_update]
      refine Ok_of_subset ?_ hm
      refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
    · refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_update]
      refine Ok_of_subset ?_ hm
      refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
  · -- commands: the nested work decides the continuation (D6a)
    refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update]
    refine Ok_of_subset ?_ hm
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
  · next exit heq =>
    refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update]
    simp only [iterKeys, heq, Outcome.keys] at hm
    refine Ok_of_subset ?_ hm
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩
  · refine ⟨by rw [world_halt, world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_halt, world_update]
    refine Ok_of_subset ?_ hm
    rw [keys_halt]
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩

omit evaluator in
theorem flatMap_resume_map (due : List (FiberId × Nat × Prim ν σ Val Err Defect FiberId Ann)) :
    (due.map fun d => Cmd.resume d.1 d.2.1 d.2.2).flatMap (Cmd.keys nk sk) =
      due.flatMap fun d => primKeys nk sk d.2.2 := by
  induction due with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, List.flatMap_cons, Cmd.keys] at ih ⊢
    rw [ih]

/-- The receipt of one command: the world grew and the loop's handles (the machine's and the
remaining commands') exist afterwards. One lemma per command, then the dispatch. -/
def StepMinted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (r : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × List (Cmd ν σ Val Err Defect FiberId Ann)) : Prop :=
  m.world.le r.1.world ∧ MintedIn r.1 (r.1.keys nk sk ++ cmdsKeys nk sk r.2)

theorem driveStep_evaluate_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.evaluate id :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.evaluate id) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    split
    · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
    · refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit, world_update]
      have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) (Ok_of_subset (by sub_tac) hm)
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hfk⟩)
      rw [keys_emit]
      refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), by sub_tac⟩

theorem driveStep_loop_minted_of_evaluator (hEval : EvaluatorMinted nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (yielding : Bool)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.loop id yielding :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.loop id yielding) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) (Ok_of_subset (by sub_tac) hm)
    have hfid : (Handle.fiber f.id).existsIn m.world = true := fiber?_exists hf
    obtain ⟨hle, hit⟩ := iteration_minted_of_evaluator nk sk hEval m f yielding
      (Ok_cons.mpr ⟨hfid, Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hm, hfk⟩⟩)
    obtain ⟨hle', hok⟩ := settle_minted nk sk id rest (iteration interp m f yielding)
      (Ok_append.mpr ⟨hit, Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩)
    exact ⟨World.le_trans hle hle', hok⟩

theorem driveStep_deliver_minted_of_evaluator (hEval : EvaluatorMinted nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (yielding : Bool)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.deliver id yielding :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.deliver id yielding) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) (Ok_of_subset (by sub_tac) hm)
    have hfid : (Handle.fiber f.id).existsIn m.world = true := fiber?_exists hf
    obtain ⟨hle, hit⟩ := hEval m f yielding
      (Ok_cons.mpr ⟨hfid, Ok_append.mpr ⟨Ok_of_subset (by sub_tac) hm, hfk⟩⟩)
    obtain ⟨hle', hok⟩ := settle_minted nk sk id rest (evaluator.evaluate interp m f yielding)
      (Ok_append.mpr ⟨hit, Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩)
    exact ⟨World.le_trans hle hle', hok⟩

theorem driveStep_resume_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId)
    (token : Nat) (answer : Prim ν σ Val Err Defect FiberId Ann) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.resume id token answer :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.resume id token answer) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next t ht =>
    split
    · split
      · refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
        simp only [MintedIn]
        rw [world_emit, world_update]
        have htk : Ok m.world (t.keys nk sk) :=
          Ok_of_subset (fiber?_keys_subset nk sk ht) (Ok_of_subset (by sub_tac) hm)
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, htk⟩)
        rw [keys_emit]
        refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) ?_, by sub_tac⟩
        simp only [RunFiber.keys, frameKeys]
        sub_tac using (flatMap_filter_subset (Pending.keys nk) _ t.pending)
      · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
    · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩

theorem driveStep_launch_minted (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.launch raceId :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.launch raceId) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next race hrace =>
    split
    · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
    · next program more hprog =>
      split
      · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
      · split
        · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
        · next host hhost =>
          have hrk : Ok m.world (race.keys nk sk) :=
            Ok_of_subset (race?_keys_subset nk sk hrace) (Ok_of_subset (by sub_tac) hm)
          have hprogk : Ok m.world (primKeys nk sk program ++ more.flatMap (primKeys nk sk)) := by
            refine Ok_of_subset ?_ hrk
            simp only [Race.keys, hprog, List.flatMap_cons]
            sub_tac
          have hhk : Ok m.world (host.keys nk sk) :=
            Ok_of_subset (fiber?_keys_subset nk sk hhost) (Ok_of_subset (by sub_tac) hm)
          have hhid : (Handle.fiber host.id).existsIn m.world = true := fiber?_exists hhost
          have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
          have hpk : Ok m.world (primKeys nk sk program) := Ok_of_subset (by sub_tac) hprogk
          obtain ⟨hle, hL⟩ := launchEntrant_minted nk sk interp raceId m host program
            (Ok_cons.mpr ⟨hhid, Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hhk⟩, hpk⟩⟩)
          generalize hLdef : launchEntrant interp raceId m host program = L at hle hL ⊢
          refine ⟨by rw [world_emit, world_updateRace]; exact hle, ?_⟩
          simp only [MintedIn]
          rw [world_emit, world_updateRace]
          have hall : Ok L.1.world (Handle.fiber L.2 :: L.1.keys nk sk ++ race.keys nk sk ++
              (m.keys nk sk ++ cmdsKeys nk sk (Cmd.launch raceId :: rest)) ++
              (primKeys nk sk program ++ more.flatMap (primKeys nk sk))) :=
            Ok_append.mpr ⟨Ok_append.mpr ⟨Ok_append.mpr ⟨hL, Ok_mono hle hrk⟩, Ok_mono hle hm⟩,
              Ok_mono hle hprogk⟩
          refine Ok_of_subset ?_ hall
          rw [keys_emit]
          refine List.append_subset.mpr ⟨List.Subset.trans (keys_updateRace_subset nk sk _) ?_, by sub_tac⟩
          sub_tac

/-- An entrant's enrollment (D6a): the race gains the child in its live set, and the race
callback is attached to a live child or fired at once on an exited one. -/
theorem driveStep_enrollRace_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat) (child : FiberId)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.enrollRace raceId child :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.enrollRace raceId child) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · next race c hrace hc =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hrest : Ok m.world (cmdsKeys nk sk rest) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys, List.nil_append]
      exact List.subset_append_right _ _
    have hrk : Ok m.world (race.keys nk sk) := Ok_of_subset (race?_keys_subset nk sk hrace) hmk
    have hcid : (Handle.fiber child).existsIn m.world = true := by
      have := fiber?_exists hc
      rwa [fiber?_id hc] at this
    have hck : Ok m.world (c.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hc) hmk
    have hM : Ok m.world ((m.updateRace { race with state :=
        { race.state with live := race.state.live ++ [child] } }).keys nk sk) := by
      refine Ok_of_subset (keys_updateRace_subset nk sk _) (Ok_append.mpr ⟨hmk, ?_⟩)
      refine Ok_of_subset ?_ (Ok_cons.mpr ⟨hcid, hrk⟩)
      simp only [Race.keys, List.map_append, List.map_cons, List.map_nil]
      sub_tac
    split
    · next exit hexit =>
      have hex : Ok m.world (exitKeys exit) := by
        have : optExitKeys c.exit = exitKeys exit := by rw [hexit]; rfl
        rw [← this]
        exact Ok_of_subset (by sub_tac) hck
      obtain ⟨hle, hF⟩ := fireObserver_raceCallback_minted nk sk hb child exit
        (m.updateRace { race with state := { race.state with live := race.state.live ++ [child] } }, [])
        raceId (by
          simp only [MintedIn]
          rw [world_updateRace]
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨hM, hex⟩)
          simp only [cmdsKeys, List.flatMap_nil, List.append_nil, Observer.keys]
          exact List.Subset.refl _)
      rw [world_updateRace] at hle
      generalize fireObserver interp child exit
        (m.updateRace { race with state := { race.state with live := race.state.live ++ [child] } }, [])
        (Observer.raceCallback raceId) = R at hle hF ⊢
      obtain ⟨R1, R2⟩ := R
      dsimp only
      refine ⟨hle, ?_⟩
      simp only [MintedIn] at hF ⊢
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨hF, Ok_mono hle hrest⟩)
      simp only [cmdsKeys, List.flatMap_append]
      sub_tac
    · refine ⟨by rw [world_modify, world_updateRace]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_modify, world_updateRace]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨hM, hrest⟩)
      refine List.append_subset.mpr ⟨?_, List.subset_append_right _ _⟩
      refine List.Subset.trans (keys_modify_subset nk sk _ _ [] fun g => ?_) ?_
      · simp only [RunFiber.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Observer.keys,
          List.append_nil]
        sub_tac
      · sub_tac
  all_goals exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩

/-- The registration's return (D6a): a buffered answer installs the settle program, whose
handles are the accepted exit's; no answer pushes the race's cancel name and parks. Both
continue through `settle`. -/
theorem driveStep_registrationDone_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat) (yielding : Bool)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.registrationDone raceId yielding :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.registrationDone raceId yielding) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next race hrace =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hrest : Ok m.world (cmdsKeys nk sk rest) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys, List.nil_append]
      exact List.subset_append_right _ _
    have hrk : Ok m.world (race.keys nk sk) := Ok_of_subset (race?_keys_subset nk sk hrace) hmk
    have hM : Ok m.world ((m.updateRace { race with registering := false }).keys nk sk) := by
      refine Ok_of_subset (keys_updateRace_subset nk sk _) (Ok_append.mpr ⟨hmk, ?_⟩)
      refine Ok_of_subset ?_ hrk
      simp only [Race.keys]
      exact List.Subset.refl _
    split
    · refine ⟨by rw [world_updateRace]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_updateRace]
      exact Ok_append.mpr ⟨hM, hrest⟩
    · next f hf =>
      have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) hM
      have hfid : (Handle.fiber f.id).existsIn m.world = true := by
        have := fiber?_exists hf
        rwa [world_updateRace] at this
      split
      · next exit hexit =>
        have hex : Ok m.world (exitKeys exit) := by
          have : optExitKeys race.state.accepted = exitKeys exit := by rw [hexit]; rfl
          rw [← this]
          refine Ok_of_subset ?_ hrk
          simp only [Race.keys]
          sub_tac
        have hcode : Ok m.world (primKeys nk sk (interp.raceSettle raceId race.state.cleanupNeeded exit)) :=
          Ok_of_subset (hb.raceSettle _ _ _) hex
        obtain ⟨hle, hS⟩ := settle_minted nk sk f.id rest
          ⟨m.updateRace { race with registering := false },
            { f with frame := { f.frame with
                current := interp.raceSettle raceId race.state.cleanupNeeded exit } },
            yielding, Outcome.continue_, []⟩ (by
          simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_nil, List.append_nil, Outcome.keys]
          rw [world_updateRace]
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hM, hfk⟩, Ok_append.mpr ⟨hcode, hrest⟩⟩)
          simp only [RunFiber.keys, frameKeys]
          sub_tac)
        rw [world_updateRace] at hle
        exact ⟨hle, hS⟩
      · have hname : nk (interp.cancelName (interp.raceCancelName raceId) f.id race.token) ⊆
            [Handle.fiber f.id] := by
          refine List.Subset.trans (hb.cancelName _ _ _) ?_
          rw [hb.raceCancelName]
          exact List.Subset.refl _
        have hn : Ok m.world (nk (interp.cancelName (interp.raceCancelName raceId) f.id race.token)) :=
          Ok_of_subset hname (Ok_cons.mpr ⟨hfid, Ok_nil _⟩)
        obtain ⟨hle, hS⟩ := settle_minted nk sk f.id rest
          ⟨(m.updateRace { race with registering := false }).emit [RunEvent.parkedOn f.id race.token],
            ({ f with frame := { f.frame with
                stack := Prim.asyncFinalizer (interp.cancelName (interp.raceCancelName raceId) f.id race.token) :: f.frame.stack } }).park
              ⟨race.token, none, [], [], Resume.void, false⟩,
            yielding, Outcome.parked, []⟩ (by
          simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_nil, List.append_nil, Outcome.keys]
          rw [world_emit, world_updateRace]
          refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hM, hfk⟩, Ok_append.mpr ⟨hn, hrest⟩⟩)
          rw [keys_emit]
          simp only [RunFiber.keys, RunFiber.park, frameKeys, List.flatMap_append, List.flatMap_cons,
            List.flatMap_nil, primKeys, Pending.keys, Option.map, Option.toList, Resume.keys]
          sub_tac)
        rw [world_emit, world_updateRace] at hle
        exact ⟨hle, hS⟩

theorem driveStep_link_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.link mode scope target interruptor extra :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.link mode scope target interruptor extra) rest) := by
  unfold StepMinted
  simp only [driveStep]
  obtain ⟨hle, hok⟩ := linkScope_minted nk sk hb m mode scope target interruptor extra
    (Ok_of_subset (by sub_tac) hm)
  generalize hLdef : linkScope interp m mode scope target interruptor extra = L at hle hok ⊢
  refine ⟨hle, ?_⟩
  have hall : Ok L.1.world (L.1.keys nk sk ++ cmdsKeys nk sk L.2 ++
      (m.keys nk sk ++ cmdsKeys nk sk (Cmd.link mode scope target interruptor extra :: rest))) :=
    Ok_append.mpr ⟨hok, Ok_mono hle hm⟩
  refine Ok_of_subset ?_ hall
  sub_tac

theorem driveStep_finish_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (exit : ExitV)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.finish id exit :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.finish id exit) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) (Ok_of_subset (by sub_tac) hm)
    have hfk' : Ok m.world (({ f with running := false } : RunFiber ν σ Val Err Defect FiberId Ann Ctx).keys nk sk) :=
      Ok_of_subset (by sub_tac) hfk
    have hfid : (Handle.fiber f.id).existsIn m.world = true := fiber?_exists hf
    have hex : Ok m.world (exitKeys exit) := Ok_of_subset (by sub_tac) hm
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    obtain ⟨hle, hE⟩ := exitFiber_minted nk sk hb m { f with running := false } exit
      (Ok_cons.mpr ⟨hfid, Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hfk'⟩, hex⟩⟩)
    generalize hEdef : exitFiber interp m { f with running := false } exit = E at hle hE ⊢
    obtain ⟨E1, E2⟩ := E
    dsimp only
    refine ⟨hle, ?_⟩
    simp only [MintedIn] at hE ⊢
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hE, Ok_mono hle hm⟩)
    simp only [cmdsKeys, List.flatMap_append]
    sub_tac

/-- One `interruptUnsafe` as a command (D6b): the target is re-read and recorded; the
evaluation it may owe carries no handle. -/
theorem driveStep_interruptTarget_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.interruptTarget target who extra :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.interruptTarget target who extra) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next g hg =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hrest : Ok m.world (cmdsKeys nk sk rest) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
      sub_tac
    have hX : Ok m.world ((interruptRecord interp who extra g).1.keys nk sk) :=
      Ok_of_subset (List.Subset.trans (interruptRecord_keys_subset nk sk interp who extra g)
        (fiber?_keys_subset nk sk hg)) hmk
    refine ⟨by rw [world_emit, world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_emit, world_update]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hX⟩, hrest⟩)
    rw [keys_emit]
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), ?_⟩
    split <;>
      simp only [cmdsKeys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Cmd.keys,
        List.nil_append, List.append_nil] <;>
      sub_tac

/-- `asVoid` adds only the void exit's (empty) keys (D6b). -/
theorem asVoidCode_keys_subset (hb : KeyBounded nk sk interp ambient)
    (code : Prim ν σ Val Err Defect FiberId Ann) :
    primKeys nk sk (asVoidCode interp code) ⊆ primKeys nk sk code := by
  simp only [asVoidCode, FiberCore.onSuccess, primKeys]
  refine List.append_subset.mpr ⟨List.Subset.refl _, ?_⟩
  refine List.Subset.trans (hb.restoreName _) ?_
  simp only [exitKeys, hb.voidValue]
  exact List.nil_subset _

/-- The await an interrupt returns names the park's targets, or an exit the machine holds
(D6b). -/
theorem awaitCode_keys_subset (hb : KeyBounded nk sk interp ambient)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (kind : ParkKind) :
    primKeys nk sk (awaitCode interp m kind) ⊆ kind.keys ++ m.keys nk sk := by
  cases kind with
  | join target mode =>
    cases hft : m.fiber? target with
    | none =>
      have h : awaitCode interp m (ParkKind.join target mode) = interp.parkCode (ParkKind.join target mode) := by
        simp [awaitCode, hft]
      rw [h]
      exact List.Subset.trans (hb.parkCode _) (List.subset_append_left _ _)
    | some t =>
      cases hx : t.exit with
      | none =>
        rw [awaitCode_join_live interp m target mode t hft hx]
        exact List.Subset.trans (hb.parkCode _) (List.subset_append_left _ _)
      | some exit =>
        rw [awaitCode_join_exited interp m target mode t exit hft hx]
        refine List.Subset.trans (hb.exitValue _ _)
          (List.Subset.trans ?_ (List.subset_append_right _ _))
        refine List.Subset.trans ?_ (fiber?_keys_subset nk sk hft)
        have : optExitKeys t.exit = exitKeys exit := by rw [hx]; rfl
        rw [← this]
        simp only [RunFiber.keys]
        sub_tac
  | race raceId => exact List.Subset.trans (hb.parkCode _) (List.subset_append_left _ _)
  | awaitAll targets => exact List.Subset.trans (hb.parkCode _) (List.subset_append_left _ _)

/-- The return of an interrupt (D6b): the host is re-read and continues with `asVoid` of the
await code, which names the park's targets or an exit the machine holds. -/
theorem driveStep_afterInterrupt_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (host : FiberId) (yielding : Bool)
    (kind : ParkKind) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.afterInterrupt host yielding kind :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.afterInterrupt host yielding kind) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hrest : Ok m.world (cmdsKeys nk sk rest) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
      sub_tac
    have hkind : Ok m.world kind.keys := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
      sub_tac
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) hmk
    have hcode : Ok m.world (primKeys nk sk (asVoidCode interp (awaitCode interp m kind))) :=
      Ok_of_subset (asVoidCode_keys_subset nk sk hb _)
        (Ok_of_subset (awaitCode_keys_subset nk sk hb m kind) (Ok_append.mpr ⟨hkind, hmk⟩))
    obtain ⟨hle, hS⟩ := settle_minted nk sk f.id rest
      ⟨m, { f with frame := { f.frame with current := asVoidCode interp (awaitCode interp m kind) } },
        yielding, Outcome.continue_, []⟩ (by
      simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_nil, List.append_nil, Outcome.keys]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hfk⟩, Ok_append.mpr ⟨hcode, hrest⟩⟩)
      simp only [RunFiber.keys, frameKeys]
      sub_tac)
    exact ⟨hle, hS⟩

/-- The parallel close's await (§20): the closer's frame gains the closed generator name over
the void cursor and the await park over minted fibers. -/
theorem driveStep_closeParAwait_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (host : FiberId) (yielding : Bool)
    (fibers : List FiberId) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.closeParAwait host yielding fibers :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.closeParAwait host yielding fibers) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hrest : Ok m.world (cmdsKeys nk sk rest) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
      sub_tac
    have hfibers : Ok m.world (fibers.map Handle.fiber) := by
      refine Ok_of_subset ?_ hm
      simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
      sub_tac
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) hmk
    have hcode : Ok m.world (primKeys nk sk (interp.parkCode (ParkKind.awaitAll fibers))) :=
      Ok_of_subset (hb.parkCode _) (by simpa only [ParkKind.keys] using hfibers)
    obtain ⟨hle, hS⟩ := settle_minted nk sk f.id rest
      ⟨m, { f with frame := { f.frame with
          current := interp.parkCode (ParkKind.awaitAll fibers)
          stack := Prim.iterator interp.closeDoneName interp.voidValue :: f.frame.stack } },
        yielding, Outcome.continue_, []⟩ (by
      simp only [MintedIn, iterKeys, cmdsKeys, List.flatMap_nil, List.append_nil, Outcome.keys]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hfk⟩, Ok_append.mpr ⟨hcode, hrest⟩⟩)
      simp only [RunFiber.keys, frameKeys, List.flatMap_cons, primKeys, hb.closeDoneName, hb.voidValue,
        List.nil_append]
      sub_tac)
    exact ⟨hle, hS⟩

/-- The race cleanup's Set walk (D6b) changes no machine; every command it issues names the
host and members of the walk. -/
theorem driveStep_raceCancel_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (raceId : Nat) (host : FiberId)
    (yielding : Bool) (remaining visited : List FiberId) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++
      cmdsKeys nk sk (Cmd.raceCancel raceId host yielding remaining visited :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.raceCancel raceId host yielding remaining visited) rest) := by
  unfold StepMinted
  simp only [driveStep]
  (repeat' split) <;> refine ⟨World.le_refl _, ?_⟩ <;> refine Ok_of_subset ?_ hm <;>
    simp only [cmdsKeys, List.flatMap_cons, Cmd.keys, ParkKind.keys, List.map_append, List.map_cons,
      List.map_nil, List.append_nil] <;>
    sub_tac

/-- Tracking a child (D6b): the parent gains the child, the child the untrack observer. -/
theorem driveStep_trackChild_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (parent child : FiberId)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.trackChild parent child :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.trackChild parent child) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next c hc =>
    split
    · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
    · have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
      have hrest : Ok m.world (cmdsKeys nk sk rest) := by
        refine Ok_of_subset ?_ hm
        simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
        sub_tac
      have hpc : Ok m.world [Handle.fiber parent, Handle.fiber child] := by
        refine Ok_of_subset ?_ hm
        simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
        sub_tac
      refine ⟨by rw [world_modify, world_modify]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_modify, world_modify]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨Ok_append.mpr ⟨hmk, hpc⟩, hrest⟩)
      refine List.append_subset.mpr ⟨?_, by sub_tac⟩
      -- the child's new observer names the parent; the parent's new child names the child
      have hinner : ((m.modify parent fun p => { p with children := p.children ++ [child] }).keys nk sk) ⊆
          m.keys nk sk ++ [Handle.fiber child] := by
        refine keys_modify_subset nk sk _ _ [Handle.fiber child] fun p => ?_
        simp only [RunFiber.keys, List.map_append, List.map_cons, List.map_nil]
        sub_tac
      refine List.Subset.trans (keys_modify_subset nk sk _ _ [Handle.fiber parent] fun g => ?_) ?_
      · simp only [RunFiber.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Observer.keys,
          List.append_nil]
        sub_tac
      · refine List.append_subset.mpr ⟨List.Subset.trans hinner ?_, ?_⟩ <;> sub_tac

/-- One exit observer as a command (D6b): `fireObserver` on the current machine. -/
theorem driveStep_observe_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (exit : ExitV)
    (observer : Observer) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.observe id exit observer :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.observe id exit observer) rest) := by
  unfold StepMinted
  simp only [driveStep]
  have hrest : Ok m.world (cmdsKeys nk sk rest) := by
    refine Ok_of_subset ?_ hm
    simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
    sub_tac
  obtain ⟨hle, hF⟩ := fireObserver_minted nk sk hb id exit (m, []) observer (by
    simp only [MintedIn, cmdsKeys, List.flatMap_nil, List.append_nil]
    refine Ok_of_subset ?_ hm
    simp only [cmdsKeys, List.flatMap_cons, Cmd.keys]
    sub_tac)
  generalize fireObserver interp id exit (m, []) observer = R at hle hF ⊢
  obtain ⟨R1, R2⟩ := R
  dsimp only
  refine ⟨hle, ?_⟩
  simp only [MintedIn] at hF ⊢
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hF, Ok_mono hle hrest⟩)
  simp only [cmdsKeys, List.flatMap_append]
  sub_tac

/-- The end of the exit path (D6b): the fiber is cleared. -/
theorem driveStep_exitDone_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.exitDone id :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.exitDone id) rest) := by
  unfold StepMinted
  simp only [driveStep]
  split
  · exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
  · next f hf =>
    have hmk : Ok m.world (m.keys nk sk) := Ok_of_subset (by sub_tac) hm
    have hfk : Ok m.world (f.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk hf) hmk
    have hclr : (f.cleared interp).keys nk sk ⊆ f.keys nk sk := by
      simp only [RunFiber.cleared, RunFiber.keys, frameKeys, FiberCore.clearStack, hb.emptyContext,
        List.flatMap_nil, List.map_nil, List.append_nil]
      sub_tac
    refine ⟨by rw [world_update]; exact World.le_refl _, ?_⟩
    simp only [MintedIn]
    rw [world_update]
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, Ok_of_subset hclr hfk⟩)
    refine List.append_subset.mpr ⟨List.Subset.trans (keys_update_subset nk sk _) (by sub_tac), ?_⟩
    simp only [cmdsKeys, List.flatMap_cons, Cmd.keys, List.nil_append]
    sub_tac

theorem driveStep_drainDue_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.drainDue :: rest))) :
    StepMinted nk sk m (driveStep interp m Cmd.drainDue rest) := by
  unfold StepMinted
  simp only [driveStep]
  have hsk : Ok ⟨m.fibers.map RunFiber.id, m.state⟩ m.state.keys := Ok_of_subset (by sub_tac) hm
  obtain ⟨hsle, hsok⟩ := hb.dueResumes m.state _ hsk
  have hle : m.world.le ({ m with state := (interp.dueResumes m.state).2 } : NM ν σ).world :=
    ⟨fun _ h => h, hsle⟩
  refine ⟨hle, ?_⟩
  simp only [MintedIn]
  have hall : Ok ({ m with state := (interp.dueResumes m.state).2 } : NM ν σ).world
      ((m.keys nk sk ++ cmdsKeys nk sk (Cmd.drainDue :: rest)) ++
        ((interp.dueResumes m.state).2.keys ++ (interp.dueResumes m.state).1.flatMap fun d => primKeys nk sk d.2.2)) :=
    Ok_append.mpr ⟨Ok_mono hle hm, hsok⟩
  refine Ok_of_subset ?_ hall
  simp only [cmdsKeys, List.flatMap_append, flatMap_resume_map]
  sub_tac

theorem driveStep_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (cmd : Cmd ν σ Val Err Defect FiberId Ann)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (cmd :: rest))) :
    m.world.le (driveStep interp m cmd rest).1.world ∧
      MintedIn (driveStep interp m cmd rest).1
        ((driveStep interp m cmd rest).1.keys nk sk ++ cmdsKeys nk sk (driveStep interp m cmd rest).2) := by
  cases cmd with
  | evaluate id => exact driveStep_evaluate_minted nk sk m id rest hm
  | loop id yielding => exact driveStep_loop_minted_of_evaluator nk sk hEval m id yielding rest hm
  | deliver id yielding => exact driveStep_deliver_minted_of_evaluator nk sk hEval m id yielding rest hm
  | resume id token answer => exact driveStep_resume_minted nk sk m id token answer rest hm
  | launch raceId => exact driveStep_launch_minted nk sk m raceId rest hm
  | enrollRace raceId child => exact driveStep_enrollRace_minted nk sk hb m raceId child rest hm
  | registrationDone raceId yielding =>
    exact driveStep_registrationDone_minted nk sk hb m raceId yielding rest hm
  | interruptTarget target who extra =>
    exact driveStep_interruptTarget_minted nk sk hb m target who extra rest hm
  | afterInterrupt host yielding kind =>
    exact driveStep_afterInterrupt_minted nk sk hb m host yielding kind rest hm
  | raceCancel raceId host yielding remaining visited =>
    exact driveStep_raceCancel_minted nk sk hb m raceId host yielding remaining visited rest hm
  | trackChild parent child => exact driveStep_trackChild_minted nk sk hb m parent child rest hm
  | observe id exit observer => exact driveStep_observe_minted nk sk hb m id exit observer rest hm
  | exitDone id => exact driveStep_exitDone_minted nk sk hb m id rest hm
  | closeParAwait host yielding fibers =>
    exact driveStep_closeParAwait_minted nk sk hb m host yielding fibers rest hm
  | link mode scope target interruptor extra =>
    exact driveStep_link_minted nk sk hb m mode scope target interruptor extra rest hm
  | finish id exit => exact driveStep_finish_minted nk sk hb m id exit rest hm
  | drainDue => exact driveStep_drainDue_minted nk sk hb m rest hm

/-- The command loop keeps every handle it holds and every handle its commands carry. -/
theorem driveState_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) :
    ∀ (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (cmds : List (Cmd ν σ Val Err Defect FiberId Ann)),
      MintedIn m (m.keys nk sk ++ cmdsKeys nk sk cmds) →
      m.world.le (driveState interp fuel m cmds).1.world ∧
        MintedIn (driveState interp fuel m cmds).1
          ((driveState interp fuel m cmds).1.keys nk sk ++ cmdsKeys nk sk (driveState interp fuel m cmds).2) := by
  induction fuel with
  | zero => intro m cmds hm; exact ⟨World.le_refl _, hm⟩
  | succ fuel ih =>
    intro m cmds hm
    cases cmds with
    | nil => rw [driveState_nil]; exact ⟨World.le_refl _, Ok_of_subset (by sub_tac) hm⟩
    | cons cmd rest =>
      rw [driveState_succ_cons]
      split
      · exact ⟨World.le_refl _, hm⟩
      · obtain ⟨hle, hstep⟩ := driveStep_minted_of_evaluator nk sk hb hEval m cmd rest hm
        obtain ⟨hle', hok⟩ := ih _ _ hstep
        exact ⟨World.le_trans hle hle', hok⟩

/-! ## The decisions

A dispatcher task carries its handles into the loop; a decision answers with a completion
whose handles the tape premise `AnswersValidAt` makes exist. Everything else a decision does
is the loop. -/

omit evaluator in
theorem cmdsKeys_taskCmds (task : Task ν σ Val Err Defect FiberId Ann) :
    cmdsKeys nk sk (taskCmds task) ⊆ task.keys nk sk := by
  cases task with
  | start child =>
    simp only [taskCmds, cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil]
    exact List.nil_subset _
  | resume target token answer =>
    simp only [taskCmds, cmdsKeys, List.flatMap_cons, List.flatMap_nil, Cmd.keys, List.append_nil, Task.keys]
    exact List.subset_cons_of_subset _ (List.Subset.refl _)

omit evaluator in
theorem flatten_tasks_keys :
    ∀ bs : List (Bucket ν σ Val Err Defect FiberId Ann),
      ((bs.map Bucket.tasks).flatten).flatMap (Task.keys nk sk) =
        bs.flatMap fun b => b.tasks.flatMap (Task.keys nk sk)
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.flatten_cons, List.flatMap_append, List.flatMap_cons]
    rw [flatten_tasks_keys bs]

theorem fireStep_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) (owner : FiberId)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × Bool) (task : Task ν σ Val Err Defect FiberId Ann)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ task.keys nk sk)) :
    acc.1.world.le (fireStep interp fuel owner acc task).1.world ∧
      MintedAt nk sk (fireStep interp fuel owner acc task).1 := by
  unfold fireStep
  split
  · try dsimp only
    obtain ⟨hle, hok⟩ := driveState_minted_of_evaluator nk sk hb hEval fuel (acc.1.emit [RunEvent.ranTask owner task]) (taskCmds task)
      (by
        simp only [MintedIn]
        rw [world_emit]
        refine Ok_of_subset ?_ hm
        sub_tac using (cmdsKeys_taskCmds nk sk task))
    rw [world_emit] at hle
    exact ⟨hle, Ok_of_subset (List.subset_append_left _ _) hok⟩
  · exact ⟨World.le_refl _, Ok_of_subset (List.subset_append_left _ _) hm⟩

theorem fireTasks_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) (owner : FiberId) :
    ∀ (tasks : List (Task ν σ Val Err Defect FiberId Ann))
      (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × Bool),
      MintedIn acc.1 (acc.1.keys nk sk ++ tasks.flatMap (Task.keys nk sk)) →
      acc.1.world.le (tasks.foldl (fireStep interp fuel owner) acc).1.world ∧
        MintedAt nk sk (tasks.foldl (fireStep interp fuel owner) acc).1
  | [], acc, hm => ⟨World.le_refl _, Ok_of_subset (List.subset_append_left _ _) hm⟩
  | task :: tasks, acc, hm => by
    rw [List.foldl_cons]
    obtain ⟨hle, hok⟩ := fireStep_minted_of_evaluator nk sk hb hEval fuel owner acc task (Ok_of_subset (by sub_tac) hm)
    obtain ⟨hle', hok'⟩ := fireTasks_minted_of_evaluator hb hEval fuel owner tasks (fireStep interp fuel owner acc task)
      (Ok_append.mpr ⟨hok, Ok_mono hle (Ok_of_subset (by sub_tac) hm)⟩)
    exact ⟨World.le_trans hle hle', hok'⟩

theorem fireState_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (owner : FiberId) (hm : MintedAt nk sk m) :
    m.world.le (fireState interp fuel m owner).1.world ∧ MintedAt nk sk (fireState interp fuel m owner).1 := by
  unfold fireState
  split
  · exact ⟨World.le_refl _, hm⟩
  · next o ho =>
    have hok : Ok m.world (o.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk ho) hm
    have hin : MintedIn ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner)
        (((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner).keys nk sk ++
          o.dispatcher.drain.1.flatMap (Task.keys nk sk)) := by
      simp only [MintedIn]
      rw [world_disarm, world_update]
      refine Ok_of_subset ?_ (Ok_append.mpr ⟨hm, hok⟩)
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · refine List.Subset.trans (keys_disarm_subset nk sk _) ?_
        refine List.Subset.trans (keys_update_subset nk sk _) ?_
        simp only [Dispatcher.drain]
        sub_tac
      · simp only [Dispatcher.drain, flatten_tasks_keys]
        simp only [RunFiber.keys, Dispatcher.keys]
        sub_tac
    obtain ⟨hle, hok'⟩ := fireTasks_minted_of_evaluator nk sk hb hEval fuel owner o.dispatcher.drain.1
      ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner, true) hin
    rw [world_disarm, world_update] at hle
    exact ⟨hle, hok'⟩

theorem flushAllState_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) :
    ∀ (rounds : Nat) (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores), MintedAt nk sk m →
      m.world.le (flushAllState interp fuel rounds m).1.world ∧ MintedAt nk sk (flushAllState interp fuel rounds m).1
  | 0, m, hm => ⟨World.le_refl _, hm⟩
  | rounds + 1, m, hm => by
    unfold flushAllState
    split
    · exact ⟨World.le_refl _, hm⟩
    · split
      · exact ⟨World.le_refl _, hm⟩
      · next owner _ _ _ =>
        try dsimp only
        obtain ⟨hle, hok⟩ := fireState_minted_of_evaluator nk sk hb hEval fuel m owner hm
        split
        · obtain ⟨hle', hok'⟩ := flushAllState_minted_of_evaluator hb hEval fuel rounds _ hok
          exact ⟨World.le_trans hle hle', hok'⟩
        · exact ⟨hle, hok⟩

theorem flushRootState_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) (root : FiberId) :
    ∀ (rounds : Nat) (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores), MintedAt nk sk m →
      m.world.le (flushRootState interp fuel root rounds m).1.world ∧
        MintedAt nk sk (flushRootState interp fuel root rounds m).1
  | 0, m, hm => by
    unfold flushRootState
    split <;> exact ⟨World.le_refl _, hm⟩
  | rounds + 1, m, hm => by
    unfold flushRootState
    split
    · exact ⟨World.le_refl _, hm⟩
    · split
      · exact ⟨World.le_refl _, hm⟩
      · try dsimp only
        obtain ⟨hle, hok⟩ := fireState_minted_of_evaluator nk sk hb hEval fuel m root hm
        split
        · obtain ⟨hle', hok'⟩ := flushRootState_minted_of_evaluator hb hEval fuel root rounds _ hok
          exact ⟨World.le_trans hle hle', hok'⟩
        · exact ⟨hle, hok⟩

/-- One decision keeps every handle, provided an external answer names handles that exist. -/
theorem stepDecisionState_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (decision : RunDecision ν σ Val Err Defect FiberId Ann)
    (hanswer : ∀ id token answer, decision = RunDecision.answerAsync id token answer →
      MintedIn m answer.keys)
    (hm : MintedAt nk sk m) :
    m.world.le (stepDecisionState interp fuel m decision).1.world ∧
      MintedAt nk sk (stepDecisionState interp fuel m decision).1 := by
  cases decision with
  | fire owner => exact fireState_minted_of_evaluator nk sk hb hEval fuel m owner hm
  | flush => exact flushAllState_minted_of_evaluator nk sk hb hEval fuel fuel m hm
  | evaluate id =>
    simp only [stepDecisionState, stepDecisionState.loop]
    obtain ⟨hle, hok⟩ := driveState_minted_of_evaluator nk sk hb hEval fuel m [Cmd.evaluate id, Cmd.drainDue]
      (Ok_of_subset (by sub_tac) hm)
    exact ⟨hle, Ok_of_subset (List.subset_append_left _ _) hok⟩
  | yieldVerdict id verdict =>
    simp only [stepDecisionState]
    refine ⟨by rw [world_modify]; exact World.le_refl _, ?_⟩
    simp only [MintedAt, MintedIn]
    rw [world_modify]
    refine Ok_of_subset (keys_modify_subset nk sk id _ [] fun g => by sub_tac) ?_
    exact Ok_of_subset (by sub_tac) hm
  | answerAsync id token answer =>
    simp only [stepDecisionState, stepDecisionState.loop]
    have ha : MintedIn m answer.keys := hanswer id token answer rfl
    have hcode : Ok m.world (primKeys nk sk (interp.answerCode answer)) := Ok_of_subset (hb.answerCode answer) ha
    obtain ⟨hle, hok⟩ := driveState_minted_of_evaluator nk sk hb hEval fuel m
      [Cmd.resume id token (interp.answerCode answer), Cmd.drainDue]
      (Ok_of_subset (by sub_tac) (Ok_append.mpr ⟨hm, hcode⟩))
    exact ⟨hle, Ok_of_subset (List.subset_append_left _ _) hok⟩
  | interruptFrom interruptor annotations target =>
    simp only [stepDecisionState, stepDecisionState.loop]
    split
    · exact ⟨World.le_refl _, hm⟩
    · next t ht =>
      try dsimp only
      have htk : Ok m.world (t.keys nk sk) := Ok_of_subset (fiber?_keys_subset nk sk ht) hm
      have hir := interruptRecord_keys_subset nk sk interp interruptor annotations t
      -- the machine with the record written back, under either trace
      have hM : ∀ M : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores,
          (M = (m.emit [RunEvent.interruptRecorded interruptor target]).emit [RunEvent.interruptDeferred target] ∨
            M = m.emit [RunEvent.interruptRecorded interruptor target]) →
          MintedAt nk sk (M.update (interruptRecord interp interruptor annotations t).1) ∧
            m.world.le (M.update (interruptRecord interp interruptor annotations t).1).world := by
        intro M hMdef
        have hMw : M.world = m.world := by rcases hMdef with rfl | rfl <;> rfl
        have hMk : M.keys nk sk = m.keys nk sk := by rcases hMdef with rfl | rfl <;> rfl
        refine ⟨?_, by rw [world_update, hMw]; exact World.le_refl _⟩
        simp only [MintedAt, MintedIn]
        rw [world_update, hMw]
        refine Ok_of_subset (keys_update_subset nk sk _) ?_
        rw [hMk]
        exact Ok_append.mpr ⟨hm, Ok_of_subset hir htk⟩
      generalize hMdef : (if (interruptRecord interp interruptor annotations t).1.frame.deferredInterrupt
          && (interruptRecord interp interruptor annotations t).1.running then
            (m.emit [RunEvent.interruptRecorded interruptor target]).emit [RunEvent.interruptDeferred target]
          else m.emit [RunEvent.interruptRecorded interruptor target]) = M
      have hMcases : M = (m.emit [RunEvent.interruptRecorded interruptor target]).emit
            [RunEvent.interruptDeferred target] ∨ M = m.emit [RunEvent.interruptRecorded interruptor target] := by
        rw [← hMdef]
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨hMok, hMle⟩ := hM M hMcases
      split
      · obtain ⟨hle, hok⟩ := driveState_minted_of_evaluator nk sk hb hEval fuel _ [Cmd.evaluate target, Cmd.drainDue]
          (Ok_of_subset (by sub_tac) hMok)
        exact ⟨World.le_trans hMle hle, Ok_of_subset (List.subset_append_left _ _) hok⟩
      · exact ⟨hMle, hMok⟩
  | installMiddleware =>
    simp only [stepDecisionState]
    exact ⟨⟨fun _ h => h, Stores.le_refl _⟩, hm⟩

/-! ## The tape premise and replay -/

/-- Every external answer on the tape, at the point replay answers it, names handles that
exist in the machine it is answered against. Computed exactly as `replayEval` walks: a stuck
machine and a fuel frontier stop the walk, so no answer past them is checked. -/
def answersValid (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) (fuel : Nat) :
    List (RunDecision ν σ Val Err Defect FiberId Ann) → RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores → Bool
  | [], _ => true
  | decision :: tape, m =>
    match m.stuck with
    | some _ => true
    | none =>
      (match decision with
        | RunDecision.answerAsync _ _ answer => decide (MintedIn m answer.keys)
        | _ => true) &&
      (let r := stepDecisionState interp fuel m decision
       if r.2 then answersValid interp fuel tape r.1 else true)

/-- The tape premise of `handles_minted`: the C15 `TapeAddressed` reading, as a decidable
check over the replay. -/
def AnswersValidAt (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) (fuel : Nat)
    (tape : List (RunDecision ν σ Val Err Defect FiberId Ann))
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  answersValid interp fuel tape m = true

instance (interp : RunInterp ν σ Val Err Defect FiberId Ann Ctx Stores) (fuel : Nat)
    (tape : List (RunDecision ν σ Val Err Defect FiberId Ann))
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : Decidable (AnswersValidAt interp fuel tape m) :=
  inferInstanceAs (Decidable (answersValid interp fuel tape m = true))

/-- Replay keeps every handle, over any tape whose external answers are valid. -/
theorem replayEval_minted_of_evaluator (hb : KeyBounded nk sk interp)
    (hEval : EvaluatorMinted nk sk interp) (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ Val Err Defect FiberId Ann))
      (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores),
      AnswersValidAt interp fuel tape m → MintedAt nk sk m →
      m.world.le (replayEval interp fuel tape m).machine.world ∧
        MintedAt nk sk (replayEval interp fuel tape m).machine
  | [], m, _, hm => by
    unfold replayEval
    (repeat' split) <;> exact ⟨World.le_refl _, hm⟩
  | decision :: tape, m, hv, hm => by
    unfold replayEval
    split
    · exact ⟨World.le_refl _, hm⟩
    · next hstuck =>
      try dsimp only
      unfold AnswersValidAt answersValid at hv
      rw [hstuck] at hv
      simp only [Bool.and_eq_true] at hv
      obtain ⟨hcheck, hrest⟩ := hv
      have hanswer : ∀ id token answer, decision = RunDecision.answerAsync id token answer →
          MintedIn m answer.keys := by
        intro id token answer hdec
        subst hdec
        simpa using hcheck
      obtain ⟨hle, hok⟩ := stepDecisionState_minted_of_evaluator nk sk hb hEval fuel m decision hanswer hm
      split
      · next hr =>
        rw [if_pos hr] at hrest
        obtain ⟨hle', hok'⟩ := replayEval_minted_of_evaluator hb hEval fuel tape _ hrest hok
        exact ⟨World.le_trans hle hle', hok'⟩
      · exact ⟨hle, hok⟩

end EvaluatorTransport

/-- The static frame evaluator is the empty-ambient instance of the evaluator premise. -/
theorem frameEvaluator_minted (hb : KeyBounded nk sk interp) :
    EvaluatorMinted nk sk interp :=
  evaluatePrim_minted nk sk hb

/-! The original public scheduler theorems specialize the one evaluator proof spine. -/

theorem iteration_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m (Handle.fiber f.id :: m.keys nk sk ++ f.keys nk sk)) :
    IterMinted nk sk m (iteration interp m f yielding) :=
  iteration_minted_of_evaluator nk sk (frameEvaluator_minted nk sk hb) m f yielding hm

theorem driveStep_loop_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (yielding : Bool)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.loop id yielding :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.loop id yielding) rest) :=
  driveStep_loop_minted_of_evaluator nk sk (frameEvaluator_minted nk sk hb) m id yielding rest hm

theorem driveStep_deliver_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (id : FiberId) (yielding : Bool)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (Cmd.deliver id yielding :: rest))) :
    StepMinted nk sk m (driveStep interp m (Cmd.deliver id yielding) rest) :=
  driveStep_deliver_minted_of_evaluator nk sk (frameEvaluator_minted nk sk hb) m id yielding rest hm

theorem driveStep_minted (hb : KeyBounded nk sk interp)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (cmd : Cmd ν σ Val Err Defect FiberId Ann)
    (rest : List (Cmd ν σ Val Err Defect FiberId Ann))
    (hm : MintedIn m (m.keys nk sk ++ cmdsKeys nk sk (cmd :: rest))) :
    m.world.le (driveStep interp m cmd rest).1.world ∧
      MintedIn (driveStep interp m cmd rest).1
        ((driveStep interp m cmd rest).1.keys nk sk ++ cmdsKeys nk sk (driveStep interp m cmd rest).2) :=
  driveStep_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) m cmd rest hm

theorem driveState_minted (hb : KeyBounded nk sk interp) (fuel : Nat) :
    ∀ (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (cmds : List (Cmd ν σ Val Err Defect FiberId Ann)),
      MintedIn m (m.keys nk sk ++ cmdsKeys nk sk cmds) →
      m.world.le (driveState interp fuel m cmds).1.world ∧
        MintedIn (driveState interp fuel m cmds).1
          ((driveState interp fuel m cmds).1.keys nk sk ++ cmdsKeys nk sk (driveState interp fuel m cmds).2) :=
  driveState_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel

theorem fireStep_minted (hb : KeyBounded nk sk interp) (fuel : Nat) (owner : FiberId)
    (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × Bool) (task : Task ν σ Val Err Defect FiberId Ann)
    (hm : MintedIn acc.1 (acc.1.keys nk sk ++ task.keys nk sk)) :
    acc.1.world.le (fireStep interp fuel owner acc task).1.world ∧
      MintedAt nk sk (fireStep interp fuel owner acc task).1 :=
  fireStep_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel owner acc task hm

theorem fireTasks_minted (hb : KeyBounded nk sk interp) (fuel : Nat) (owner : FiberId) :
    ∀ (tasks : List (Task ν σ Val Err Defect FiberId Ann))
      (acc : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores × Bool),
      MintedIn acc.1 (acc.1.keys nk sk ++ tasks.flatMap (Task.keys nk sk)) →
      acc.1.world.le (tasks.foldl (fireStep interp fuel owner) acc).1.world ∧
        MintedAt nk sk (tasks.foldl (fireStep interp fuel owner) acc).1 :=
  fireTasks_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel owner

theorem fireState_minted (hb : KeyBounded nk sk interp) (fuel : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (owner : FiberId) (hm : MintedAt nk sk m) :
    m.world.le (fireState interp fuel m owner).1.world ∧ MintedAt nk sk (fireState interp fuel m owner).1 :=
  fireState_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel m owner hm

theorem flushAllState_minted (hb : KeyBounded nk sk interp) (fuel : Nat) :
    ∀ (rounds : Nat) (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores), MintedAt nk sk m →
      m.world.le (flushAllState interp fuel rounds m).1.world ∧ MintedAt nk sk (flushAllState interp fuel rounds m).1 :=
  flushAllState_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel

theorem flushRootState_minted (hb : KeyBounded nk sk interp) (fuel : Nat) (root : FiberId) :
    ∀ (rounds : Nat) (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores), MintedAt nk sk m →
      m.world.le (flushRootState interp fuel root rounds m).1.world ∧
        MintedAt nk sk (flushRootState interp fuel root rounds m).1 :=
  flushRootState_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel root

theorem stepDecisionState_minted (hb : KeyBounded nk sk interp) (fuel : Nat)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) (decision : RunDecision ν σ Val Err Defect FiberId Ann)
    (hanswer : ∀ id token answer, decision = RunDecision.answerAsync id token answer →
      MintedIn m answer.keys)
    (hm : MintedAt nk sk m) :
    m.world.le (stepDecisionState interp fuel m decision).1.world ∧
      MintedAt nk sk (stepDecisionState interp fuel m decision).1 :=
  stepDecisionState_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel m decision hanswer hm

theorem replayEval_minted (hb : KeyBounded nk sk interp) (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ Val Err Defect FiberId Ann))
      (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores),
      AnswersValidAt interp fuel tape m → MintedAt nk sk m →
      m.world.le (replayEval interp fuel tape m).machine.world ∧
        MintedAt nk sk (replayEval interp fuel tape m).machine :=
  replayEval_minted_of_evaluator nk sk hb (frameEvaluator_minted nk sk hb) fuel

/-! ## The stores' interpreter is key-bounded

The stores' own alphabet (`Name`, `Thunk`): every program the stores build names only what the
name or the operation named, and every store step answers a value that exists in the store it
leaves. -/

section StoresInstance

/-- From here on, the membership search also unfolds the stores' own alphabets and the stores'
key traversals. These rules are tried before the general ones and expand to the `norm` form. -/
macro_rules
  | `(tactic| sub_tac) => `(tactic| sub_tac norm [programKeys, Name.keys, Thunk.keys, ActionName.keys,
      FinName.keys, ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys, DeferredStore.keys,
      DeferredCell.keys, ScopeStore.keys, ScopeEntry.keys])
  | `(tactic| sub_tac using $hs:term,*) => `(tactic| sub_tac using $hs,* norm [programKeys, Name.keys,
      Thunk.keys, ActionName.keys, FinName.keys, ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys,
      DeferredStore.keys, DeferredCell.keys, ScopeStore.keys, ScopeEntry.keys])

theorem programKeys_ofExit (e : ExitV) : programKeys (Prim.ofExit e) = exitKeys e :=
  primKeys_ofExit _ _ e

theorem programKeys_voidAllOf (reasons : List (Reason Err Defect FiberId Ann)) :
    programKeys (Prim.ofExit (voidAllOf reasons)) = [] := by
  cases reasons <;> rfl

theorem completionPrim_keys (c : Completion Val Err Defect FiberId Ann) :
    programKeys (completionPrim c) ⊆ c.keys := by
  cases c with
  | ofExit exit => rw [completionPrim, programKeys_ofExit]; exact List.Subset.refl _
  | ofRefGet cell => simp only [completionPrim]; sub_tac

theorem exitsVal_keys : ∀ exits : List ExitV, (exitsVal exits).keys = exits.flatMap exitKeys
  | [] => rfl
  | exit :: rest => by
    cases exit <;> simp only [exitsVal, reifyExitVal, Val.keys, List.flatMap_cons, exitKeys, exitsVal_keys rest]

theorem reifyExitVal_keys (e : ExitV) : (reifyExitVal e).keys = exitKeys e := by
  cases e <;> rfl

theorem finProgram_keys (fin : FinName) (exit : ExitV) :
    programKeys (finProgram fin exit) ⊆ fin.keys ++ exitKeys exit := by
  cases fin with
  | interruptFiber fiber skipSelf => cases skipSelf <;> simp only [finProgram] <;> sub_tac
  | closeChildScope scope => simp only [finProgram]; sub_tac
  | detachFromParent parent key => simp only [finProgram]; sub_tac
  | release label fails => cases fails <;> simp only [finProgram] <;> sub_tac
  | awaitNewChildren snapshot => simp only [finProgram]; sub_tac
  | parkThen slot => simp only [finProgram]; sub_tac

theorem raceEntrants_keys (race : RaceName) :
    ((raceEntrants race).map progOf).flatMap programKeys = [] := by
  cases race <;> rfl

theorem progOf_keys : ∀ n : ProgName, programKeys (progOf n) ⊆ n.keys
  | ProgName.value v => by simp only [progOf]; sub_tac
  | ProgName.failCause cause => by simp only [progOf]; sub_tac
  | ProgName.syncOp op => by simp only [progOf]; sub_tac
  | ProgName.yieldNow priority => by simp only [progOf]; sub_tac
  | ProgName.park slot => by simp only [progOf]; sub_tac
  | ProgName.awaitDeferred cell => by simp only [progOf]; sub_tac
  | ProgName.intoDeferred body cell => by simp only [progOf]; sub_tac
  | ProgName.intoBody body cell => by simp only [progOf]; sub_tac
  | ProgName.maskedPark slot => by simp only [progOf]; sub_tac
  | ProgName.awaitFibers targets => by simp only [progOf]; sub_tac
  | ProgName.finalizerOf fin exit => by simp only [progOf]; sub_tac using (finProgram_keys fin exit)
  | ProgName.interruptDeferred cell => by simp only [progOf]; sub_tac
  | ProgName.onExitOf body fin flag => by simp only [progOf]; sub_tac using (progOf_keys body)
  | ProgName.seqOf first second => by simp only [progOf]; sub_tac using (progOf_keys first)
  | ProgName.forkThen child options mode => by simp only [progOf]; sub_tac
  | ProgName.forkOnly child options => by simp only [progOf]; sub_tac
  | ProgName.forkInScope child options scope => by simp only [progOf]; sub_tac
  | ProgName.runInScope target scope => by simp only [progOf]; sub_tac
  | ProgName.forkScopedOf child options => by simp only [progOf]; sub_tac
  | ProgName.raceOf race => by simp only [progOf]; sub_tac
  | ProgName.closeScopeOf scope exit => by simp only [progOf]; sub_tac
  | ProgName.awaitAllNew body => by simp only [progOf]; sub_tac
  | ProgName.interruptFibers targets => by simp only [progOf]; sub_tac
  | ProgName.joinFiber target mode => by simp only [progOf]; sub_tac
  | ProgName.cancelRace race => by simp only [progOf]; sub_tac
  | ProgName.closeWalk strategy order exit => by cases strategy <;> simp only [progOf] <;> sub_tac

/-- The finalizer programs of a close order, at the closing exit (the parallel walk's step,
§20), name the order's handles and the exit's. -/
theorem finPrograms_keys (exit : ExitV) : ∀ order : List FinName,
    (order.map fun fin => finProgram fin exit).flatMap programKeys ⊆
      order.flatMap FinName.keys ++ exitKeys exit
  | [] => List.nil_subset _
  | fin :: rest => by
    have ih := finPrograms_keys exit rest
    simp only [List.map_cons, List.flatMap_cons]
    sub_tac using (finProgram_keys fin exit), ih

/-- The inline merge (§20) returns only the void value. -/
theorem closeDone_done {ν σ κ : Type} {reasons : List (Reason Err Defect FiberId Ann)} {r : Val}
    (h : (closeDone reasons : IterStep ν σ Val Err Defect FiberId Ann κ) = IterStep.done r) :
    r = Val.unit := by
  cases reasons with
  | nil => simp only [closeDone, IterStep.done.injEq] at h; exact h.symm
  | cons _ _ => simp only [closeDone] at h; cases h

/-- The inline merge (§20) never yields an effect. -/
theorem closeDone_not_resume {ν σ κ : Type} {reasons : List (Reason Err Defect FiberId Ann)} {next : κ} {n : ν}
    (h : (closeDone reasons : IterStep ν σ Val Err Defect FiberId Ann κ) = IterStep.resume next n) : False := by
  cases reasons with
  | nil => simp only [closeDone] at h; cases h
  | cons _ _ => simp only [closeDone] at h; cases h

theorem cancelProgram_keys (name : Name) : programKeys (cancelProgram name) ⊆ name.keys := by
  unfold cancelProgram
  split <;> sub_tac

/-- The settle program names only the accepted exit: its cleanup carries the race identity,
which is a lookup key (D6a). -/
theorem raceSettleProgram_keys (race : Nat) (cleanupNeeded : Bool) (exit : ExitV) :
    programKeys (raceSettleProgram race cleanupNeeded exit) ⊆ exitKeys exit := by
  unfold raceSettleProgram
  split
  · sub_tac
  · rw [programKeys_ofExit]
    exact List.Subset.refl _

theorem contAOf_keys (name : Name) (v : Val) : programKeys (contAOf name v) ⊆ name.keys ++ v.keys := by
  cases name with
  | restore exit => simp only [contAOf, programKeys_ofExit]; sub_tac
  | merge exit => simp only [contAOf, programKeys_ofExit]; sub_tac
  | seq next => simp only [contAOf]; sub_tac using (progOf_keys next)
  | joinOn mode => cases v <;> simp only [contAOf] <;> sub_tac
  | interruptWith cell => cases v <;> simp only [contAOf] <;> sub_tac
  | doneInto cell => cases v <;> simp only [contAOf] <;> sub_tac
  | constant value => simp only [contAOf]; sub_tac
  | exitOfValue => cases v <;> simp only [contAOf] <;> sub_tac
  | snapshotThen body => cases v <;> simp only [contAOf] <;> sub_tac using (progOf_keys body)
  | registerAwait cell => simp only [contAOf]; sub_tac
  | cancelAwait cell => simp only [contAOf]; sub_tac
  | externalRegister slot => simp only [contAOf]; sub_tac
  | abortController => simp only [contAOf]; sub_tac
  | cancelPark => simp only [contAOf]; sub_tac
  | cancelRace race => simp only [contAOf]; sub_tac
  | withWaiter base waiter token => simp only [contAOf]; sub_tac
  | reFail cause => simp only [contAOf]; sub_tac
  | finalizerName fin => simp only [contAOf]; sub_tac
  | closeSeq rest exit captured => simp only [contAOf]; sub_tac
  | closeParDone => simp only [contAOf]; sub_tac

theorem contEOf_keys (name : Name) (cause : CauseV) : programKeys (contEOf name cause) ⊆ name.keys := by
  cases name with
  | restore exit => simp only [contEOf, programKeys_ofExit]; sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | merge exit => simp only [contEOf, programKeys_ofExit]; sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | closeSeq rest exit captured => simp only [contEOf]; sub_tac
  | constant value => simp only [contEOf]; sub_tac
  | seq next => simp only [contEOf]; sub_tac
  | joinOn mode => simp only [contEOf]; sub_tac
  | interruptWith cell => simp only [contEOf]; sub_tac
  | doneInto cell => simp only [contEOf]; sub_tac
  | exitOfValue => simp only [contEOf]; sub_tac
  | snapshotThen body => simp only [contEOf]; sub_tac
  | registerAwait cell => simp only [contEOf]; sub_tac
  | cancelAwait cell => simp only [contEOf]; sub_tac
  | externalRegister slot => simp only [contEOf]; sub_tac
  | abortController => simp only [contEOf]; sub_tac
  | cancelPark => simp only [contEOf]; sub_tac
  | cancelRace race => simp only [contEOf]; sub_tac
  | withWaiter base waiter token => simp only [contEOf]; sub_tac
  | reFail cause' => simp only [contEOf]; sub_tac
  | finalizerName fin => simp only [contEOf]; sub_tac
  | closeParDone => simp only [contEOf]; sub_tac

theorem actionOf_keys (action : ActionName) :
    (actionOf action).keys Name.keys Thunk.keys ⊆ action.keys := by
  cases action with
  | fork program options => simp only [actionOf]; sub_tac using (progOf_keys program)
  | forkIn program options scope => simp only [actionOf]; sub_tac using (progOf_keys program)
  | forkScoped program options => simp only [actionOf]; sub_tac using (progOf_keys program)
  | interruptAs target who => simp only [actionOf]; sub_tac
  | raceAll race =>
    simp only [actionOf, WithFiberAction.keys, ActionName.keys]
    rw [show ((raceEntrants race).map progOf).flatMap (primKeys Name.keys Thunk.keys) = [] from
      raceEntrants_keys race]
    exact List.nil_subset _
  | setInterruptible body flag => simp only [actionOf]; sub_tac using (progOf_keys body)
  | runIn target scope => simp only [actionOf]; sub_tac
  | interrupt target => simp only [actionOf]; sub_tac
  | interruptScoped target => simp only [actionOf]; sub_tac
  | interruptAll targets interruptor => simp only [actionOf]; sub_tac
  | awaitAll targets => simp only [actionOf]; sub_tac
  | snapshotChildren => simp only [actionOf]; sub_tac
  | awaitNewChildren snapshot => simp only [actionOf]; sub_tac
  | setContext context => simp only [actionOf]; sub_tac
  | getContext => simp only [actionOf]; sub_tac
  | getId => simp only [actionOf]; sub_tac
  | closeScope scope exit => simp only [actionOf]; sub_tac
  | refuse cause => simp only [actionOf]; sub_tac
  | dropObservers token => simp only [actionOf]; sub_tac
  | cancelRace race => simp only [actionOf]; sub_tac
  | ambientScope => simp only [actionOf]; sub_tac
  | closePar order exit =>
    simp only [actionOf, WithFiberAction.keys, ActionName.keys]
    exact finPrograms_keys exit order

/-! ### The Deferred store -/

theorem DeferredStore.setCell_keys_subset (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell) :
    (self.setCell cell c).keys ⊆ self.keys ++ c.keys := by
  intro x hx
  simp only [DeferredStore.keys, DeferredStore.setCell, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · obtain ⟨c', hc', hxc⟩ := List.mem_flatMap.mp hx
    rcases List.mem_or_eq_of_mem_set hc' with h | rfl
    · exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨c', h, hxc⟩))
    · exact Or.inr hxc
  · exact Or.inl (Or.inr hx)

theorem DeferredStore.setCell_le (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell) :
    self.cells.length ≤ (self.setCell cell c).cells.length := by
  rw [DeferredStore.setCell_cells_length]
  exact Nat.le_refl _

theorem DeferredStore.register_keys (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    (self.register cell waiter token).1.keys ⊆ self.keys ∧
      (∀ p, (self.register cell waiter token).2 = some p → programKeys p ⊆ self.keys) ∧
      self.cells.length ≤ (self.register cell waiter token).1.cells.length := by
  unfold DeferredStore.register
  split
  · exact ⟨List.Subset.refl _, (fun p hp => nomatch (show (none : Option Program) = some p from hp)),Nat.le_refl _⟩
  · next c hc =>
    split
    · next effect heff =>
      refine ⟨List.Subset.refl _, fun p hp => ?_, Nat.le_refl _⟩
      simp only [Option.some.injEq] at hp
      subst hp
      have hcm : c ∈ self.cells := List.mem_of_getElem? hc
      have : c.keys ⊆ self.keys := by
        intro y hy
        simp only [DeferredStore.keys, List.mem_append]
        exact Or.inl (List.mem_flatMap.mpr ⟨c, hcm, hy⟩)
      refine List.Subset.trans ?_ this
      simp only [DeferredCell.keys, heff]
      exact List.Subset.refl _
    · refine ⟨?_, (fun p hp => nomatch (show (none : Option Program) = some p from hp)),DeferredStore.setCell_le _ _ _⟩
      refine List.Subset.trans (DeferredStore.setCell_keys_subset _ _ _) ?_
      have hcm : c ∈ self.cells := List.mem_of_getElem? hc
      refine List.append_subset.mpr ⟨List.Subset.refl _, ?_⟩
      intro y hy
      simp only [DeferredStore.keys, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr ⟨c, hcm, by simpa [DeferredCell.keys] using hy⟩)

theorem flatMap_resumes_const (ws : List (FiberId × Nat)) (e : Program) :
    (ws.map fun w => (w.1, w.2, e)).flatMap (fun r => programKeys r.2.2) ⊆ programKeys e := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hr
  exact hxr

theorem DeferredStore.complete_keys (self : DeferredStore) (cell : DeferredKey) (e : Program) :
    (self.complete cell e).1.keys ⊆ self.keys ++ programKeys e ∧
      self.cells.length ≤ (self.complete cell e).1.cells.length := by
  unfold DeferredStore.complete
  split
  · exact ⟨List.subset_append_left _ _, Nat.le_refl _⟩
  · next c hc =>
    split
    · exact ⟨List.subset_append_left _ _, Nat.le_refl _⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        simp only [DeferredStore.keys, List.mem_append] at hx
        rcases hx with hx | hx
        · have := DeferredStore.setCell_keys_subset self cell ⟨some e, []⟩
          simp only [DeferredStore.keys, DeferredCell.keys] at this
          have hx' := this (List.mem_append_left _ hx)
          simp only [List.mem_append] at hx' ⊢
          rcases hx' with (h | h) | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inl (List.mem_append_right _ h)
          · exact Or.inr h
        · simp only [List.flatMap_append, List.mem_append] at hx
          rcases hx with hx | hx
          · exact List.mem_append.mpr (Or.inl (List.mem_append_right _ hx))
          · exact List.mem_append.mpr (Or.inr (flatMap_resumes_const c.waiters e hx))
      · show self.cells.length ≤ (self.setCell cell ⟨some e, []⟩).cells.length
        exact DeferredStore.setCell_le _ _ _

theorem DeferredStore.cancel_keys (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    (self.cancel cell waiter token).keys ⊆ self.keys ∧
      self.cells.length ≤ (self.cancel cell waiter token).cells.length := by
  unfold DeferredStore.cancel
  split
  · exact ⟨List.Subset.refl _, Nat.le_refl _⟩
  · next c hc =>
    refine ⟨?_, DeferredStore.setCell_le _ _ _⟩
    refine List.Subset.trans (DeferredStore.setCell_keys_subset _ _ _) ?_
    have hcm : c ∈ self.cells := List.mem_of_getElem? hc
    refine List.append_subset.mpr ⟨List.Subset.refl _, ?_⟩
    intro y hy
    simp only [DeferredStore.keys, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨c, hcm, by simpa [DeferredCell.keys] using hy⟩)

theorem DeferredStore.drainDue_keys (self : DeferredStore) :
    (self.drainDue).2.keys ⊆ self.keys ∧
      ((self.drainDue).1.flatMap fun r => programKeys r.2.2) ⊆ self.keys := by
  simp only [DeferredStore.drainDue, DeferredStore.keys, List.flatMap_nil, List.append_nil]
  exact ⟨List.subset_append_left _ _, List.subset_append_right _ _⟩

/-! ### The scope store -/

theorem tableInsert_keys_subset (table : List (Nat × FinName)) (key : Nat) (fin : FinName) :
    ((Scope.tableInsert table key fin).flatMap fun kf => FinName.keys kf.2) ⊆
      (table.flatMap fun kf => FinName.keys kf.2) ++ fin.keys := by
  unfold Scope.tableInsert
  split
  · intro x hx
    obtain ⟨kf', hkf', hxk⟩ := List.mem_flatMap.mp hx
    obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp hkf'
    split at hxk
    · exact List.mem_append_right _ hxk
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨kf, hkf, hxk⟩)
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Subset.refl _

theorem Scope.isClosed_of_state_closed (sc : ScopeV) (exit : ExitV) (h : sc.state = ScopeState.closed exit) :
    sc.isClosed = true := by
  show sc.state.isClosed = true
  rw [h]
  rfl

theorem Scope.isOpen_false_of_not_open (sc : ScopeV)
    (h : sc.state = ScopeState.empty ∨ ∃ exit, sc.state = ScopeState.closed exit) :
    sc.isOpen = false := by
  show sc.state.isOpen = false
  rcases h with h | ⟨exit, h⟩ <;> rw [h] <;> rfl

/-- Removing from a scope that is open with nothing registered leaves it so. -/
theorem Scope.removeUnsafe_openEmpty (sc : ScopeV) (key : Nat) (h : sc.state = ScopeState.openEmpty) :
    (sc.removeUnsafe key).state = ScopeState.openEmpty := by
  unfold Scope.removeUnsafe
  simp only [h]
  rfl

theorem scopeAddUnsafe_keys (sc : ScopeV) (key : Nat) (fin : FinName) :
    ((sc.addUnsafe key fin).finalizers.flatMap fun kf => FinName.keys kf.2) ⊆
      (sc.finalizers.flatMap fun kf => FinName.keys kf.2) ++ fin.keys := by
  rcases hst : sc.state with _ | _ | ⟨k', f'⟩ | table | exit
  · rw [Scope.finalizers_eq, Scope.addUnsafe_empty sc key fin hst, ScopeState.entries_openInline]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.subset_append_right _ _
  · rw [Scope.finalizers_eq, Scope.addUnsafe_openEmpty sc key fin hst, ScopeState.entries_openInline]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.subset_append_right _ _
  · rw [Scope.finalizers_eq, Scope.addUnsafe_openInline sc k' key f' fin hst, ScopeState.entries_openMap,
      Scope.finalizers_eq, hst, ScopeState.entries_openInline]
    exact tableInsert_keys_subset _ _ _
  · rw [Scope.finalizers_eq, Scope.addUnsafe_openMap sc table key fin hst, ScopeState.entries_openMap,
      Scope.finalizers_eq, hst, ScopeState.entries_openMap]
    exact tableInsert_keys_subset _ _ _
  · rw [Scope.addUnsafe_closed sc key fin (Scope.isClosed_of_state_closed sc exit hst)]
    exact List.subset_append_left _ _

theorem scopeAddExit_keys (sc : ScopeV) (key : Nat) (fin : FinName) :
    ((Scope.addExit finExit sc key fin).1.finalizers.flatMap fun kf => FinName.keys kf.2) ⊆
      (sc.finalizers.flatMap fun kf => FinName.keys kf.2) ++ fin.keys := by
  unfold Scope.addExit
  split
  · exact List.subset_append_left _ _
  · exact scopeAddUnsafe_keys sc key fin

theorem scopeRemoveUnsafe_keys (sc : ScopeV) (key : Nat) :
    ((sc.removeUnsafe key).finalizers.flatMap fun kf => FinName.keys kf.2) ⊆
      sc.finalizers.flatMap fun kf => FinName.keys kf.2 := by
  rcases hst : sc.state with _ | _ | ⟨k', f'⟩ | table | exit
  · rw [Scope.removeUnsafe_not_open sc key (Scope.isOpen_false_of_not_open sc (Or.inl hst))]
    exact List.Subset.refl _
  · rw [Scope.finalizers_eq, Scope.removeUnsafe_openEmpty sc key hst, ScopeState.entries_openEmpty]
    exact List.nil_subset _
  · by_cases hk : k' = key
    · subst hk
      rw [Scope.finalizers_eq, Scope.removeUnsafe_inline_hit sc k' f' hst, ScopeState.entries_openEmpty]
      exact List.nil_subset _
    · rw [Scope.removeUnsafe_inline_miss sc k' key f' hst hk]
      exact List.Subset.refl _
  · rw [Scope.finalizers_eq, Scope.removeUnsafe_openMap sc table key hst, ScopeState.entries_openMap,
      Scope.tableRemove_eq, Scope.finalizers_eq, hst, ScopeState.entries_openMap]
    exact flatMap_filter_subset _ _ _
  · rw [Scope.removeUnsafe_not_open sc key (Scope.isOpen_false_of_not_open sc (Or.inr ⟨exit, hst⟩))]
    exact List.Subset.refl _

theorem ScopeStore.setEntry_keys_subset (self : ScopeStore) (e : ScopeEntry) :
    (self.setEntry e).keys ⊆ self.keys ++ e.keys := by
  intro x hx
  simp only [ScopeStore.keys, ScopeStore.setEntry] at hx
  obtain ⟨e', he', hxe⟩ := List.mem_flatMap.mp hx
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he'
  split at hxe
  · exact List.mem_append_right _ hxe
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e0, he0, hxe⟩)

theorem ScopeStore.entry_keys_subset {self : ScopeStore} {key : Nat} {e : ScopeEntry}
    (h : self.entryAt key = some e) : e.keys ⊆ self.keys :=
  fun _ hx => List.mem_flatMap.mpr ⟨e, List.mem_of_find?_eq_some h, hx⟩

theorem ScopeStore.make_keys (self : ScopeStore) (name : Nat) (strategy : FinalizerStrategy) :
    (self.make name strategy).keys ⊆ self.keys := by
  simp only [ScopeStore.keys, ScopeStore.make, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    ScopeEntry.keys, Scope.make_finalizers, List.append_nil]
  exact List.Subset.refl _

theorem ScopeStore.addFinalizer_keys (self : ScopeStore) (scope key : Nat) (fin : FinName) :
    (self.addFinalizer scope key fin).1.keys ⊆ self.keys ++ fin.keys := by
  unfold ScopeStore.addFinalizer
  split
  · exact List.subset_append_left _ _
  · next entry hentry =>
    try dsimp only
    refine List.Subset.trans (ScopeStore.setEntry_keys_subset _ _) ?_
    refine List.append_subset.mpr ⟨List.subset_append_left _ _, ?_⟩
    have := scopeAddExit_keys entry.scope key fin
    simp only [ScopeEntry.keys]
    refine List.Subset.trans this ?_
    refine List.append_subset.mpr ⟨?_, List.subset_append_right _ _⟩
    refine List.Subset.trans ?_ (List.subset_append_left _ _)
    exact ScopeStore.entry_keys_subset hentry

theorem ScopeStore.removeFinalizer_keys (self : ScopeStore) (scope key : Nat) :
    (self.removeFinalizer scope key).keys ⊆ self.keys := by
  unfold ScopeStore.removeFinalizer
  split
  · exact List.Subset.refl _
  · next entry hentry =>
    refine List.Subset.trans (ScopeStore.setEntry_keys_subset _ _) ?_
    refine List.append_subset.mpr ⟨List.Subset.refl _, ?_⟩
    simp only [ScopeEntry.keys]
    refine List.Subset.trans (scopeRemoveUnsafe_keys entry.scope key) ?_
    exact ScopeStore.entry_keys_subset hentry

theorem ScopeStore.closeState_keys (self : ScopeStore) (key : Nat) (exit : ExitV) :
    (self.closeState key exit).keys ⊆ self.keys := by
  unfold ScopeStore.closeState
  split
  · exact List.Subset.refl _
  · refine List.Subset.trans (ScopeStore.setEntry_keys_subset _ _) ?_
    simp only [ScopeEntry.keys, Scope.closeState_finalizers, List.flatMap_nil, List.append_nil]
    exact List.Subset.refl _

theorem ScopeStore.closeOrder_keys {self : ScopeStore} {key : Nat} {entry : ScopeEntry}
    (h : self.entryAt key = some entry) : entry.scope.closeOrder.flatMap FinName.keys ⊆ self.keys := by
  intro x hx
  obtain ⟨fin, hfin, hxf⟩ := List.mem_flatMap.mp hx
  rw [Scope.closeOrder_eq, List.mem_reverse] at hfin
  obtain ⟨kf, hkf, rfl⟩ := List.mem_map.mp hfin
  exact ScopeStore.entry_keys_subset h (List.mem_flatMap.mpr ⟨kf, hkf, hxf⟩)

theorem ScopeStore.entryAt_closeState_isSome (self : ScopeStore) (scope key : Nat) (exit : ExitV)
    (h : (self.entryAt key).isSome = true) : ((self.closeState scope exit).entryAt key).isSome = true := by
  unfold ScopeStore.closeState
  split
  · exact h
  · exact ScopeStore.entryAt_setEntry_isSome _ _ _ h

/-! ### The heap and the store step -/

theorem FnName.total_keys (f : FnName) (a : Val) : (f.total a).keys ⊆ a.keys := by
  cases f <;> cases a <;> simp only [FnName.total] <;> exact List.Subset.refl _

theorem FnName.partialUpdate_keys (f : FnName) (a a' : Val) (h : f.partialUpdate a = some a') :
    a'.keys ⊆ a.keys := by
  cases f <;> cases a <;> simp only [FnName.partialUpdate, FnName.total, Option.some.injEq] at h <;>
    first
      | (subst h; exact List.Subset.refl _)
      | (cases h)
      | (rename_i n; cases n <;> simp only [Option.some.injEq] at h <;> first | (subst h; exact List.Subset.refl _) | cases h)

theorem FnName.modify_keys (f : FnName) (a : Val) :
    (f.modify a).1.keys ⊆ a.keys ∧ (f.modify a).2.keys ⊆ a.keys := by
  cases f <;> cases a <;> simp only [FnName.modify, FnName.total] <;> exact ⟨List.Subset.refl _, List.Subset.refl _⟩

theorem FnName.modifySome_keys (f : FnName) (a : Val) :
    (f.modifySome a).1.keys ⊆ a.keys ∧ ((f.modifySome a).2.getD a).keys ⊆ a.keys := by
  cases f <;> cases a <;> simp only [FnName.modifySome, FnName.modify, FnName.total, Option.getD] <;>
    exact ⟨List.Subset.refl _, List.Subset.refl _⟩

theorem refPoke_keys (heap : RefHeap) (cell : RefKey) (y : Val) :
    (refPoke heap cell y).flatMap Val.keys ⊆ heap.flatMap Val.keys ++ y.keys := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
  rcases List.mem_or_eq_of_mem_set ha with h | rfl
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨a, h, hxa⟩)
  · exact List.mem_append_right _ hxa

theorem mem_heap_keys {heap : RefHeap} {a : Val} (h : a ∈ heap) : a.keys ⊆ heap.flatMap Val.keys :=
  fun _ hx => List.mem_flatMap.mpr ⟨a, h, hx⟩

/-- One heap step answers and writes only values built from the operation's argument and the
values already in the heap; the fresh cell of `refMake` exists in the heap it leaves. -/
theorem refStep_keys (o : SyncOp) (s : Stores) (v : Val) (heap' : RefHeap) (ids : List FiberId)
    (h : refStep o s.refs = some (v, heap')) (hok : Ok ⟨ids, s⟩ (o.keys ++ s.keys)) :
    Ok ⟨ids, { s with refs := heap' }⟩ (v.keys ++ heap'.flatMap Val.keys) := by
  have hle : s.le { s with refs := heap' } :=
    ⟨refStep_length o s.refs v heap' h, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _⟩
  have hmono : World.le ⟨ids, s⟩ ⟨ids, { s with refs := heap' }⟩ := ⟨fun _ hh => hh, hle⟩
  have hok' := Ok_mono hmono hok
  cases o with
  | refMake initial =>
    simp only [refStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_append.mpr ⟨?_, ?_⟩
    · refine Ok_cons.mpr ⟨?_, Ok_nil _⟩
      simp [Handle.existsIn]
    · refine Ok_of_subset ?_ hok'
      sub_tac
  | refGet cell =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
  | refSet cell value =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell value)
  | refGetAndSet cell value =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell value), (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
  | refSetAndGet cell value =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell value)
  | refUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell (f.total a)),
      (List.Subset.trans (FnName.total_keys f a) (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
  | refGetAndUpdate cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell (f.total a)),
      (List.Subset.trans (FnName.total_keys f a) (mem_heap_keys (mem_of_refPeek_eq_some hpeek))),
      (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
  | refUpdateAndGet cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell (f.total a)),
      (List.Subset.trans (FnName.total_keys f a) (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
  | refUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    split
    · next a' ha' =>
      sub_tac using (refPoke_keys s.refs cell a'),
        (List.Subset.trans (FnName.partialUpdate_keys pf a a' ha') (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
    · sub_tac
  | refGetAndUpdateSome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    split
    · next a' ha' =>
      sub_tac using (refPoke_keys s.refs cell a'),
        (List.Subset.trans (FnName.partialUpdate_keys pf a a' ha') (mem_heap_keys (mem_of_refPeek_eq_some hpeek))),
        (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
    · sub_tac using (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
  | refUpdateSomeAndGet cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.bind_eq_some_iff.mp h
    split at hf
    · next a' ha' =>
      obtain ⟨fresh, hfresh, hff⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hff
      obtain ⟨rfl, rfl⟩ := hff
      have hfm : fresh ∈ refPoke s.refs cell a' := mem_of_refPeek_eq_some hfresh
      have hfk : fresh.keys ⊆ s.refs.flatMap Val.keys ++ a'.keys :=
        List.Subset.trans (mem_heap_keys hfm) (refPoke_keys s.refs cell a')
      refine Ok_of_subset ?_ hok'
      sub_tac using hfk, (refPoke_keys s.refs cell a'),
        (List.Subset.trans (FnName.partialUpdate_keys pf a a' ha') (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      refine Ok_of_subset ?_ hok'
      sub_tac using (mem_heap_keys (mem_of_refPeek_eq_some hpeek))
  | refModify cell f =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell (f.modify a).2),
      (List.Subset.trans (FnName.modify_keys f a).1 (mem_heap_keys (mem_of_refPeek_eq_some hpeek))),
      (List.Subset.trans (FnName.modify_keys f a).2 (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
  | refModifySome cell pf =>
    simp only [refStep] at h
    obtain ⟨a, hpeek, hf⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine Ok_of_subset ?_ hok'
    sub_tac using (refPoke_keys s.refs cell ((pf.modifySome a).2.getD a)),
      (List.Subset.trans (FnName.modifySome_keys pf a).1 (mem_heap_keys (mem_of_refPeek_eq_some hpeek))),
      (List.Subset.trans (FnName.modifySome_keys pf a).2 (mem_heap_keys (mem_of_refPeek_eq_some hpeek)))
  | _ => simp [refStep] at h

/-- A store step from a store whose handles exist answers a value whose handles exist, and
leaves a store whose handles exist. -/
theorem syncOpStep_keys (o : SyncOp) (s s' : Stores) (v : Val) (ids : List FiberId)
    (h : syncOpStep o s = some (s', v)) (hok : Ok ⟨ids, s⟩ (o.keys ++ s.keys)) :
    Ok ⟨ids, s'⟩ (v.keys ++ s'.keys) := by
  have hle := syncOpStep_le o s s' v h
  have hmono : World.le ⟨ids, s⟩ ⟨ids, s'⟩ := ⟨fun _ hh => hh, hle⟩
  have hok' := Ok_mono hmono hok
  cases o with
  | deferredMake =>
    simp only [syncOpStep_deferredMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_append.mpr ⟨Ok_cons.mpr ⟨?_, Ok_nil _⟩, ?_⟩
    · simp [Handle.existsIn, DeferredStore.make]
    · refine Ok_of_subset ?_ hok'
      simp only [DeferredStore.make]
      sub_tac
  | deferredIsDone cell | deferredPoll cell | scopeIsClosed cell =>
    simp only [syncOpStep_deferredIsDone, syncOpStep_deferredPoll, syncOpStep_scopeIsClosed] at h
    obtain ⟨_, _, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    refine Ok_of_subset ?_ hok'
    sub_tac
  | deferredCompleteWith cell completion =>
    simp only [syncOpStep_deferredCompleteWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_of_subset ?_ hok'
    have hcompletion : (s.deferreds.complete cell (completionPrim completion)).1.keys ⊆
        s.deferreds.keys ++ completion.keys :=
      List.Subset.trans (DeferredStore.complete_keys s.deferreds cell (completionPrim completion)).1
        (List.append_subset.mpr ⟨List.subset_append_left _ _,
          List.Subset.trans (completionPrim_keys completion) (List.subset_append_right _ _)⟩)
    sub_tac using hcompletion norm [SyncOp.keys]
  | deferredInterruptWith cell interruptor =>
    simp only [syncOpStep_deferredInterruptWith, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_of_subset ?_ hok'
    have hc := (DeferredStore.complete_keys s.deferreds cell
      (Prim.ofExit (Exit.failure (Cause.interrupt (some interruptor))))).1
    rw [programKeys_ofExit] at hc
    simp only [exitKeys, List.append_nil] at hc
    sub_tac using hc
  | deferredAwaitCleanup cell waiter token =>
    simp only [syncOpStep_deferredAwaitCleanup, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_of_subset ?_ hok'
    sub_tac using (DeferredStore.cancel_keys s.deferreds cell waiter token).1
  | scopeMake strategy =>
    simp only [syncOpStep_scopeMake, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_append.mpr ⟨Ok_cons.mpr ⟨?_, Ok_nil _⟩, ?_⟩
    · exact ScopeStore.entryAt_make_self s.scopes s.nextName strategy
    · refine Ok_of_subset ?_ hok'
      sub_tac using (ScopeStore.make_keys s.scopes s.nextName strategy)
  | scopeAdd scope key finalizer =>
    simp only [syncOpStep_scopeAdd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_of_subset ?_ hok'
    sub_tac using (ScopeStore.addFinalizer_keys s.scopes scope key finalizer)
  | scopeRemove scope key =>
    simp only [syncOpStep_scopeRemove, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Ok_of_subset ?_ hok'
    sub_tac using (ScopeStore.removeFinalizer_keys s.scopes scope key)
  | _ =>
    simp only [syncOpStep] at h
    obtain ⟨⟨a, heap'⟩, hstep, hf⟩ := Option.map_eq_some_iff.mp h
    cases hf
    have hstepk := refStep_keys _ s a heap' ids hstep hok
    have hsk : Ok ⟨ids, { s with refs := heap' }⟩ s.keys := Ok_of_subset (List.subset_append_right _ _) hok'
    refine Ok_of_subset ?_ (Ok_append.mpr ⟨hstepk, hsk⟩)
    sub_tac

/-! ### The stores' interpreter -/

/-- The unsafe close's snapshot grows the store, keeps its handles, and captures only
finalizers the store held. -/
theorem scopeCloseSnapshot_keys (scope : Nat) (exit : ExitV) (s s' : Stores)
    (strategy : FinalizerStrategy) (order : List FinName)
    (h : scopeCloseSnapshot scope exit s = some (s', strategy, order)) :
    s.le s' ∧ s'.keys ⊆ s.keys ∧ order.flatMap FinName.keys ⊆ s.keys := by
  unfold scopeCloseSnapshot at h
  obtain ⟨entry, hentry, h⟩ := Option.bind_eq_some_iff.mp h
  change some _ = some (s', strategy, order) at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨⟨Nat.le_refl _, Nat.le_refl _,
    fun key hk => ScopeStore.entryAt_closeState_isSome _ _ _ _ hk, Nat.le_refl _⟩, ?_, ?_⟩
  · sub_tac using (ScopeStore.closeState_keys s.scopes scope exit)
  · exact List.Subset.trans (ScopeStore.closeOrder_keys hentry) (by sub_tac)

/-- Unsafe close's optional code — a single finalizer or the generator walk (§20) — retains
only its exit and the captured scope finalizers. -/
theorem storesCloseScopeUnsafe_keys (scope : Nat) (exit : ExitV) (flag : Bool)
    (s s' : Stores) (program : Option Program)
    (h : storesCloseScopeUnsafe scope exit flag s = some (s', program)) :
    s.le s' ∧ program.toList.flatMap programKeys ++ s'.keys ⊆ exitKeys exit ++ s.keys := by
  unfold storesCloseScopeUnsafe at h
  obtain ⟨⟨state, strategy, order⟩, hsnapshot, h⟩ := Option.bind_eq_some_iff.mp h
  change some _ = some (s', program) at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hle, hstate, horder⟩ := scopeCloseSnapshot_keys scope exit s state strategy order hsnapshot
  refine ⟨hle, List.append_subset.mpr ⟨?_,
    List.Subset.trans hstate (List.subset_append_right _ _)⟩⟩
  refine List.Subset.trans ?_ (List.append_subset.mpr
    ⟨List.Subset.trans horder (List.subset_append_right _ _), List.subset_append_left _ _⟩)
  cases order with
  | nil => exact List.nil_subset _
  | cons fin rest =>
    cases rest with
    | nil =>
      simpa only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using finProgram_keys fin exit
    | cons next rest =>
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        programKeys, primKeys, Thunk.keys, ProgName.keys]
      exact List.Subset.refl _

theorem stores_keyBounded : KeyBounded Name.keys Thunk.keys stores where
  contA n v := contAOf_keys n v
  contE n c := contEOf_keys n c
  syncValue t := by simp only [stores]; exact List.nil_subset _
  suspendBody t := by
    cases t with
    | body program => simp only [stores]; sub_tac using (progOf_keys program)
    | park kind => simp only [stores]; sub_tac
    | act action => simp only [stores]; sub_tac
    | op operation => simp only [stores]; sub_tac
  reifyExit e := by simp only [stores, reifyExitVal_keys]; exact List.Subset.refl _
  iterNext_done n v r h := by
    cases n with
    | closeSeq remaining exit captured =>
      cases remaining with
      | nil =>
        simp only [stores, closeSeqStep] at h
        rw [closeDone_done h]
        exact List.nil_subset _
      | cons fin rest => simp only [stores, closeSeqStep] at h; cases h
    | closeParDone =>
      simp only [stores] at h
      rw [closeDone_done h]
      exact List.nil_subset _
    | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
    | snapshotThen _ | registerAwait _ | cancelAwait _ | externalRegister _ | abortController | cancelPark
    | cancelRace _ | withWaiter _ _ _ | reFail _ | finalizerName _ =>
      simp only [stores, IterStep.done.injEq] at h
      subst h
      exact List.subset_append_right _ _
  iterNext_resume n v next n' h := by
    cases n with
    | closeSeq remaining exit captured =>
      cases remaining with
      | nil => simp only [stores, closeSeqStep] at h; exact (closeDone_not_resume h).elim
      | cons fin rest =>
        simp only [stores, closeSeqStep, IterStep.resume.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [primKeys, Name.keys, List.flatMap_cons]
        sub_tac using (finProgram_keys fin exit)
    | closeParDone => simp only [stores] at h; exact (closeDone_not_resume h).elim
    | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
    | snapshotThen _ | registerAwait _ | cancelAwait _ | externalRegister _ | abortController | cancelPark
    | cancelRace _ | withWaiter _ _ _ | reFail _ | finalizerName _ =>
      simp only [stores] at h; cases h
  loopBody n c := by simp only [stores]; sub_tac
  loopStep n c v := by simp only [stores]; sub_tac
  loopDone n := by simp only [stores]; exact List.nil_subset _
  cancelThenFail n c := by simp only [stores]; sub_tac using (cancelProgram_keys n)
  parkOf code target mode h := by
    simp only [stores] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      mem_tac [Thunk.keys, ParkKind.keys]
    · cases h
  parkCode kind := by simp only [stores]; sub_tac
  parkOfAwaitAll code targets h := by
    simp only [stores] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      sub_tac
    · cases h
  interruptCode target := by simp only [stores]; sub_tac
  interruptAsCode target who := by simp only [stores]; sub_tac
  interruptAllCode targets := by simp only [stores]; sub_tac
  withFiberOf t a h := by
    cases t with
    | act action =>
      simp only [stores, Option.some.injEq] at h
      subst h
      exact actionOf_keys action
    | park _ | op _ | body _ => simp only [stores] at h; cases h
  syncState t s s' v ids h hok := by
    cases t with
    | op operation =>
      simp only [stores] at h
      exact ⟨syncOpStep_le operation s s' v h, syncOpStep_keys operation s s' v ids h hok⟩
    | park _ | act _ | body _ => simp only [stores] at h; cases h
  registerAsync n fiber token s ids hok := by
    cases n with
    | registerAwait cell =>
      simp only [stores]
      obtain ⟨hkeys, himm, hlen⟩ := DeferredStore.register_keys s.deferreds cell fiber token
      have hle : s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } :=
        ⟨Nat.le_refl _, hlen, fun _ hh => hh, Nat.le_refl _⟩
      refine ⟨hle, ?_⟩
      have hok' := Ok_mono (World.le_of_state hle) hok
      refine Ok_of_subset ?_ hok'
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · sub_tac using hkeys
      · cases himm' : (s.deferreds.register cell fiber token).2 with
        | none => exact List.nil_subset _
        | some p =>
          show programKeys p ⊆ _
          refine List.Subset.trans (himm p himm') ?_
          sub_tac
    | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
    | snapshotThen _ | cancelAwait _ | externalRegister _ | abortController | cancelPark | cancelRace _
    | withWaiter _ _ _ | reFail _ | finalizerName _ | closeSeq _ _ _ | closeParDone =>
      simp only [stores]
      exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
  answerCode c := completionPrim_keys c
  dueResumes s ids hok := by
    simp only [stores]
    obtain ⟨h1, h2⟩ := DeferredStore.drainDue_keys s.deferreds
    have hle : s.le { s with deferreds := (s.deferreds.drainDue).2 } := by
      refine ⟨Nat.le_refl _, ?_, fun _ hh => hh, Nat.le_refl _⟩
      simp only [DeferredStore.drainDue]
      exact Nat.le_refl _
    refine ⟨hle, ?_⟩
    have hok' := Ok_mono (World.le_of_state hle) hok
    refine Ok_of_subset ?_ hok'
    sub_tac using h1, h2
  cancelName base fiber token := by simp only [stores]; sub_tac
  abortName := rfl
  parkCancelName := rfl
  raceCancelName race := rfl
  raceSettle race cleanupNeeded exit := by
    simp only [stores]; exact raceSettleProgram_keys race cleanupNeeded exit
  finalizerProgram n e p h := by
    cases n with
    | finalizerName fin =>
      simp only [stores, Option.some.injEq] at h
      subst h
      exact finProgram_keys fin e
    | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
    | snapshotThen _ | registerAwait _ | cancelAwait _ | externalRegister _ | abortController | cancelPark
    | cancelRace _ | withWaiter _ _ _ | reFail _ | closeSeq _ _ _ | closeParDone =>
      simp only [stores] at h; cases h
  restoreName e := by simp only [stores]; sub_tac
  mergeName e := by simp only [stores]; sub_tac
  scopeStatus scope s h := by
    simp only [stores, ScopeStore.status, Option.isSome_map] at h
    exact h
  scopeLinkFiber mode scope fiber s s' key ids h hok := by
    simp only [stores] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, hkey⟩ := h
      subst hkey
      -- the registration allocates from the supply, so `nextName` only grows
      have hle : s.le s' := by
        rw [← hs]
        exact ⟨Nat.le_refl _, Nat.le_refl _,
          fun k hk => ScopeStore.entryAt_addFinalizer_isSome _ _ _ _ k hk, Nat.le_succ _⟩
      refine ⟨hle, ?_⟩
      have hok' := Ok_mono (World.le_of_state hle) hok
      refine Ok_of_subset ?_ hok'
      rw [← hs]
      sub_tac using (ScopeStore.addFinalizer_keys s.scopes scope s.nextName _)
  dropFinalizer scope key s s' ids h hok := by
    simp only [stores] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      have hle : s.le { s with scopes := s.scopes.removeFinalizer scope key } :=
        ⟨Nat.le_refl _, Nat.le_refl _, fun k hk => ScopeStore.entryAt_removeFinalizer_isSome _ _ _ k hk,
          Nat.le_refl _⟩
      refine ⟨hle, ?_⟩
      have hok' := Ok_mono (World.le_of_state hle) hok
      refine Ok_of_subset ?_ hok'
      sub_tac using (ScopeStore.removeFinalizer_keys s.scopes scope key)
  closeScope scope exit flag closer s s' p ids h hok := by
    simp only [stores, storesCloseScope] at h
    obtain ⟨r, hr, hrp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    obtain ⟨hle, hkeys⟩ := storesCloseScopeUnsafe_keys scope exit flag s r.1 r.2 hr
    refine ⟨hle, ?_⟩
    have hok' := Ok_mono (World.le_of_state hle) hok
    refine Ok_of_subset ?_ hok'
    cases hp : r.2 with
    | none =>
      rw [hp] at hkeys
      simp only [Option.toList_none, List.flatMap_nil, List.nil_append] at hkeys
      simp only [Option.getD_none]
      exact List.Subset.trans (List.append_subset.mpr ⟨List.nil_subset _, hkeys⟩)
        (List.subset_cons_of_subset _ (List.Subset.refl _))
    | some q =>
      rw [hp] at hkeys
      simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hkeys
      simp only [Option.getD_some]
      exact List.Subset.trans hkeys (List.subset_cons_of_subset _ (List.Subset.refl _))
  emptyContext := rfl
  contextValue ctx := by simp only [stores]; exact List.Subset.refl _
  exitValue e mode := by
    cases mode with
    | awaitValue => simp only [stores, primKeys, reifyExitVal_keys]; exact List.Subset.refl _
    | joinEffect => simp only [stores, primKeys_ofExit]; exact List.Subset.refl _
  fiberValue id := by simp only [stores]; exact List.Subset.refl _
  fiberIdValue _ := List.nil_subset _
  fibersValue ids := by simp only [stores]; exact List.Subset.refl _
  exitsValue exits := by simp only [stores, exitsVal_keys]; exact List.Subset.refl _
  voidValue := rfl
  scopeValue scope := by simp only [stores]; exact List.Subset.refl _
  closeDoneName := rfl
  ambientScope ctx scope h := by
    simp only [stores] at h
    simp only [Ctx.keys, h, List.mem_singleton]

end StoresInstance

end Effect4.Machine
