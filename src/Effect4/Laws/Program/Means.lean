import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Machine.Book
import Effect4.Api

/-!
# The frame/term relation (P3, step 2): code, saved slots, fibers

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The frame
machine runs compiled `Prim` code over a stack of primitives; the term machine runs
`RProgram`s over a stack of `ScopeFrame` slots. This module says when the two carry the
same work:

* `CodeMeans root c r` relates the frame's current primitive with the term's current
  program *as both will be evaluated next*. The term's continuations are functions, so
  the relation quantifies over their applications; a continuation that will be resolved
  against a completed-exit view is related for every view (`prepareR completed` on the
  term side, the name refresh of `interpAt` on the frame side).
* A guard's normal branch runs the body into the closing marker whose delivery pops the
  guard's slot: the term's current is `body'.bind (unguardTail K)` while the frame's is
  `body` with the frame on the stack. `Delivers k` is the shape of a continuation that
  only hands its exit on (the term's `answer` slots and the tails of guards).
* `SlotMeans root f s` relates one frame on the stack with one term slot, and
  `StackMeans` the two stacks, allowing the term's transparent `answer` slots and the
  finalizer mask it records where the frame pushed a restoring mask or nothing.
* `Means root f₁ f₂` is the saved-state relation `S` of the book: the three control bits
  equal, the currents in `CodeMeans`, the stacks in `StackMeans`.

Nothing here runs a machine; `Simulation.lean` discharges the step obligation against it.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The frame machine's fiber at the native alphabet. -/
abbrev FFiber := FrameFiber EffName EffThunk Val Err Defect FiberId Ann

/-- A continuation that only delivers the exit it is given: a bare exit, or the closing
marker of a guard whose own continuation is dead (delivery walks the saved slots). -/
def Delivers (k : ExitV → RProgram) : Prop :=
  ∀ ex, k ex = .pure ex ∨ ∃ k', k ex = .vis (.inr (.unguard ex)) k'

/-- The tail a guard's normal branch runs into: the closing marker, whose delivery pops
the guard's slot; its continuation is `K` only by the bind laws, never run. -/
def unguardTail (K : ExitV → RProgram) : ExitV → RProgram :=
  fun ex => .vis (.inr (.unguard ex)) K

theorem delivers_unguardTail (K : ExitV → RProgram) : Delivers (unguardTail K) :=
  fun _ => Or.inr ⟨K, rfl⟩

theorem delivers_pure : Delivers Effects.Program.pure := fun _ => Or.inl rfl

/-- `interpAt`'s refresh of the value-continuation names against a completed view. -/
def _root_.Effect4.Program.EffName.refreshA (completed : List (FiberId × ExitV)) : EffName → EffName
  | .cont p => .cont { p with completed }
  | .onValue p => .onValue { p with completed }
  | .releaseBody p exit previous => .releaseBody { p with completed } exit previous
  | name => name

/-- `interpAt`'s refresh of the cause-continuation names against a completed view. -/
def _root_.Effect4.Program.EffName.refreshE (completed : List (FiberId × ExitV)) : EffName → EffName
  | .caught p => .caught { p with completed }
  | .caughtError p => .caughtError { p with completed }
  | .onCause p => .onCause { p with completed }
  | name => name

theorem interpAt_contA (root : NativeEff) (completed : List (FiberId × ExitV)) (n : EffName) (v : Val) :
    (interpAt root completed).contA n v = contAOf root (n.refreshA completed) v := by
  cases n <;> rfl

theorem interpAt_contE (root : NativeEff) (completed : List (FiberId × ExitV)) (n : EffName)
    (c : CauseV) :
    (interpAt root completed).contE n c = contEOf root (n.refreshE completed) c := by
  cases n <;> rfl

/-- The frame's finalizer code for an `OnExit` frame whose finalizer is a program, at the
refreshed interpreter (`Machine.finalizerCode` reads only the two exit names). -/
abbrev finalizerCodeAt (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    (program : NCode) : NCode :=
  finalizerCode (interpAt root completed) ex program

/-- The frame's current primitive and the term's current program carry the same work. The
`withFiber` clauses pair a frame action with the term's fiber operation: value-answering
operations that resume their continuation directly carry it related on every value;
operations whose answer arrives as code save the continuation as an answer slot, which
only delivers. -/
inductive CodeMeans (root : NativeEff) : NCode → RProgram → Prop
  -- exits: a bare exit, or the closing marker of a guard
  | success (v : Val) : CodeMeans root (Prim.success v) (.pure (.success v))
  | successUnguard (v : Val) (k : ExitV → RProgram) :
      CodeMeans root (Prim.success v) (.vis (.inr (.unguard (.success v))) k)
  | failure (c : CauseV) : CodeMeans root (Prim.failure c) (.pure (.failure c))
  | failureUnguard (c : CauseV) (k : ExitV → RProgram) :
      CodeMeans root (Prim.failure c) (.vis (.inr (.unguard (.failure c))) k)
  /-- `Prim.ofExit ex` after a finalizer's restoring continuation: the term's
  `finishFinalizer` marker pops the finalizer mask it recorded and delivers `ex`. -/
  | finishSuccess (v : Val) (k : ExitV → RProgram) :
      CodeMeans root (Prim.success v) (.vis (.inr (.finishFinalizer (.success v))) k)
  | finishFailure (c : CauseV) (k : ExitV → RProgram) :
      CodeMeans root (Prim.failure c) (.vis (.inr (.finishFinalizer (.failure c))) k)
  -- store operations and pure thunks
  | syncOp (o : SyncOp) (k : Val → RProgram) (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.sync (EffThunk.op o)) (.vis (.inl o) k)
  | syncStore (o : SyncOp) (k : Val → RProgram) (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.sync (EffThunk.store (Thunk.op o))) (.vis (.inl o) k)
  | syncPure (p : Point) (k : Val → RProgram)
      (hk : CodeMeans root (Prim.success (syncValueAt root (.pure p))) (k (syncValueAt root (.pure p)))) :
      CodeMeans root (Prim.sync (EffThunk.pure p)) (.vis (.inr (.sync (syncValueAt root (.pure p)))) k)
  -- suspensions: the counted checkpoint that returns code
  | suspendBody (p : Point) (k : Val → RProgram)
      (hk : ∀ completed, CodeMeans root (suspendBodyAt root (.body { p with completed }))
        (prepareR completed (k .unit))) :
      CodeMeans root (Prim.suspend (EffThunk.body p)) (.vis (.inr (.suspend p)) k)
  /-- `getOrElseMemoize`'s suspend (`Layer.ts:445`, the join): the frame's memo-lookup thunk
  at the layer's point, the term's counted step there. -/
  | suspendMemo (q : Point) (m : MemoMapId) (scope : Nat) (k : Val → RProgram)
      (hk : ∀ completed, CodeMeans root (suspendBodyAt root (.memoLookup q m scope))
        (prepareR completed (k .unit))) :
      CodeMeans root (Prim.suspend (EffThunk.memoLookup q m scope)) (.vis (.inr (.suspend q)) k)
  /-- A live frontier: the frame's suspension returns itself at every view, the term's
  frontier operation stays. The two points agree on everything but the captured view. -/
  | frontier (p p' : Point) (reason : FrontierReason) (k : ExitV → RProgram)
      (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
      (hloop : ∀ completed, suspendBodyAt root (.body { p' with completed }) =
        Prim.suspend (EffThunk.body { p' with completed })) :
      CodeMeans root (Prim.suspend (EffThunk.body p')) (.vis (.inr (.frontier reason p)) k)
  | yieldError (p : Point) (e : Err) (k : Val → RProgram)
      (hk : ∀ completed, CodeMeans root (Prim.failure (Cause.fail e)) (prepareR completed (k .unit))) :
      CodeMeans root (Prim.yieldableError e) (.vis (.inr (.suspend p)) k)
  /-- A stores program under `suspend`, spelled by its `ProgName`: the multiple-finalizer
  close (§20) is the one the term names. -/
  | closeWalk (strategy : FinalizerStrategy) (order : List FinName) (ex : ExitV) (k : Val → RProgram)
      (hk : ∀ completed, CodeMeans root (embed (progOf (ProgName.closeWalk strategy order ex)))
        (prepareR completed (k .unit))) :
      CodeMeans root (Prim.suspend (EffThunk.store (Thunk.body (ProgName.closeWalk strategy order ex))))
        (.vis (.inr (.closeWalk strategy order ex)) k)
  /-- A capture's release under `suspend` (V1): the frame's `Thunk.foreign`, the term's
  `foreignRelease` operation — both counted, both continuing with the release. -/
  | foreignRelease (c : Capture) (ex : ExitV) (k : Val → RProgram)
      (hk : ∀ completed, CodeMeans root (suspendBodyAt root (.store (Thunk.foreign c ex)))
        (prepareR completed (k .unit))) :
      CodeMeans root (Prim.suspend (EffThunk.store (Thunk.foreign c ex)))
        (.vis (.inr (.foreignRelease c ex)) k)
  -- frames pushed by the current primitive: the term's guards
  | onSuccess (body : NCode) (n : EffName) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hK : ∀ completed v, CodeMeans root (contAOf root (n.refreshA completed) v)
        (prepareR completed (K (.success v))))
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.onSuccess body n) (.vis (.inr (.guard_ .onSuccess)) g)
  | onSuccessConst (body next : NCode) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hK : ∀ completed v, CodeMeans root next (prepareR completed (K (.success v))))
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.onSuccessConst body next) (.vis (.inr (.guard_ .onSuccess)) g)
  | onFailure (body : NCode) (n : EffName) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hK : ∀ completed c, CodeMeans root (contEOf root (n.refreshE completed) c)
        (prepareR completed (K (.failure c))))
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.onFailure body n) (.vis (.inr (.guard_ .onFailure)) g)
  | onBoth (body : NCode) (a e : EffName) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hA : ∀ completed v, CodeMeans root (contAOf root (a.refreshA completed) v)
        (prepareR completed (K (.success v))))
      (hE : ∀ completed c, CodeMeans root (contEOf root (e.refreshE completed) c)
        (prepareR completed (K (.failure c))))
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.onSuccessAndFailure body a e) (.vis (.inr (.guard_ .all)) g)
  | exitFrame (body : NCode) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hK : ∀ completed ex, CodeMeans root (Prim.success (reifyExitVal ex)) (prepareR completed (K ex)))
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.exitFrame body) (.vis (.inr (.guard_ .all)) g)
  /-- An `OnExit` frame whose finalizer is a program on every view. -/
  | onExit (body : NCode) (fin : EffName) (g : Option ExitV → RProgram) (body' : RProgram)
      (K : ExitV → RProgram) (hb : CodeMeans root body body')
      (hK : ∀ completed ex program, (interpAt root completed).finalizerProgram fin ex = some program →
        CodeMeans root (finalizerCodeAt root completed ex program) (prepareR completed (K ex)))
      (hsome_prog : ∀ completed ex, ((interpAt root completed).finalizerProgram fin ex).isSome = true)
      (hnone : g none = body'.bind (unguardTail K)) (hsome : ∀ ex, g (some ex) = K ex) :
      CodeMeans root (Prim.onExit body fin false) (.vis (.inr (.guard_ (.onExit false))) g)
  /-- The scoped entry's `OnExit`: the native exit callback on both sides. -/
  | scopedFrame (body : NCode) (previous : Ctx) (scope : Nat) (g : Option ExitV → RProgram)
      (body' : RProgram) (k : ExitV → RProgram) (hb : CodeMeans root body body') (hk : Delivers k)
      (hnone : g none = body'.bind (unguardTail fun ex => .vis (.inr (.scopeExit previous scope ex)) k))
      (hsome : ∀ ex, g (some ex) = .vis (.inr (.scopeExit previous scope ex)) k) :
      CodeMeans root (Prim.onExit body (.scopedExit previous scope) false)
        (.vis (.inr (.guard_ (.onExit false))) g)
  -- generator and loop entries: the term saves the entry's continuation as an answer
  -- slot, so it only delivers
  | genEntry (p p' : Point) (k : ExitV → RProgram)
      (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
      (hk : Delivers k) :
      CodeMeans root (Prim.iterator (.gen p' [] false) Val.unit) (.vis (.inr (.gen p)) k)
  | loopEntry (p p' : Point) (cursor : Val) (k : ExitV → RProgram)
      (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
      (hk : Delivers k) :
      CodeMeans root (Prim.whileLoop (.loop p') cursor) (.vis (.inr (.loop p cursor)) k)
  | closeIterSeq (order : List FinName) (ex : ExitV) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.iterator (.store (Name.closeSeq order ex [])) Val.unit)
        (.vis (.inr (.closeIter .sequential order ex)) k)
  -- parks and the counted yield: answer slots again, on the value or the exit
  | yieldNow (priority : Nat) (k : Val → RProgram) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.yieldNowWith priority) (.vis (.inr (.yieldNow priority)) k)
  | asyncAwait (cell : DeferredKey) (request : Val) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.async (.registerAwait cell) true (some (.cancelAwait cell)))
        (.vis (.inr (.async (.registerAwait cell) request)) k)
  | asyncExternal (slot : Nat) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.async (.store (.externalRegister slot)) false none)
        (.vis (.inr (.async (.store (.externalRegister slot)) .unit)) k)
  -- `Effect.sleep(d)`, `0 < d` (the timer, A4): the registration by the machine's name
  | asyncSleep (millis : Nat) (request : Val) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))
        (.vis (.inr (.async (.store (.registerSleep millis)) request)) k)
  | joinValue (target : FiberId) (k : Val → RProgram) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.suspend (EffThunk.park (.join target .awaitValue)))
        (.vis (.inr (.await target .awaitValue)) k)
  | joinEffect (target : FiberId) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.suspend (EffThunk.park (.join target .joinEffect)))
        (.vis (.inr (.await target .joinEffect)) k)
  | joinValueStore (target : FiberId) (k : Val → RProgram) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.suspend (EffThunk.store (Thunk.park (.join target .awaitValue))))
        (.vis (.inr (.await target .awaitValue)) k)
  | joinEffectStore (target : FiberId) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.suspend (EffThunk.store (Thunk.park (.join target .joinEffect))))
        (.vis (.inr (.await target .joinEffect)) k)
  | racePark (race : Nat) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.suspend (EffThunk.park (.race race))) (.vis (.inr (.raceRegister race)) k)
  | awaitAllPark (targets : List FiberId) (k : Val → RProgram) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.suspend (EffThunk.park (.awaitAll targets)))
        (.vis (.inr (.awaitAll targets)) k)
  -- `withFiber`: one clause per fiber action, on the thunk the frame's interpreter reads
  | actFork (t : EffThunk) (program : NCode) (options : Supervision.ForkOptions) (body : Body)
      (k : Val → RProgram) (ht : (interpOf root).withFiberOf t = some (.fork program options))
      (hc : CodeMeans root program (denoteBody root body))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.fork body options)) k)
  | actForkIn (t : EffThunk) (program : NCode) (options : Supervision.ForkOptions) (q : Point)
      (scope : Nat) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.forkIn program options scope))
      (hc : CodeMeans root program (denoteAt root q))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.forkIn q options scope)) k)
  | actAmbientScope (t : EffThunk) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some .ambientScope)
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr .ambientScope) k)
  | actRunIn (t : EffThunk) (target : FiberId) (scope : Nat) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.runIn target scope))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.runIn target scope)) k)
  | actInterrupt (t : EffThunk) (target : FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.interrupt target)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.interrupt target)) k)
  | actInterruptAs (t : EffThunk) (target who : FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.interruptAs target who)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.interruptAs target who)) k)
  | actInterruptScoped (t : EffThunk) (target : FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.interruptScoped target)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.interruptScoped target)) k)
  | actInterruptAll (t : EffThunk) (targets : List FiberId) (who : Option FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.interruptAll targets who)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.interruptAll targets who)) k)
  | actAwaitAll (t : EffThunk) (targets : List FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.awaitAll targets)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.awaitAll targets)) k)
  | actAwaitAllFailFast (t : EffThunk) (targets : List FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.awaitAllFailFast targets)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.awaitAllFailFast targets)) k)
  | actSnapshotChildren (t : EffThunk) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some .snapshotChildren)
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr .snapshotChildren) k)
  | actAwaitNewChildren (t : EffThunk) (snapshot : List FiberId) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.awaitNewChildren snapshot)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.awaitNewChildren snapshot)) k)
  | actRaceAll (t : EffThunk) (entrants : List NCode) (points : List Point) (k : ExitV → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.raceAll entrants))
      (hlen : entrants.length = points.length)
      (hc : ∀ x ∈ entrants.zip (points.map (denoteAt root)), CodeMeans root x.1 x.2)
      (hk : Delivers k) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.raceAll points)) k)
  | actMask (t : EffThunk) (body : NCode) (flag : Bool) (b : Body) (k : ExitV → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.setInterruptible body flag))
      (hc : CodeMeans root body (denoteBody root b)) (hk : Delivers k) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.mask flag b)) k)
  | actSetContext (t : EffThunk) (context : Ctx) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.setContext context))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.setContext context)) k)
  | actGetContext (t : EffThunk) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some .getContext)
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr .getContext) k)
  | actGetId (t : EffThunk) (k : Val → RProgram) (ht : (interpOf root).withFiberOf t = some .getId)
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr .getId) k)
  | actCloseScope (t : EffThunk) (scope : Nat) (ex : ExitV) (k : ExitV → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.closeScope scope ex)) (hk : Delivers k) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.closeScope scope ex)) k)
  | actRefuse (t : EffThunk) (cause : CauseV) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.refuse cause))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.refuse cause)) k)
  | actDropObservers (t : EffThunk) (token : Nat) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.dropObservers token))
      (hk : ∀ v, CodeMeans root (Prim.success v) (k v)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.dropObservers token)) k)
  | actCancelRace (t : EffThunk) (race : Nat) (k : Val → RProgram)
      (ht : (interpOf root).withFiberOf t = some (.cancelRace race)) (hk : Delivers (seqR k)) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.cancelRace race)) k)
  | actClosePar (t : EffThunk) (programs : List NCode) (order : List FinName) (ex : ExitV)
      (k : ExitV → RProgram) (ht : (interpOf root).withFiberOf t = some (.closePar programs))
      (hlen : programs.length = order.length)
      (hc : ∀ x ∈ programs.zip (order.map fun fin => denoteFin fin ex), CodeMeans root x.1 x.2)
      (hk : Delivers k) :
      CodeMeans root (Prim.withFiber t) (.vis (.inr (.closeIter .parallel order ex)) k)
  /-- The native scoped entry: no action at the node, the term's `scoped` operation. -/
  | scopedNode (p : Point) (b : NativeEff) (k : ExitV → RProgram)
      (hnode : Node.at_ (.eff root) p.path = some (.eff (.scoped b))) (hk : Delivers k) :
      CodeMeans root (Prim.withFiber (EffThunk.act p)) (.vis (.inr (.scoped (p.child 0))) k)

  /-- The external callback has no cancellation finalizer and answers with an exit. -/
  | asyncForeign (op : NativeOp) (request : Val) (k : ExitV → RProgram) (hk : Delivers k) :
      CodeMeans root (Prim.async (.external op request) false none)
        (.vis (.inr (.async (.external op request) request)) k)

/-! ## The saved slots -/

/-- One frame on the frame stack and one slot on the term stack carry the same
continuation. -/
inductive SlotMeans (root : NativeEff) : NCode → ScopeFrame → Prop
  | onSuccess (body : NCode) (n : EffName) (K : ExitV → RProgram)
      (hK : ∀ completed v, CodeMeans root (contAOf root (n.refreshA completed) v)
        (prepareR completed (K (.success v)))) :
      SlotMeans root (Prim.onSuccess body n) (.resume .onSuccess K)
  | onSuccessConst (body next : NCode) (K : ExitV → RProgram)
      (hK : ∀ completed v, CodeMeans root next (prepareR completed (K (.success v)))) :
      SlotMeans root (Prim.onSuccessConst body next) (.resume .onSuccess K)
  | onFailure (body : NCode) (n : EffName) (K : ExitV → RProgram)
      (hK : ∀ completed c, CodeMeans root (contEOf root (n.refreshE completed) c)
        (prepareR completed (K (.failure c)))) :
      SlotMeans root (Prim.onFailure body n) (.resume .onFailure K)
  | onBoth (body : NCode) (a e : EffName) (K : ExitV → RProgram)
      (hA : ∀ completed v, CodeMeans root (contAOf root (a.refreshA completed) v)
        (prepareR completed (K (.success v))))
      (hE : ∀ completed c, CodeMeans root (contEOf root (e.refreshE completed) c)
        (prepareR completed (K (.failure c)))) :
      SlotMeans root (Prim.onSuccessAndFailure body a e) (.resume .all K)
  | exitFrame (body : NCode) (K : ExitV → RProgram)
      (hK : ∀ completed ex, CodeMeans root (Prim.success (reifyExitVal ex)) (prepareR completed (K ex))) :
      SlotMeans root (Prim.exitFrame body) (.resume .all K)
  | onExit (body : NCode) (fin : EffName) (K : ExitV → RProgram)
      (hK : ∀ completed ex program, (interpAt root completed).finalizerProgram fin ex = some program →
        CodeMeans root (finalizerCodeAt root completed ex program) (prepareR completed (K ex)))
      (hsome_prog : ∀ completed ex, ((interpAt root completed).finalizerProgram fin ex).isSome = true) :
      SlotMeans root (Prim.onExit body fin false) (.resume (.onExit false) K)
  | scopedFrame (body : NCode) (previous : Ctx) (scope : Nat) (K k : ExitV → RProgram)
      (hk : Delivers k) (hK : ∀ ex, K ex = .vis (.inr (.scopeExit previous scope ex)) k) :
      SlotMeans root (Prim.onExit body (.scopedExit previous scope) false) (.resume (.onExit false) K)
  | iterator (generator : EffName) (cursor : Val) : SlotMeans root (Prim.iterator generator cursor) (.iter generator)
  /-- The loop frames name the same loop up to the captured view: the frame's was minted by
  the refreshed suspension, the term's carries the point it was denoted at; the hooks read
  only the address and the environment. -/
  | whileLoop (p p' : Point) (cursor : Val)
      (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root) :
      SlotMeans root (Prim.whileLoop (.loop p') cursor) (.loop (.loop p) cursor)
  | mask (flag : Bool) : SlotMeans root (Prim.setInterruptible flag) (.restoreMask flag)
  | asyncFinalizer (name : EffName) : SlotMeans root (Prim.asyncFinalizer name) (.asyncFinalizer name)

/-- The two stacks carry the same continuations: slot for frame, the term's transparent
`answer` slots skipped, and the finalizer mask it records where the frame pushed the
restoring mask (an interruptible fiber masked by `OnExit`) or nothing (already masked). -/
inductive StackMeans (root : NativeEff) : List NCode → List ScopeFrame → Prop
  | nil : StackMeans root [] []
  | slot {f : NCode} {s : ScopeFrame} {S : List NCode} {T : List ScopeFrame}
      (h : SlotMeans root f s) (rest : StackMeans root S T) : StackMeans root (f :: S) (s :: T)
  | answer {S : List NCode} {T : List ScopeFrame} (next : ExitV → RProgram) (hd : Delivers next)
      (rest : StackMeans root S T) : StackMeans root S (.answer next :: T)
  | finMaskTrue {S : List NCode} {T : List ScopeFrame} (rest : StackMeans root S T) :
      StackMeans root (Prim.setInterruptible true :: S) (.finalizerMask true :: T)
  | finMaskFalse {S : List NCode} {T : List ScopeFrame} (rest : StackMeans root S T) :
      StackMeans root S (.finalizerMask false :: T)

/-- The mask discipline of the term's stack, read from the top with the current mask: a
`restoreMask` slot restores the mask below it; a `finalizerMask` slot delimits a finalizer
that runs masked (the frame pushed its restoring `setInterruptible true` exactly when the
mask was on, so the slot for an already masked finalizer restores nothing). -/
def MaskInv : Bool → List ScopeFrame → Prop
  | _, [] => True
  | _, .restoreMask flag :: rest => MaskInv flag rest
  | b, .finalizerMask flag :: rest => b = false ∧ MaskInv flag rest
  | b, _ :: rest => MaskInv b rest

theorem maskInv_nil (b : Bool) : MaskInv b [] := trivial

theorem maskInv_resume (b : Bool) (kind : GuardKind) (K : ExitV → RProgram) (rest : List ScopeFrame) :
    MaskInv b (.resume kind K :: rest) = MaskInv b rest := rfl

theorem maskInv_answer (b : Bool) (k : ExitV → RProgram) (rest : List ScopeFrame) :
    MaskInv b (.answer k :: rest) = MaskInv b rest := rfl

theorem maskInv_restoreMask (b flag : Bool) (rest : List ScopeFrame) :
    MaskInv b (.restoreMask flag :: rest) = MaskInv flag rest := rfl

theorem maskInv_finalizerMask (b flag : Bool) (rest : List ScopeFrame) :
    MaskInv b (.finalizerMask flag :: rest) = (b = false ∧ MaskInv flag rest) := rfl

theorem maskInv_asyncFinalizer (b : Bool) (name : EffName) (rest : List ScopeFrame) :
    MaskInv b (.asyncFinalizer name :: rest) = MaskInv b rest := rfl

theorem maskInv_iter (b : Bool) (name : EffName) (rest : List ScopeFrame) :
    MaskInv b (.iter name :: rest) = MaskInv b rest := rfl

theorem maskInv_loop (b : Bool) (name : EffName) (cursor : Val) (rest : List ScopeFrame) :
    MaskInv b (.loop name cursor :: rest) = MaskInv b rest := rfl

/-- The saved-state relation of the book: control bits equal, currents in `CodeMeans`,
stacks in `StackMeans`, and the term's mask discipline. -/
def Means (root : NativeEff) (f₁ : FFiber) (f₂ : RSaved) : Prop :=
  f₁.interruptible = f₂.interruptible ∧ f₁.interruptedCause = f₂.interruptedCause ∧
    f₁.deferredInterrupt = f₂.deferredInterrupt ∧
    CodeMeans root f₁.current f₂.current ∧ StackMeans root f₁.stack f₂.stack ∧
    MaskInv f₂.interruptible f₂.stack

/-! ## The first laws: delivering continuations -/

/-- A delivering exit continuation is related to `Prim.ofExit` on every exit. -/
theorem codeMeans_of_delivers (root : NativeEff) {k : ExitV → RProgram} (hk : Delivers k) (ex : ExitV) :
    CodeMeans root (Prim.ofExit ex) (k ex) := by
  rcases hk ex with h | ⟨k', h⟩ <;> rw [h] <;> cases ex <;> first
    | exact CodeMeans.success _
    | exact CodeMeans.failure _
    | exact CodeMeans.successUnguard _ _
    | exact CodeMeans.failureUnguard _ _

/-- A value continuation whose `seqR` delivers is related to the frame's success on every
value. -/
theorem codeMeans_of_deliversV (root : NativeEff) {k : Val → RProgram} (hk : Delivers (seqR k)) (v : Val) :
    CodeMeans root (Prim.success v) (k v) :=
  codeMeans_of_delivers root hk (.success v)

/-! ## `prepareR` and `bind` -/

theorem prepareR_pure (completed : List (FiberId × ExitV)) (ex : ExitV) :
    prepareR completed (.pure ex) = .pure ex := rfl

theorem prepareR_construct (completed : List (FiberId × ExitV)) (k : List (FiberId × ExitV) → RProgram) :
    prepareR completed (.vis (.inr .construction) k) = prepareR completed (k completed) := rfl

theorem prepareR_guard (completed : List (FiberId × ExitV)) (kind : GuardKind)
    (g : Option ExitV → RProgram) :
    prepareR completed (.vis (.inr (.guard_ kind)) g) =
      .vis (.inr (.guard_ kind)) fun
        | none => prepareR completed (g none)
        | some ex => g (some ex) := rfl

theorem prepareR_store (completed : List (FiberId × ExitV)) (o : SyncOp) (k : Val → RProgram) :
    prepareR completed (.vis (.inl o) k) = .vis (.inl o) k := rfl

/-- On any fiber operation but `construction` and a guard, `prepareR` is the identity. -/
theorem prepareR_fiber (completed : List (FiberId × ExitV)) (op : FiberOp) (k : op.answer → RProgram)
    (hc : op ≠ .construction) (hg : ∀ kind, op ≠ .guard_ kind) :
    prepareR completed (.vis (.inr op) k) = .vis (.inr op) k := by
  cases op <;> first
    | exact absurd rfl hc
    | exact absurd rfl (hg _)
    | rfl

/-- Delivering tails commute with `prepareR`: a bare exit or a closing marker is never a
construction, so resolving heads through the tail is resolving them before it. -/
theorem prepareR_bind (completed : List (FiberId × ExitV)) {h : ExitV → RProgram} (hd : Delivers h)
    (r : RProgram) : prepareR completed (r.bind h) = (prepareR completed r).bind h := by
  induction r with
  | pure ex =>
    show prepareR completed (h ex) = h ex
    rcases hd ex with hh | ⟨k', hh⟩ <;> rw [hh] <;> rfl
  | vis op k ih =>
    cases op with
    | inl o => rfl
    | inr fop =>
      cases fop with
      | construction =>
        show prepareR completed ((k completed).bind h) = (prepareR completed (k completed)).bind h
        exact ih completed
      | guard_ kind =>
        refine congrArg (@Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.guard_ kind))) (funext fun o => ?_)
        cases o with
        | none => exact ih none
        | some ex => rfl
      | _ => rfl

/-- A delivering continuation followed by a delivering tail delivers. -/
theorem delivers_bind {k h : ExitV → RProgram} (hk : Delivers k) (hd : Delivers h) :
    Delivers fun ex => (k ex).bind h := by
  intro ex
  show (k ex).bind h = .pure ex ∨ ∃ k', (k ex).bind h = .vis (.inr (.unguard ex)) k'
  rcases hk ex with hh | ⟨k', hh⟩
  · rw [hh]
    show h ex = .pure ex ∨ ∃ k', h ex = .vis (.inr (.unguard ex)) k'
    exact hd ex
  · rw [hh]
    exact Or.inr ⟨fun r => (k' r).bind h, rfl⟩

theorem delivers_seqR_bind {k : Val → RProgram} {h : ExitV → RProgram} (hk : Delivers (seqR k))
    (hd : Delivers h) : Delivers (seqR fun v => (k v).bind h) := by
  intro ex
  cases ex with
  | failure c => exact Or.inl rfl
  | success v =>
    have := delivers_bind hk hd (.success v)
    exact this

theorem unguardTail_bind (K h : ExitV → RProgram) :
    (fun ex => (unguardTail K ex).bind h) = unguardTail fun ex => (K ex).bind h := rfl

/-! ## Closure under delivering tails and under `prepareR` -/

/-- The relation is closed under running the term into a delivering tail: the frame's
current stays, the tail only hands the body's exit on. -/
theorem CodeMeans.bindTail {root : NativeEff} {c : NCode} {r : RProgram} (h : CodeMeans root c r)
    {t : ExitV → RProgram} (ht : Delivers t) : CodeMeans root c (r.bind t) := by
  induction h with
  | success v =>
    rcases ht (.success v) with hh | ⟨k', hh⟩
    · show CodeMeans root _ (t (.success v)); rw [hh]; exact CodeMeans.success v
    · show CodeMeans root _ (t (.success v)); rw [hh]; exact CodeMeans.successUnguard v k'
  | successUnguard v k => exact CodeMeans.successUnguard v _
  | failure c =>
    rcases ht (.failure c) with hh | ⟨k', hh⟩
    · show CodeMeans root _ (t (.failure c)); rw [hh]; exact CodeMeans.failure c
    · show CodeMeans root _ (t (.failure c)); rw [hh]; exact CodeMeans.failureUnguard c k'
  | failureUnguard c k => exact CodeMeans.failureUnguard c _
  | finishSuccess v k => exact CodeMeans.finishSuccess v _
  | finishFailure c k => exact CodeMeans.finishFailure c _
  | syncOp o k _ ih => exact CodeMeans.syncOp o _ ih
  | syncStore o k _ ih => exact CodeMeans.syncStore o _ ih
  | syncPure p k _ ih => exact CodeMeans.syncPure p _ ih
  | suspendBody p k _ ih =>
    refine CodeMeans.suspendBody p _ fun completed => ?_
    rw [prepareR_bind completed ht]
    exact ih completed
  | suspendMemo q m scope k _ ih =>
    refine CodeMeans.suspendMemo q m scope _ fun completed => ?_
    rw [prepareR_bind completed ht]
    exact ih completed
  | frontier p p' reason k hp hloop => exact CodeMeans.frontier p p' reason _ hp hloop
  | yieldError p e k _ ih =>
    refine CodeMeans.yieldError p e _ fun completed => ?_
    rw [prepareR_bind completed ht]
    exact ih completed
  | closeWalk strategy order ex k _ ih =>
    refine CodeMeans.closeWalk strategy order ex _ fun completed => ?_
    rw [prepareR_bind completed ht]
    exact ih completed
  | foreignRelease c ex k _ ih =>
    refine CodeMeans.foreignRelease c ex _ fun completed => ?_
    rw [prepareR_bind completed ht]
    exact ih completed
  | onSuccess body n g body' K hb hK hnone hsome ihb ihK =>
    refine CodeMeans.onSuccess body n _ body' (fun ex => (K ex).bind t) hb ?_ ?_ ?_
    · intro completed v
      rw [prepareR_bind completed ht]
      exact ihK completed v
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | onSuccessConst body next g body' K hb hK hnone hsome ihb ihK =>
    refine CodeMeans.onSuccessConst body next _ body' (fun ex => (K ex).bind t) hb ?_ ?_ ?_
    · intro completed v
      rw [prepareR_bind completed ht]
      exact ihK completed v
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | onFailure body n g body' K hb hK hnone hsome ihb ihK =>
    refine CodeMeans.onFailure body n _ body' (fun ex => (K ex).bind t) hb ?_ ?_ ?_
    · intro completed c
      rw [prepareR_bind completed ht]
      exact ihK completed c
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | onBoth body a e g body' K hb hA hE hnone hsome ihb ihA ihE =>
    refine CodeMeans.onBoth body a e _ body' (fun ex => (K ex).bind t) hb ?_ ?_ ?_ ?_
    · intro completed v
      rw [prepareR_bind completed ht]
      exact ihA completed v
    · intro completed c
      rw [prepareR_bind completed ht]
      exact ihE completed c
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | exitFrame body g body' K hb hK hnone hsome ihb ihK =>
    refine CodeMeans.exitFrame body _ body' (fun ex => (K ex).bind t) hb ?_ ?_ ?_
    · intro completed ex
      rw [prepareR_bind completed ht]
      exact ihK completed ex
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | onExit body fin g body' K hb hK hsome_prog hnone hsome ihb ihK =>
    refine CodeMeans.onExit body fin _ body' (fun ex => (K ex).bind t) hb ?_ hsome_prog ?_ ?_
    · intro completed ex program hprog
      rw [prepareR_bind completed ht]
      exact ihK completed ex program hprog
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
  | scopedFrame body previous scope g body' k hb hk hnone hsome ihb =>
    refine CodeMeans.scopedFrame body previous scope _ body' (fun ex => (k ex).bind t) hb
      (delivers_bind hk ht) ?_ ?_
    · show (g none).bind t = _
      rw [hnone, Effects.Program.bind_assoc]
      rfl
    · intro ex
      show (g (some ex)).bind t = _
      rw [hsome]
      rfl
  | genEntry p p' k hp hk => exact CodeMeans.genEntry p p' _ hp (delivers_bind hk ht)
  | loopEntry p p' cursor k hp hk => exact CodeMeans.loopEntry p p' cursor _ hp (delivers_bind hk ht)
  | closeIterSeq order ex k hk => exact CodeMeans.closeIterSeq order ex _ (delivers_bind hk ht)
  | yieldNow priority k hk => exact CodeMeans.yieldNow priority _ (delivers_seqR_bind hk ht)
  | asyncAwait cell request k hk => exact CodeMeans.asyncAwait cell request _ (delivers_bind hk ht)
  | asyncExternal slot k hk => exact CodeMeans.asyncExternal slot _ (delivers_bind hk ht)
  | asyncForeign op request k hk => exact CodeMeans.asyncForeign op request _ (delivers_bind hk ht)
  | asyncSleep millis request k hk => exact CodeMeans.asyncSleep millis request _ (delivers_bind hk ht)
  | joinValue target k hk => exact CodeMeans.joinValue target _ (delivers_seqR_bind hk ht)
  | joinEffect target k hk => exact CodeMeans.joinEffect target _ (delivers_bind hk ht)
  | joinValueStore target k hk => exact CodeMeans.joinValueStore target _ (delivers_seqR_bind hk ht)
  | joinEffectStore target k hk => exact CodeMeans.joinEffectStore target _ (delivers_bind hk ht)
  | racePark race k hk => exact CodeMeans.racePark race _ (delivers_bind hk ht)
  | awaitAllPark targets k hk => exact CodeMeans.awaitAllPark targets _ (delivers_seqR_bind hk ht)
  | actFork t' program options body k ht' hc hk ihc ihk => exact CodeMeans.actFork t' program options body _ ht' hc ihk
  | actForkIn t' program options q scope k ht' hc hk ihc ihk =>
    exact CodeMeans.actForkIn t' program options q scope _ ht' hc ihk
  | actAmbientScope t' k ht' hk ihk => exact CodeMeans.actAmbientScope t' _ ht' ihk
  | actRunIn t' target scope k ht' hk ihk => exact CodeMeans.actRunIn t' target scope _ ht' ihk
  | actInterrupt t' target k ht' hk => exact CodeMeans.actInterrupt t' target _ ht' (delivers_seqR_bind hk ht)
  | actInterruptAs t' target who k ht' hk =>
    exact CodeMeans.actInterruptAs t' target who _ ht' (delivers_seqR_bind hk ht)
  | actInterruptScoped t' target k ht' hk =>
    exact CodeMeans.actInterruptScoped t' target _ ht' (delivers_seqR_bind hk ht)
  | actInterruptAll t' targets who k ht' hk =>
    exact CodeMeans.actInterruptAll t' targets who _ ht' (delivers_seqR_bind hk ht)
  | actAwaitAll t' targets k ht' hk => exact CodeMeans.actAwaitAll t' targets _ ht' (delivers_seqR_bind hk ht)
  | actAwaitAllFailFast t' targets k ht' hk =>
    exact CodeMeans.actAwaitAllFailFast t' targets _ ht' (delivers_seqR_bind hk ht)
  | actSnapshotChildren t' k ht' hk ihk => exact CodeMeans.actSnapshotChildren t' _ ht' ihk
  | actAwaitNewChildren t' snapshot k ht' hk =>
    exact CodeMeans.actAwaitNewChildren t' snapshot _ ht' (delivers_seqR_bind hk ht)
  | actRaceAll t' entrants points k ht' hlen hc hk ihc =>
    exact CodeMeans.actRaceAll t' entrants points _ ht' hlen hc (delivers_bind hk ht)
  | actMask t' body flag b k ht' hc hk ihc => exact CodeMeans.actMask t' body flag b _ ht' hc (delivers_bind hk ht)
  | actSetContext t' context k ht' hk ihk => exact CodeMeans.actSetContext t' context _ ht' ihk
  | actGetContext t' k ht' hk ihk => exact CodeMeans.actGetContext t' _ ht' ihk
  | actGetId t' k ht' hk ihk => exact CodeMeans.actGetId t' _ ht' ihk
  | actCloseScope t' scope ex k ht' hk => exact CodeMeans.actCloseScope t' scope ex _ ht' (delivers_bind hk ht)
  | actRefuse t' cause k ht' hk ihk => exact CodeMeans.actRefuse t' cause _ ht' ihk
  | actDropObservers t' token k ht' hk ihk => exact CodeMeans.actDropObservers t' token _ ht' ihk
  | actCancelRace t' race k ht' hk => exact CodeMeans.actCancelRace t' race _ ht' (delivers_seqR_bind hk ht)
  | actClosePar t' programs order ex k ht' hlen hc hk ihc =>
    exact CodeMeans.actClosePar t' programs order ex _ ht' hlen hc (delivers_bind hk ht)
  | scopedNode p b k hnode hk => exact CodeMeans.scopedNode p b _ hnode (delivers_bind hk ht)

/-- The relation is closed under resolving the term's heads against a completed view: a
related term has no construction head, and a guard's normal branch stays related. -/
theorem CodeMeans.prepare {root : NativeEff} {c : NCode} {r : RProgram} (h : CodeMeans root c r)
    (completed : List (FiberId × ExitV)) : CodeMeans root c (prepareR completed r) := by
  induction h with
  | success v => exact CodeMeans.success v
  | successUnguard v k => exact CodeMeans.successUnguard v k
  | failure c => exact CodeMeans.failure c
  | failureUnguard c k => exact CodeMeans.failureUnguard c k
  | finishSuccess v k => exact CodeMeans.finishSuccess v k
  | finishFailure c k => exact CodeMeans.finishFailure c k
  | syncOp o k hk _ => exact CodeMeans.syncOp o k hk
  | syncStore o k hk _ => exact CodeMeans.syncStore o k hk
  | syncPure p k hk _ => exact CodeMeans.syncPure p k hk
  | suspendBody p k hk _ => exact CodeMeans.suspendBody p k hk
  | suspendMemo q m scope k hk _ => exact CodeMeans.suspendMemo q m scope k hk
  | frontier p p' reason k hp hloop => exact CodeMeans.frontier p p' reason k hp hloop
  | yieldError p e k hk _ => exact CodeMeans.yieldError p e k hk
  | closeWalk strategy order ex k hk _ => exact CodeMeans.closeWalk strategy order ex k hk
  | foreignRelease c ex k hk _ => exact CodeMeans.foreignRelease c ex k hk
  | onSuccess body n g body' K hb hK hnone hsome ihb _ =>
    refine CodeMeans.onSuccess body n _ (prepareR completed body') K ihb hK ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail K)]
    · intro ex; exact hsome ex
  | onSuccessConst body next g body' K hb hK hnone hsome ihb _ =>
    refine CodeMeans.onSuccessConst body next _ (prepareR completed body') K ihb hK ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail K)]
    · intro ex; exact hsome ex
  | onFailure body n g body' K hb hK hnone hsome ihb _ =>
    refine CodeMeans.onFailure body n _ (prepareR completed body') K ihb hK ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail K)]
    · intro ex; exact hsome ex
  | onBoth body a e g body' K hb hA hE hnone hsome ihb _ _ =>
    refine CodeMeans.onBoth body a e _ (prepareR completed body') K ihb hA hE ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail K)]
    · intro ex; exact hsome ex
  | exitFrame body g body' K hb hK hnone hsome ihb _ =>
    refine CodeMeans.exitFrame body _ (prepareR completed body') K ihb hK ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail K)]
    · intro ex; exact hsome ex
  | onExit body fin g body' K hb hK hsome_prog hnone hsome ihb _ =>
    refine CodeMeans.onExit body fin _ (prepareR completed body') K ihb hK hsome_prog ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail _)]
    · intro ex; exact hsome ex
  | scopedFrame body previous scope g body' k hb hk hnone hsome ihb =>
    refine CodeMeans.scopedFrame body previous scope _ (prepareR completed body') k ihb hk ?_ ?_
    · show prepareR completed (g none) = _
      rw [hnone, prepareR_bind completed (delivers_unguardTail _)]
    · intro ex; exact hsome ex
  | genEntry p p' k hp hk => exact CodeMeans.genEntry p p' k hp hk
  | loopEntry p p' cursor k hp hk => exact CodeMeans.loopEntry p p' cursor k hp hk
  | closeIterSeq order ex k hk => exact CodeMeans.closeIterSeq order ex k hk
  | yieldNow priority k hk => exact CodeMeans.yieldNow priority k hk
  | asyncAwait cell request k hk => exact CodeMeans.asyncAwait cell request k hk
  | asyncExternal slot k hk => exact CodeMeans.asyncExternal slot k hk
  | asyncForeign op request k hk => exact CodeMeans.asyncForeign op request k hk
  | asyncSleep millis request k hk => exact CodeMeans.asyncSleep millis request k hk
  | joinValue target k hk => exact CodeMeans.joinValue target k hk
  | joinEffect target k hk => exact CodeMeans.joinEffect target k hk
  | joinValueStore target k hk => exact CodeMeans.joinValueStore target k hk
  | joinEffectStore target k hk => exact CodeMeans.joinEffectStore target k hk
  | racePark race k hk => exact CodeMeans.racePark race k hk
  | awaitAllPark targets k hk => exact CodeMeans.awaitAllPark targets k hk
  | actFork t program options body k ht hc hk _ _ => exact CodeMeans.actFork t program options body k ht hc hk
  | actForkIn t program options q scope k ht hc hk _ _ =>
    exact CodeMeans.actForkIn t program options q scope k ht hc hk
  | actAmbientScope t k ht hk _ => exact CodeMeans.actAmbientScope t k ht hk
  | actRunIn t target scope k ht hk _ => exact CodeMeans.actRunIn t target scope k ht hk
  | actInterrupt t target k ht hk => exact CodeMeans.actInterrupt t target k ht hk
  | actInterruptAs t target who k ht hk => exact CodeMeans.actInterruptAs t target who k ht hk
  | actInterruptScoped t target k ht hk => exact CodeMeans.actInterruptScoped t target k ht hk
  | actInterruptAll t targets who k ht hk => exact CodeMeans.actInterruptAll t targets who k ht hk
  | actAwaitAll t targets k ht hk => exact CodeMeans.actAwaitAll t targets k ht hk
  | actAwaitAllFailFast t targets k ht hk => exact CodeMeans.actAwaitAllFailFast t targets k ht hk
  | actSnapshotChildren t k ht hk _ => exact CodeMeans.actSnapshotChildren t k ht hk
  | actAwaitNewChildren t snapshot k ht hk => exact CodeMeans.actAwaitNewChildren t snapshot k ht hk
  | actRaceAll t entrants points k ht hlen hc hk _ => exact CodeMeans.actRaceAll t entrants points k ht hlen hc hk
  | actMask t body flag b k ht hc hk _ => exact CodeMeans.actMask t body flag b k ht hc hk
  | actSetContext t context k ht hk _ => exact CodeMeans.actSetContext t context k ht hk
  | actGetContext t k ht hk _ => exact CodeMeans.actGetContext t k ht hk
  | actGetId t k ht hk _ => exact CodeMeans.actGetId t k ht hk
  | actCloseScope t scope ex k ht hk => exact CodeMeans.actCloseScope t scope ex k ht hk
  | actRefuse t cause k ht hk _ => exact CodeMeans.actRefuse t cause k ht hk
  | actDropObservers t token k ht hk _ => exact CodeMeans.actDropObservers t token k ht hk
  | actCancelRace t race k ht hk => exact CodeMeans.actCancelRace t race k ht hk
  | actClosePar t programs order ex k ht hlen hc hk _ =>
    exact CodeMeans.actClosePar t programs order ex k ht hlen hc hk
  | scopedNode p b k hnode hk => exact CodeMeans.scopedNode p b k hnode hk

end Effect4.Program.Sched
