import Effect4.Program.DenoteR
import Effect4.Machine.Behaviour

/-!
# The term scheduler's state and interpreter (R3, restated by P2)

Packet: `Test/contracts/program-runtime-r.contract.md`; plan and corrections:
`docs/research/2026-09-06-r3-r4-implementation.md` and the P2 phase model of
`docs/research/2026-09-06-p0-fable-record.md` §4. The machine, stores and
decisions are the existing ones; `RProgram` is their semantic code parameter.
Functions in a saved continuation belong to this proof carrier, never `Eff`.

Direct program shapes transcribe `Machine/Stores.lean:1041-1181` and
`Program/Compile.lean:582-734`. No recursive translation through named
primitive continuations is claimed. `RSTATE-FB-STORE-CODE` leaves other
manually inserted Deferred programs at an unsupported frontier. The source
store interface and Completion tape produce exactly the three decoded shapes.
`RSTATE-FB-EVALUATOR-FIELD` names the unused frame-only interpreter hooks;
`RSTATE-FB-ONSUCCESS-NAME` restricts the shared loop's composition hook to
`restore`, its sole producer. `RSTATE-FB-IDENTITY`: semantic saved states have
no serialization or decidable equality. No host correspondence is proved.

The generator walk `walkR` is the term instance of the compile's `runStmts`: the
same navigation (`blockAt`, `blockExit`, `loopExit`), the source classifier
`inlineYield` for the inline folds, and the term as the yielded code. `interpR`'s
`iterNext` and `loopBody` are that walk and the addressed loop body; the loop's
test, step and done hooks are the compile's own.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- The saved continuations and hooks above a term, mirroring the frame slots.
`resume` is a lexical handler boundary. `answer` is the continuation of an operation
whose answer arrives as code through the shared loop, the operation-answer adapter
(P0 record §4): delivering into it continues the same delivery when its result is a
closing marker or a bare exit. `iter` and `loop` are the generator's and the cursor
loop's own frames, first-order, whose continuations run inside the body's delivery.
`finalizerMask` delimits one `onExitR` cleanup, including an already masked one. -/
inductive ScopeFrame
  | resume (kind : GuardKind) (next : ExitV → RProgram)
  | answer (next : ExitV → RProgram)
  | restoreMask (flag : Bool)
  | asyncFinalizer (name : EffName)
  | finalizerMask (flag : Bool)
  | iter (generator : EffName)
  | loop (loop : EffName) (cursor : Val)

structure RSaved where
  current : RProgram
  stack : List ScopeFrame
  interruptible : Bool
  interruptedCause : Option CauseV
  deferredInterrupt : Bool

def RSaved.pendingCause (f : RSaved) : CauseV := f.interruptedCause.getD Cause.empty

/-- `exitFiber` is the sole producer of `continueWith`, with a restore name.
Other names are the declared unused-hook refusal, not an interpretation. -/
def restoreR (code : RProgram) (name : EffName) : RProgram :=
  match name with
  | .restore ex => (guardR .onSuccess code).bind (seqR fun _ => .pure ex)
  | _ => .pure outsideExit

@[reducible] instance termCore :
    FiberCore EffName Val Err Defect FiberId Ann RProgram RSaved where
  current := RSaved.current
  answerWith := fun f code => { f with current := code }
  start := fun code flag => ⟨code, [], flag, none, false⟩
  interruptible := RSaved.interruptible
  interruptedCause := RSaved.interruptedCause
  deferredInterrupt := RSaved.deferredInterrupt
  recordCause := fun f cause => { f with interruptedCause := some cause }
  setDeferred := fun f flag => { f with deferredInterrupt := flag }
  pendingFailure := fun f =>
    { f with current := .pure (.failure f.pendingCause), deferredInterrupt := false }
  pushAsyncFinalizer := fun name f => { f with stack := .asyncFinalizer name :: f.stack }
  -- the generator's own frame under the effect a command yields on its behalf (§20); the
  -- term's iterator frame carries no cursor
  pushIterator := fun name _ f => { f with stack := .iter name :: f.stack }
  clearStack := fun f => { f with stack := [] }
  success := fun v => .pure (.success v)
  failure := fun c => .pure (.failure c)
  onSuccess := restoreR
  -- the injected `Yield` passes its void answer on, as the frame's `Prim.yieldNowWith 0`
  -- resumes with `success void`; the constant continuation then discards it
  yieldBefore := fun previous =>
    (guardR .onSuccess (.vis (.inr (.yieldNow 0)) fun v => .pure (.success v))).bind
      (seqR fun _ => previous)

abbrev RState := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
abbrev RFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram RSaved
abbrev RInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram
abbrev RIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
abbrev RCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- Resolve an existing source point into its term. -/
def denoteAt (root : NativeEff) (p : Point) : RProgram :=
  match Node.at_ (.eff root) p.path with
  | some (.eff e) => denoteR root e p
  | _ => .pure badShapeExit

/-- The scope's finalizer shapes (`Stores.finProgram`). -/
def denoteFin : FinName → ExitV → RProgram
  | .interruptFiber fiber true, _ => fiberValR (.interruptScoped fiber) rfl
  | .interruptFiber fiber false, _ => fiberValR (.interrupt fiber) rfl
  | .closeChildScope scope, ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure
  | .detachFromParent parent key, _ => storeR (.scopeRemove parent key)
  | .release label fails, _ =>
    .pure (if fails then .failure (Cause.fail (.tag label)) else .success .unit)
  | .parkThen slot, _ => .vis (.inr (.async (.store (.externalRegister slot)) .unit)) Effects.Program.pure
  | .awaitNewChildren snapshot, _ => fiberValR (.awaitNewChildren snapshot) rfl
  -- a capture's release (V1): the counted suspend, then `provideContext(release(a, exit),
  -- context)` (`internal/effect.ts:3983`, `:2180-2199`): the current context read, the captured
  -- one set, the release at the capture's point over the exit under the finalizer restoring
  -- the previous context — constructed with the view at its invocation (`constructR`), as the
  -- frame's `interpAt` refreshes the release's name
  | .foreign c, ex => .vis (.inr (.foreignRelease c ex)) fun _ =>
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
        match Val.context? v with
        | some previous =>
          (guardR .onSuccess (fiberValR (.setContext c.ctx) rfl)).bind (seqR fun _ =>
            constructR fun completed =>
              .vis (.inr (.mask false
                (.release ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)) previous)))
                Effects.Program.pure)
        | none => .pure badShapeExit)
  -- `fromBuild`'s `onExit` (`Layer.ts:343`, the join): close the layer scope on failure only
  | .closeChildOnFailure scope, .failure cause =>
    .vis (.inr (.closeScope scope (.failure cause))) Effects.Program.pure
  | .closeChildOnFailure _, .success _ => .pure (.success .unit)
  -- the memo entry finalizer (`Layer.ts:401-410`, the join): `observers--`; the last
  -- observer's release answers the layer scope, closed with the exit
  | .memoEntry layer memoMap, ex =>
    (guardR .onSuccess (storeR (.memoRelease layer memoMap))).bind (seqR fun v =>
      match Val.scope? v with
      | some s => .vis (.inr (.closeScope s ex)) Effects.Program.pure
      | none => .pure (.success .unit))
  -- `memoMapBuild`'s `onExit` (`:414-417`): the exit stored, the Deferred completed
  | .memoDone layer memoMap, ex => storeR (.memoComplete layer memoMap ex)

/-- `acquireRelease`'s masked half at the term (`internal/effect.ts:3978-3986`, V1): the
counted `Scope` read, the acquire (its term at the point's child 0), the registration of the
release as a capture, and the closed branch that runs the release now. -/
def acquireInR (acquire : RProgram) (p : Point) (ctx : Ctx) : RProgram :=
  (guardR .onSuccess (fiberValR .ambientScope rfl)).bind (seqR fun v =>
    match Val.scope? v with
    | some s =>
      (guardR .onSuccess acquire).bind (seqR fun a =>
        (guardR .onSuccess (storeR (.scopeAdd s (.foreign (p.capture a ctx))))).bind (seqR fun w =>
          if w = Val.unit then .pure (.success a)
          else
            match exitOfVal w with
            | some ex =>
              (guardR .onSuccess (denoteFin (.foreign (p.capture a ctx)) ex)).bind
                (seqR fun _ => .pure (.success a))
            | none => .pure badShapeExit))
    | none => .pure badShapeExit)

/-- External answers and the programs stored by the source Deferred interface. -/
def denoteCompletion : Completion Val Err Defect FiberId Ann → RProgram
  | .ofExit ex => .pure ex
  | .ofRefGet cell => storeR (.refGet cell)

/-- A shape decoder, not an interpreter for arbitrary named store programs. -/
def denoteStored : Effect4.Machine.Program → RProgram
  | .success v => .pure (.success v)
  | .failure c => .pure (.failure c)
  | .sync (.op (.refGet cell)) => storeR (.refGet cell)
  | _ => pending .unsupported (rootPoint 0)

theorem denoteStored_completion (answer : Completion Val Err Defect FiberId Ann) :
    denoteStored (completionPrim answer) = denoteCompletion answer := by
  cases answer with
  | ofExit ex => cases ex <;> rfl
  | ofRefGet _ => rfl

/-- The `Exit` primitive around a finalizer (`internal/effect.ts:3617`, `:3621-3637`): the
term's both-arm boundary, answering the reified exit; it never fails. -/
def exitR (body : RProgram) : RProgram :=
  (guardR .all body).bind fun ex => .pure (.success (reifyExitVal ex))

/-- `Stores.closeSeqStep` at the term instance (§20): the sequential close generator's step,
its finalizer under the term's own `Exit` guard. -/
def closeSeqStepR (remaining : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram :=
  let captured := captured ++ reasonsOfVal value
  match remaining with
  | [] => closeDone captured
  | fin :: rest =>
    IterStep.resume (exitR (denoteFin fin exit)) (.store (.closeSeq rest exit captured))

/-- `scopeCloseFinalizers` at the term instance (§20): the counted `fnUntraced` suspend, then
the counted `Iterator` entry of the walk. -/
def closeWalkR (strategy : FinalizerStrategy) (order : List FinName) (ex : ExitV) : RProgram :=
  .vis (.inr (.closeWalk strategy order ex)) fun _ =>
    .vis (.inr (.closeIter strategy order ex)) Effects.Program.pure

/-- Unsafe close shares its state snapshot with the native frame adapter and
distinguishes no returned effect from a successful returned effect
(`internal/effect.ts:3782-3797`). A single finalizer is returned directly; two or more are
the generator walk (§20). The closer's mask is inherited at the daemons' fork. -/
def closeScopeUnsafeR (scope : Nat) (ex : ExitV) (_interruptible : Bool)
    (state : Stores) : Option (Stores × Option RProgram) := do
  let (state, strategy, order) ← scopeCloseSnapshot scope ex state
  return (state, match order with
    | [] => none
    | [fin] => some (denoteFin fin ex)
    | _ => some (closeWalkR strategy order ex))

/-- `Scope.close(scope, exit)` (`:3775-3776`): the unsafe close's program, or void. -/
def closeScopeR (scope : Nat) (ex : ExitV) (interruptible : Bool)
    (state : Stores) : Option (Stores × RProgram) :=
  (closeScopeUnsafeR scope ex interruptible state).map fun r =>
    (r.1, r.2.getD (.pure (.success .unit)))

def denoteBody (root : NativeEff) : Body → RProgram
  | .at_ p => denoteAt root p
  | .fin fin ex => denoteFin fin ex
  | .raceCleanup race => fiberValR (.cancelRace race) rfl
  | .acquireIn p ctx => acquireInR (denoteAt root (p.child 0)) p ctx
  | .release q previous => onExitR (denoteAt root q) fun _ => fiberValR (.setContext previous) rfl

/-- `Stores.raceSettleProgram` at the term instance: the exit alone, or the masked
race-named cleanup then the exit (`internal/effect.ts:1510-1514`, D6a). -/
def denoteRaceSettle (race : Nat) (cleanupNeeded : Bool) (ex : ExitV) : RProgram :=
  if cleanupNeeded then
    (guardR .onSuccess (.vis (.inr (.mask false (.raceCleanup race))) Effects.Program.pure)).bind
      (seqR fun _ => .pure ex)
  else .pure ex

def denoteStoreCancel : Name → RProgram
  | .withWaiter (.cancelAwait cell) waiter token => storeR (.deferredAwaitCleanup cell waiter token)
  | .withWaiter .cancelPark _ token => fiberValR (.dropObservers token) rfl
  | .withWaiter (.cancelRace race) _ _ => fiberValR (.cancelRace race) rfl
  | _ => .pure (.success .unit)

def denoteCancel : EffName → RProgram
  | .withWaiter (.cancelAwait cell) waiter token => storeR (.deferredAwaitCleanup cell waiter token)
  | .withWaiter (.store base) waiter token => denoteStoreCancel (.withWaiter base waiter token)
  | .store name => denoteStoreCancel name
  | _ => .pure (.success .unit)

/-- The generator walk at the term instance (`Compile.runStmts` at the frame instance):
from the list at `pc` with `env` in scope, through pure statements to the next yield,
the return, or the body's end. Inline source exits are folded by `inlineYield`; a
yielded failure halts; anything else resumes with the term at its point and the
advanced generator name. An exhausted scan resumes with the compile-fuel frontier at
the exhausted point, under the same advanced name. -/
def walkR (root : NativeEff) (p : Point) :
    Nat → List Nat → List Val → List Val →
      List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram
  | 0, pc, env, folded =>
    (folded, .resume (pending .compileFuel { p with path := p.path ++ [0] ++ pc, env := env, fuel := 0 })
      (.gen { p with env := env } pc false))
  | fuel + 1, pc, env, folded =>
    match blockAt root p pc with
    | some .nil =>
      match blockExit root p pc env with
      | none => (folded, .done Val.unit)
      | some (pc', env') => walkR root p fuel pc' env' folded
    | some (.cons s _) =>
      match s with
      | .bindYield e => yieldOf e true fuel pc env folded
      | .yieldDiscard e => yieldOf e false fuel pc env folded
      | .ret v =>
        match evalTerm env v with
        | some value => (folded, .done value)
        | none => (folded, .halt (Cause.die Defect.badName))
      | .ifElse test _ _ =>
        match evalTerm env test with
        | some (.bool true) => walkR root p fuel (pc ++ [0, 0]) env folded
        | some (.bool false) => walkR root p fuel (pc ++ [0, 1]) env folded
        | _ => (folded, .halt (Cause.die Defect.badName))
      | .whileTrue _ => walkR root p fuel (pc ++ [0, 0]) env folded
      | .breakLoop =>
        match loopExit root (pc.length + 1) p pc env with
        | some (pc', env') => walkR root p fuel pc' env' folded
        | none => (folded, .halt (Cause.die Defect.badName))
    | none => (folded, .halt (Cause.die Defect.badName))
where
  /-- The effect of a yield statement at `pc`, denoted at its own point. -/
  yieldOf (e : NativeEff) (bind : Bool) (fuel : Nat) (pc : List Nat) (env : List Val)
      (folded : List Val) :
      List Val × IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram :=
    let q : Point := { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
    match inlineYield e q with
    | some (.success value) =>
      walkR root p fuel (pc ++ [1]) (if bind then env ++ [value] else env) (folded ++ [value])
    | some (.failure cause) => (folded, .halt cause)
    | none => (folded, .resume (denoteR root e q) (.gen { p with env := env } (pc ++ [1]) bind))

/-- The actual loop and generator hooks, with the same non-code fields as `interpOf`.
Frame-only hooks have explicit refusal bodies and are not read by `evaluateR`. -/
def interpR (root : NativeEff) : RInterp where
  contA := fun _ _ => .pure outsideExit
  contE := fun _ _ => .pure outsideExit
  syncValue := (interpOf root).syncValue
  suspendBody := fun
    | .body p => denoteAt root p
    | _ => .pure outsideExit
  finalizerExit := (interpOf root).finalizerExit
  reifyExit := reifyExitVal
  iterNext := fun name value =>
    match name with
    | .gen p pc bind => walkR root p p.fuel pc (if bind then p.env ++ [value] else p.env) []
    -- the close generators (§20): the sequential walk's step, and the parallel walk's inline
    -- merge of the exits its await answered
    | .store (.closeSeq remaining exit captured) => ([], closeSeqStepR remaining exit captured value)
    | .store .closeParDone => ([], closeDone (reasonsOfVal value))
    | _ => ([], .done value)
  loopTest := (interpOf root).loopTest
  loopBody := fun name cursor =>
    match name with
    | .loop p => denoteAt root (p.childWith 0 cursor)
    | _ => .pure (.success cursor)
  loopStep := (interpOf root).loopStep
  loopDone := (interpOf root).loopDone
  notImplemented := .notImplemented
  cancelThenFail := fun name cause =>
    (guardR .onSuccess (denoteCancel name)).bind (seqR fun _ => .pure (.failure cause))
  parkOf := fun _ => none
  -- the named parks as term operations: a race's registration and the two join modes
  parkCode := fun
    | .race race => .vis (.inr (.raceRegister race)) Effects.Program.pure
    | .join target .joinEffect => .vis (.inr (.await target .joinEffect)) Effects.Program.pure
    | .join target .awaitValue => .vis (.inr (.await target .awaitValue)) fun v => .pure (.success v)
    | .awaitAll targets => .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)
  -- the interrupt programs as term operations (source-repairs §19, D6b)
  interruptCode := fun target => fiberValR (.interrupt target) rfl
  interruptAsCode := fun target who => fiberValR (.interruptAs target who) rfl
  interruptAllCode := fun targets => fiberValR (.interruptAll targets none) rfl
  withFiberOf := fun _ => none
  syncState := fun _ _ => none
  registerAsync := fun name fiber token state =>
    match name with
    | .registerAwait cell | .store (.registerAwait cell) =>
      let (deferreds, immediate) := state.deferreds.register cell fiber token
      ({ state with deferreds }, immediate.map denoteStored)
    | _ => (state, none)
  answerCode := denoteCompletion
  dueResumes := fun state =>
    let (due, deferreds) := state.deferreds.drainDue
    (due.map fun d => (d.1, d.2.1, denoteStored d.2.2), { state with deferreds })
  cancelName := (interpOf root).cancelName
  abortName := .abort
  parkCancelName := .store .cancelPark
  raceCancelName := fun race => .store (.cancelRace race)
  raceSettle := denoteRaceSettle
  finalizerProgram := fun name ex =>
    match name with
    | .fin p => some (denoteAt root (p.childWith 1 (reifyExitVal ex)))
    | .scopeClose scope => some (.vis (.inr (.closeScope scope ex)) Effects.Program.pure)
    | .restoreCtx previous => some (fiberValR (.setContext previous) rfl)
    | .store (.finalizerName fin) => some (denoteFin fin ex)
    | _ => none
  restoreName := .restore
  mergeName := .merge
  scopeStatus := (interpOf root).scopeStatus
  scopeLinkFiber := (interpOf root).scopeLinkFiber
  dropFinalizer := (interpOf root).dropFinalizer
  closeScope := fun scope ex flag _ => closeScopeR scope ex flag
  ambientScope := Ctx.ambientScope
  budgetOf := (interpOf root).budgetOf
  emptyContext := emptyCtx
  contextValue := Val.context
  exitValue := fun ex mode => .pure (match mode with
    | .awaitValue => .success (reifyExitVal ex)
    | .joinEffect => ex)
  fiberValue := Val.fiber
  fiberIdValue := fun fiber => Val.nat fiber.value
  fibersValue := Val.fibers
  exitsValue := exitsVal
  voidValue := .unit
  scopeValue := Val.scopeHandle
  closeDoneName := .store .closeParDone
  encodeFiber := id
  stackAnnotations := stackAnnotationsOf
  asyncFiberError := .asyncFiber
  missingScope := .missingService

/-- Generator/loop callbacks see the current construction view before their
inline-exit test. Addressed eager bodies still use their captured point. -/
def interpRAt (root : NativeEff) (completed : List (FiberId × ExitV)) : RInterp :=
  { interpR root with
    iterNext := fun name value => match name with
      | .gen p pc bind => walkR root { p with completed } p.fuel pc
          (if bind then p.env ++ [value] else p.env) []
      | .store (.closeSeq remaining exit captured) => ([], closeSeqStepR remaining exit captured value)
      | .store .closeParDone => ([], closeDone (reasonsOfVal value))
      | _ => ([], .done value)
    loopBody := fun name cursor => match name with
      | .loop p => denoteAt root ({ p with completed }.childWith 0 cursor)
      | _ => .pure (.success cursor)
    finalizerProgram := fun name ex => match name with
      | .fin p => some (denoteAt root ({ p with completed }.childWith 1 (reifyExitVal ex)))
      | _ => (interpR root).finalizerProgram name ex }

end Effect4.Program.Sched
