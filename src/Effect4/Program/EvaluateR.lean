import Effect4.Program.InterpR

/-!
# The local term evaluator (R4, restated by P2)

Packet: `Test/contracts/program-runtime-r.contract.md`; the phase model:
`docs/research/2026-09-06-p0-fable-record.md` §4. This is the second
`FiberEvaluator` instance of the existing command loop, not another loop.
The fiber arms are the shared `FiberAction` helpers of `Machine/Fibers.lean`
(the frame arms under the core's answer, P1b) and the term's own mask and async
arms; the saved-slot walk uses `Machine/Frames.lean:639-676,1459-1498,2302-2368`.
Those files name the rc.112 lines they model. Observation and replay remain
generic and unchanged.

The phases: an operation whose answer is a value computed in its own arm resumes
its continuation directly, with no saved slot; an operation whose answer arrives as
code through the shared loop saves the operation-answer slot `ScopeFrame.answer`,
and delivering into that slot continues the same delivery when its result is a
closing marker or a bare exit, as the frame machine's resume code pops the source
frame in the one counted step that evaluates it. `suspend` is the counted step that
returns code; `sync` answers through the `answered` phase; `gen` and `loop` are the
generator's and the loop's initial entries, whose later iterations the walk runs
inside the body's delivery through the `iter` and `loop` slots.

`RSTEP-FB-FRONTIER`: no compile, choice or unsupported frontier is answered; it
retains its term and consumes only the command budget. The cleanup-end marker
`finishFinalizer` delivers the finalizer's exit through the saved slots exactly as the
frame's `Prim.ofExit` does after a finalizer's restoring continuation: the recorded
`finalizerMask` slot restores the mask on the way out (P3 walk agreement, 2026-09-07; the
earlier refusal of an unmatched marker, `RSTEP-FB-PROTOCOL`, diverged from the frame). The
finite comparisons of the batteries are not the later simulation (`RSTEP-FB-SIMULATION`).
The repaired reference keeps the final pop's saved state through `Cmd.finish`.
The term already retained that state. General code/stack correspondence is
still the P3 obligation, not a consequence of this local correction.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

def GuardKind.hasExitArm (kind : GuardKind) (ex : ExitV) : Bool :=
  match kind, ex with
  | .onSuccess, .failure _ | .onFailure, .success _ => false
  | _, _ => true

/-- The current code for an addressed or synthesized body, through the interpreter. -/
def bodyR (interp : RInterp) : Body → RProgram
  | .at_ p => interp.suspendBody (.body p)
  | .fin fin ex => denoteFin fin ex
  | .raceCleanup race => fiberValR (.cancelRace race) rfl
  | .acquireIn p ctx => acquireInR (interp.suspendBody (.body (p.child 0))) p ctx
  | .release q previous =>
    onExitR (interp.suspendBody (.body q)) fun _ => fiberValR (.setContext previous) rfl

/-- Walk saved slots in the same order as `getCont`: run hooks before testing
the demanded arm, re-read the mask for failure skipping, and visit a cleanup's
pushed mask before the older slots. `some exit` means no slot answered. An
answer slot's continuation is term glue: a closing marker or a bare exit continues
this same delivery. A generator or loop slot runs its continuation here, as the
host's `Iterator` and `While` frames do, and re-pushes itself; a failure passes
both, as frames with only a success arm. -/
def popR (interp : RInterp) (ex : ExitV) : List ScopeFrame → RSaved → RSaved × Option ExitV
  | [], frame => ({ frame with stack := [] }, some ex)
  | slot :: rest, frame =>
    let frame := { frame with stack := rest }
    let failing := match ex with | .failure _ => true | _ => false
    match slot with
    | .restoreMask flag | .finalizerMask flag =>
      let frame := { frame with interruptible := flag }
      match frame.interruptedCause with
      | some cause =>
        if flag && !failing then ({ frame with current := .pure (.failure cause) }, none)
        else popR interp ex rest frame
      | none => popR interp ex rest frame
    | .resume kind next =>
      let flag := frame.interruptible
      let frame := match kind with
        | .onExit false => { frame with interruptible := false }
        | _ => frame
      if kind.hasExitArm ex && !(failing && frame.interruptible && frame.interruptedCause.isSome) then
        let frame := match kind with
          | .onExit _ => { frame with stack := .finalizerMask flag :: frame.stack }
          | _ => frame
        ({ frame with current := next ex }, none)
      else popR interp ex rest frame
    | .answer next =>
      match next ex with
      | .pure ex' => popR interp ex' rest frame
      | .vis (.inr (.unguard ex')) _ => popR interp ex' rest frame
      | code => ({ frame with current := code }, none)
    | .asyncFinalizer name =>
      match ex with
      | .failure cause =>
        let stack := if frame.interruptible then .restoreMask true :: rest else rest
        let code := if cause.hasInterrupts then interp.cancelThenFail name cause else .pure ex
        ({ frame with current := code, stack, interruptible := false }, none)
      | .success _ =>
        -- A passed async hook masks and immediately visits its pushed restore.
        if frame.interruptible && frame.interruptedCause.isSome then
          ({ frame with current := .pure (.failure frame.pendingCause) }, none)
        else popR interp ex rest frame
    | .iter generator =>
      match ex with
      | .failure _ => popR interp ex rest frame
      | .success v =>
        match (interp.iterNext generator v).2 with
        | .done result => ({ frame with current := .pure (.success result) }, none)
        | .halt cause => ({ frame with current := .pure (.failure cause) }, none)
        | .resume code next => ({ frame with current := code, stack := .iter next :: rest }, none)
    | .loop name cursor =>
      match ex with
      | .failure _ => popR interp ex rest frame
      | .success v =>
        let next := interp.loopStep name cursor v
        if interp.loopTest name next then
          ({ frame with current := interp.loopBody name next, stack := .loop name next :: rest }, none)
        else ({ frame with current := .pure (.success (interp.loopDone name)) }, none)

def outcomeOfWalk : Option ExitV → Outcome EffName EffThunk Val Err Defect FiberId Ann
  | none => .continue_
  | some exit => .finished exit

/-- Deferred interruption is checked before a success delivery touches any slot. -/
def deliverR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) : RIter :=
  let deferred := match ex with | .success _ => f.frame.deferredInterrupt | _ => false
  if deferred then
    ⟨m, { f with frame := { f.frame with
      current := .pure (.failure f.frame.pendingCause)
      deferredInterrupt := false } }, yielding, .continue_, []⟩
  else
    let (frame, done) := popR interp ex f.frame.stack { f.frame with deferredInterrupt := false }
    ⟨m, { f with frame }, yielding, outcomeOfWalk done, []⟩

def pushR (f : RFiber) (slot : ScopeFrame) : RFiber :=
  { f with frame := { f.frame with stack := slot :: f.frame.stack } }

def saveR (f : RFiber) (kind : GuardKind) (next : ExitV → RProgram) : RFiber :=
  pushR f (.resume kind next)

/-- Save the continuation of an operation whose answer arrives as code. -/
def saveAnswerR (f : RFiber) (next : ExitV → RProgram) : RFiber := pushR f (.answer next)

def answerR (f : RFiber) (code : RProgram) : RFiber :=
  { f with frame := { f.frame with current := code } }

def answerValueR (f : RFiber) (value : Val) : RFiber := answerR f (.pure (.success value))

/-- How the term installs a value answer: the operation's continuation applied to it. -/
def answerWith (next : Val → RProgram) :
    FiberAction.Answer EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram RSaved :=
  fun f v => answerR f (next v)

/-- One fiber operation. A value computed here resumes the continuation directly; an
answer that arrives as code saves the answer slot first. -/
def evaluateFiberR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : FiberOp) (next : op.answer → RProgram) : RIter :=
  match op with
  | .construction =>
    -- `evaluateR` removes this head before dispatching a counted operation.
    ⟨m, answerR f (prepareR m.completedExits (next m.completedExits)), yielding, .continue_, []⟩
  | .scoped body =>
    -- `internal/effect.ts:3938-3948`: make/install in the WithFiber, then return
    -- OnExit around the already constructed body; do not refresh its point.
    let scope := m.state.nextName
    let state := { m.state with
      scopes := m.state.scopes.make scope .sequential, nextName := scope + 1 }
    let previous := f.context
    let context := { previous with ambientScope := some scope }
    let f := { f with
      context := context
      maxOpsBeforeYield := context.maxOpsBeforeYield
      preventYield := context.preventYield }
    let code := (guardR (.onExit false) (bodyR interp (.at_ body))).bind fun ex =>
      .vis (.inr (.scopeExit previous scope ex)) Effects.Program.pure
    ⟨{ m with state }, answerR (saveAnswerR f next) code, yielding, .continue_, []⟩
  | .scopeExit _ _ _ =>
    -- A generated callback is consumed during its preceding delivery. A raw
    -- marker arriving as a counted operation is outside that protocol.
    ⟨m, answerR f (.pure badShapeExit), yielding, .continue_, []⟩
  | .guard_ kind =>
    ⟨m, answerR (saveR f kind fun ex => next (some ex)) (next none), yielding, .continue_, []⟩
  | .unguard ex => deliverR interp m f yielding ex
  -- the cleanup-end marker delivers the finalizer's exit through the saved slots: the
  -- `finalizerMask` slot it meets restores the mask, as the frame's restoring
  -- `setInterruptible` does under `Prim.ofExit` (`internal/effect.ts:4021-4029`)
  | .finishFinalizer ex => deliverR interp m f yielding ex
  | .frontier _ _ => ⟨m, f, yielding, .continue_, []⟩
  | .suspend _ => ⟨m, answerR f (next .unit), yielding, .continue_, []⟩
  -- the counted suspend before a capture's release (V1), as `suspend` and `closeWalk`
  | .foreignRelease _ _ => ⟨m, answerR f (next .unit), yielding, .continue_, []⟩
  | .sync v => ⟨m, answerR f (next v), yielding, .answered, []⟩
  | .gen p =>
    let f := saveAnswerR f next
    match (interp.iterNext (.gen p [] false) .unit).2 with
    | .done v => ⟨m, answerR f (.pure (.success v)), yielding, .continue_, []⟩
    | .halt c => ⟨m, answerR f (.pure (.failure c)), yielding, .continue_, []⟩
    | .resume code cont => ⟨m, answerR (pushR f (.iter cont)) code, yielding, .continue_, []⟩
  | .loop p cursor =>
    let f := saveAnswerR f next
    if interp.loopTest (.loop p) cursor then
      ⟨m, answerR (pushR f (.loop (.loop p) cursor)) (interp.loopBody (.loop p) cursor),
        yielding, .continue_, []⟩
    else ⟨m, answerR f (.pure (.success (interp.loopDone (.loop p)))), yielding, .continue_, []⟩
  | .yieldNow priority => FiberAction.yieldNow interp m (saveAnswerR f (seqR next)) yielding priority
  | .async register _request =>
    let f := saveAnswerR f next
    let token := m.nextToken
    let (state, immediate) := interp.registerAsync register f.id token m.state
    let m := { m with state, nextToken := token + 1 }
    match immediate with
    | some code => ⟨m, answerR f code, yielding, .continue_, [.drainDue]⟩
    | none =>
      let cancel := match register with
        | .registerAwait cell => some (EffName.cancelAwait cell)
        | .store (.registerAwait cell) => some (EffName.store (.cancelAwait cell))
        | _ => none
      let f := match cancel with
        | none => f
        | some name => pushR f (.asyncFinalizer (interp.cancelName name f.id token))
      let f := f.park ⟨token, none, [], [], .void, false⟩
      ⟨m.emit [.parkedOn f.id token], f, yielding, .parked, []⟩
  | .await target mode =>
    let f := match mode with
      | .joinEffect => saveAnswerR f next
      | .awaitValue => saveAnswerR f (seqR next)
    FiberAction.join interp m f yielding target mode
  | .fork child options =>
    FiberAction.fork interp m f yielding (bodyR interp child) options (answerWith next)
  | .forkIn child options scope =>
    FiberAction.forkIn interp m f yielding (bodyR interp (.at_ child)) options scope
      (answerWith next)
  | .forkScoped child options =>
    FiberAction.forkScoped interp m f yielding (bodyR interp (.at_ child)) options
      (fun f v => answerR f (next (.success v)))
  | .runIn target scope =>
    FiberAction.runIn interp m f yielding target scope (answerWith next)
  | .interrupt target =>
    FiberAction.interrupt interp m (saveAnswerR f (seqR next)) yielding target
  | .interruptAs target who =>
    FiberAction.interruptAs interp m (saveAnswerR f (seqR next)) yielding target who
  | .interruptScoped target =>
    if target = f.id then ⟨m, answerR f (next interp.voidValue), yielding, .continue_, []⟩
    else FiberAction.interruptScoped interp m (saveAnswerR f (seqR next)) yielding target
  | .interruptAll targets who =>
    FiberAction.interruptAll interp m (saveAnswerR f (seqR next)) yielding targets who
  | .awaitAll targets => FiberAction.awaitAll interp m (saveAnswerR f (seqR next)) yielding targets false
  | .awaitAllFailFast targets =>
    FiberAction.awaitAll interp m (saveAnswerR f (seqR next)) yielding targets true
  | .snapshotChildren => FiberAction.snapshotChildren interp m f yielding (answerWith next)
  | .awaitNewChildren snapshot =>
    FiberAction.awaitNewChildren interp m (saveAnswerR f (seqR next)) yielding snapshot
  | .raceAll entrants =>
    FiberAction.raceAll interp m (saveAnswerR f next) yielding
      (entrants.map fun p => bodyR interp (.at_ p))
  | .raceRegister race => registerRace m f yielding race
  | .mask flag body =>
    let f := saveAnswerR f next
    let old := f.frame.interruptible
    let stack := if old = flag then f.frame.stack else .restoreMask old :: f.frame.stack
    let frame := { f.frame with interruptible := flag, stack }
    let code := if flag && !old && frame.interruptedCause.isSome then
      .pure (.failure frame.pendingCause) else bodyR interp body
    ⟨m, answerR { f with frame } code, yielding, .continue_, []⟩
  | .setContext context => FiberAction.setContext interp m f yielding context (answerWith next)
  | .getContext => FiberAction.getContext interp m f yielding (answerWith next)
  | .getId => FiberAction.getId interp m f yielding (answerWith next)
  | .closeScope scope ex => FiberAction.closeScope interp m (saveAnswerR f next) yielding scope ex
  | .refuse cause => FiberAction.refuse m f yielding cause
  | .dropObservers token => FiberAction.dropObservers interp m f yielding token (answerWith next)
  | .cancelRace raceId => FiberAction.cancelRace interp m (saveAnswerR f (seqR next)) yielding raceId
  -- §20: the `Scope` service read, and the two counted steps of a multi-finalizer close
  | .ambientScope => FiberAction.ambientScope interp m f yielding (answerWith next)
  | .closeWalk _ _ _ => ⟨m, answerR f (next .unit), yielding, .continue_, []⟩
  | .closeIter .sequential order ex =>
    -- `Iterator[evaluate]` over the sequential generator, like `.gen`
    let f := saveAnswerR f next
    match (interp.iterNext (.store (.closeSeq order ex [])) .unit).2 with
    | .done v => ⟨m, answerR f (.pure (.success v)), yielding, .continue_, []⟩
    | .halt c => ⟨m, answerR f (.pure (.failure c)), yielding, .continue_, []⟩
    | .resume code cont => ⟨m, answerR (pushR f (.iter cont)) code, yielding, .continue_, []⟩
  | .closeIter .parallel order ex =>
    FiberAction.closePar interp m (saveAnswerR f next) yielding (order.map fun fin => denoteFin fin ex)

/-- Store deliveries retain the shared loop's `answered`/`deliver` split, so
a completing Deferred's synchronous resumes run before its continuation; the
operation's continuation is installed directly, with no saved slot. -/
def evaluateRawR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) : RIter :=
  match f.frame.current with
  | .pure ex => deliverR interp m f yielding ex
  | .vis (.inr op) next => evaluateFiberR interp m f yielding op next
  | .vis (.inl op) next =>
    match syncOpStep op m.state with
    | some (state, value) => ⟨{ m with state }, answerR f (next value), yielding, .answered, [.drainDue]⟩
    | none => ⟨m, answerR f (next .unit), yielding, .answered, []⟩

/-- The scoped exit callback restores context and closes its scope before the
next loop checkpoint (`internal/effect.ts:3944-3947`). This stateful glue is
outside pure construction preparation and uses the mask retained by the pop. -/
def prepareScopedExitR (it : RIter) : RIter :=
  match it.fiber.frame.current with
  | .vis (.inr (.scopeExit previous scope ex)) next =>
    let f := { it.fiber with
      context := previous
      maxOpsBeforeYield := previous.maxOpsBeforeYield
      preventYield := previous.preventYield }
    match closeScopeUnsafeR scope ex f.frame.interruptible it.machine.state with
    -- an unknown scope halts the machine; the callback's exit stays the fiber's current, as
    -- the frame keeps the exit it was delivering
    | none => { it with fiber := answerR f (.pure ex), outcome := .stuck (.unknownScope scope) }
    | some (state, program) =>
      let code := match program with
        | none => .vis (.inr (.finishFinalizer ex)) next
        | some code => (finalizerR ex code).bind next
      { it with machine := { it.machine with state }, fiber := answerR f code }
  | _ => it

/-- A store answer owes delivery after its nested resumes. Every other result
finishes its callback and construction glue before another loop can yield. -/
def prepareIterR (it : RIter) : RIter :=
  match it.outcome with
  | .answered | .commands => it
  | _ => prepareScopedExitR
      { it with fiber := answerR it.fiber (prepareR it.machine.completedExits it.fiber.frame.current) }

/-- Resolve construction glue without charging a host operation. Source
callbacks returning code capture this view before the next run-loop checkpoint. -/
def evaluateR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) : RIter :=
  prepareIterR (evaluateRawR interp m
    (answerR f (prepareR m.completedExits f.frame.current)) yielding)

@[reducible] instance termEvaluator :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit where
  evaluate := evaluateR

/-- The native term evaluator shares the frame evaluator's construction view. -/
@[reducible] def termEvaluatorFor (root : NativeEff) :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit where
  evaluate := fun _ m f yielding => evaluateR (interpRAt root m.completedExits) m f yielding

end Effect4.Program.Sched
