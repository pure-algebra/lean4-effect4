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
retains its term and consumes only the command budget. `RSTEP-FB-PROTOCOL` names an
unmatched cleanup-end marker, which generated `onExitR` never emits. The finite
comparisons of the batteries are not the later simulation (`RSTEP-FB-SIMULATION`).
`RSTEP-FB-TERMINAL-MASK`: the reference `finishFrame` discards a final pop's
saved state; this evaluator retains it. The exited fiber's mask can differ.
The observation excludes that bit, and comparisons check it on live fibers.
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
  | .interruptFibers live => fiberValR (.interruptAll live none) rfl

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

/-- After a cleanup's mask is restored, its continuation is delivered like an adapter's. -/
def finishWith (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (code : RProgram) : RIter :=
  match code with
  | .pure ex' =>
    let (frame, done) := popR interp ex' f.frame.stack f.frame
    ⟨m, { f with frame }, yielding, outcomeOfWalk done, []⟩
  | .vis (.inr (.unguard ex')) _ =>
    let (frame, done) := popR interp ex' f.frame.stack f.frame
    ⟨m, { f with frame }, yielding, outcomeOfWalk done, []⟩
  | code => ⟨m, answerR f code, yielding, .continue_, []⟩

/-- One fiber operation. A value computed here resumes the continuation directly; an
answer that arrives as code saves the answer slot first. -/
def evaluateFiberR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : FiberOp) (next : op.answer → RProgram) : RIter :=
  match op with
  | .guard_ kind =>
    ⟨m, answerR (saveR f kind fun ex => next (some ex)) (next none), yielding, .continue_, []⟩
  | .unguard ex => deliverR interp m f yielding ex
  | .finishFinalizer ex =>
    match f.frame.stack with
    | .finalizerMask flag :: rest =>
      let f := { f with frame := { f.frame with stack := rest, interruptible := flag } }
      match f.frame.interruptedCause, ex with
      | some cause, .success _ =>
        if flag then ⟨m, answerR f (.pure (.failure cause)), yielding, .continue_, []⟩
        else finishWith interp m f yielding (next ex)
      | _, _ => finishWith interp m f yielding (next ex)
    | _ => ⟨m, answerR f (.pure badShapeExit), yielding, .continue_, []⟩
  | .frontier _ _ | .acquireRelease _ _ => ⟨m, f, yielding, .continue_, []⟩
  | .suspend _ => ⟨m, answerR f (next .unit), yielding, .continue_, []⟩
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
  | .forkIn child options scope key =>
    FiberAction.forkIn interp m f yielding (bodyR interp (.at_ child)) options scope key
      (answerWith next)
  | .forkScoped child options key =>
    FiberAction.forkScoped interp m f yielding (bodyR interp (.at_ child)) options key
      (fun f v => answerR f (next (.success v)))
  | .runIn target scope key =>
    FiberAction.runIn interp m f yielding target scope key (answerWith next)
  | .interrupt target =>
    FiberAction.interruptThenJoin interp m (saveAnswerR f (seqR next)) yielding target (some f.id)
  | .interruptScoped target =>
    if target = f.id then ⟨m, answerR f (next interp.voidValue), yielding, .continue_, []⟩
    else FiberAction.interruptThenJoin interp m (saveAnswerR f (seqR next)) yielding target (some f.id)
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

/-- Store deliveries retain the shared loop's `answered`/`deliver` split, so
a completing Deferred's synchronous resumes run before its continuation; the
operation's continuation is installed directly, with no saved slot. -/
def evaluateR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) : RIter :=
  match f.frame.current with
  | .pure ex => deliverR interp m f yielding ex
  | .vis (.inr op) next => evaluateFiberR interp m f yielding op next
  | .vis (.inl op) next =>
    match syncOpStep op m.state with
    | some (state, value) => ⟨{ m with state }, answerR f (next value), yielding, .answered, [.drainDue]⟩
    | none => ⟨m, answerR f (next .unit), yielding, .answered, []⟩

@[reducible] instance termEvaluator :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit where
  evaluate := evaluateR

end Effect4.Program.Sched
