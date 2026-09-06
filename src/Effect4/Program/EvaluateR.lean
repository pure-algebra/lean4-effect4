import Effect4.Program.InterpR

/-!
# The local term evaluator (R4)

Packet: `Test/contracts/program-runtime-r.contract.md`. This is the second
`FiberEvaluator` instance of the existing command loop, not another loop.
The fiber arms transcribe `Machine/Fibers.lean:844-1103`; the saved-slot walk
uses `Machine/Frames.lean:639-676,1459-1498,2302-2368`. Those files name the
rc.112 lines they model. Observation and replay remain generic and unchanged.

`RSTEP-FB-FRONTIER`: no source or unfolding frontier is answered; it retains
its term and consumes only the command budget. `RSTEP-FB-PROTOCOL` names an
unmatched cleanup-end marker, which generated `onExitR` never emits. R3/R4
supplies executable clauses and finite comparisons, not the later simulation
or equality of automatic yield counts (`RSTEP-FB-SIMULATION`).
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
pushed mask before the older slots. `some exit` means no slot answered. -/
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

/-- Deferred interruption is checked before a success delivery touches any slot. -/
def deliverR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) : RIter :=
  let deferred := match ex with | .success _ => f.frame.deferredInterrupt | _ => false
  if deferred then
    ⟨m, { f with frame := { f.frame with
      current := .pure (.failure f.frame.pendingCause)
      deferredInterrupt := false } }, yielding, .continue_, []⟩
  else
    let (frame, done) := popR interp ex f.frame.stack { f.frame with deferredInterrupt := false }
    ⟨m, { f with frame }, yielding, match done with
      | none => .continue_ | some exit => .finished exit, []⟩

def saveR (f : RFiber) (kind : GuardKind) (next : ExitV → RProgram) : RFiber :=
  { f with frame := { f.frame with stack := .resume kind next :: f.frame.stack } }

def saveValueR (f : RFiber) (next : Val → RProgram) : RFiber := saveR f .onSuccess (seqR next)

def answerR (f : RFiber) (code : RProgram) : RFiber :=
  { f with frame := { f.frame with current := code } }

def answerValueR (f : RFiber) (value : Val) : RFiber := answerR f (.pure (.success value))

def outcomeR (m : RState) (parked : Bool) : Outcome EffName EffThunk Val Err Defect FiberId Ann :=
  match m.stuck with | some why => .stuck why | none => if parked then .parked else .continue_

/-- Record interruption with the caller's annotations, then await the target. -/
def interruptJoinR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (target : FiberId) : RIter :=
  match m.fiber? target with
  | none => ⟨m, f, yielding, .stuck (.unknownFiber target), []⟩
  | some t =>
    let (t, applyNow) := interruptRecord interp (some f.id) (interp.stackAnnotations f.id) t
    let m := (m.update t).emit [.interruptRecorded (some f.id) target]
    let nested := if applyNow then [Cmd.evaluate target] else []
    let (m, f, parked) := countdownPark interp m f [target] .void
    ⟨m, f, yielding, outcomeR m parked, nested⟩

/-- `scopeOpen`/`scopeProvide`/`scopeBody` as terms: restore the context before
closing the scope; both cleanups use the normal `onExitR` mask. -/
def scopedR (interp : RInterp) (body : Point) (scope : Nat) : RProgram :=
  onExitR
    ((guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun
      | .context previous =>
        (guardR .onSuccess (fiberValR (.setContext { previous with ambientScope := some scope }) rfl)).bind
          (seqR fun _ => onExitR (interp.suspendBody (.body body))
            (fun _ => fiberValR (.setContext previous) rfl))
      | _ => .pure badShapeExit))
    (fun ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure)

/-- One fiber operation. Each suspension first saves its answer continuation;
the generic loop can then resume it with ordinary term code. -/
def evaluateFiberR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : FiberOp) (next : op.answer → RProgram) : RIter :=
  match op with
  | .guard_ kind =>
    let f := saveR f kind (fun ex => next (some ex))
    ⟨m, answerR f (next none), yielding, .continue_, []⟩
  | .unguard ex => deliverR interp m f yielding ex
  | .finishFinalizer ex =>
    match f.frame.stack with
    | .finalizerMask flag :: rest =>
      let frame := { f.frame with stack := rest, interruptible := flag }
      let code := match frame.interruptedCause, ex with
        | some cause, .success _ => if flag then .pure (.failure cause) else next ex
        | _, _ => next ex
      ⟨m, answerR { f with frame } code, yielding, .continue_, []⟩
    | _ => ⟨m, answerR f (.pure badShapeExit), yielding, .continue_, []⟩
  | .frontier _ _ | .acquireRelease _ _ => ⟨m, f, yielding, .continue_, []⟩
  | .yieldNow priority =>
    let f := saveValueR f next
    let token := m.nextToken
    let m := { m with nextToken := token + 1 }
    let f := { answerValueR f interp.voidValue with
      dispatcher := f.dispatcher.enqueue priority (.resume f.id token (.pure (.success interp.voidValue))) }
    let f := f.park ⟨token, none, [], [], .void, false⟩
    ⟨(m.arm f.id).emit [.parkedOn f.id token], f, yielding, .parked, []⟩
  | .async register _request =>
    let f := saveR f .all next
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
        | some name => { f with frame :=
            { f.frame with stack := .asyncFinalizer (interp.cancelName name f.id token) :: f.frame.stack } }
      let f := f.park ⟨token, none, [], [], .void, false⟩
      ⟨m.emit [.parkedOn f.id token], f, yielding, .parked, []⟩
  | .await target mode =>
    let f := match mode with
      | .joinEffect => saveR f .all next
      | .awaitValue => saveValueR f next
    match m.fiber? target with
    | none => ⟨m, f, yielding, .stuck (.unknownFiber target), []⟩
    | some t => match t.exit with
      | some ex => ⟨m, answerR f (interp.exitValue ex mode), yielding, .continue_, []⟩
      | none =>
        let token := m.nextToken
        let m := { m with nextToken := token + 1 }
        let m := m.update { t with observers := t.observers ++ [.resumeAwait f.id token mode] }
        let name := interp.cancelName interp.parkCancelName f.id token
        let f := { f with frame := { f.frame with stack := .asyncFinalizer name :: f.frame.stack } }
        let f := f.park ⟨token, some target, [], [], .void, false⟩
        ⟨m.emit [.parkedOn f.id token], f, yielding, .parked, []⟩
  | .fork child options =>
    let f := saveValueR f next
    let m := if options.daemon then m else { m with middlewareInstalled := true }
    let (m, f, child) := spawn interp m f (bodyR interp child) options
    let (m, f, nested) := start m f child options.startImmediately
    ⟨m, answerValueR f (interp.fiberValue child), yielding, .continue_, nested⟩
  | .forkIn child options scope key =>
    let f := saveValueR f next
    let (m, f, child) := spawn interp m f (bodyR interp (.at_ child)) { options with daemon := true }
    let (m, f, nested) := start m f child options.startImmediately
    ⟨m, answerValueR f (interp.fiberValue child), yielding, .continue_,
      nested ++ [.link .forkIn scope key child (some f.id) (interp.stackAnnotations f.id)]⟩
  | .forkScoped child options key =>
    let f := saveR f .all next
    match interp.ambientScope f.context with
    | none => ⟨m, answerR f (.pure (.failure (Cause.die interp.missingScope))), yielding, .continue_, []⟩
    | some scope =>
      let (m, f, child) := spawn interp m f (bodyR interp (.at_ child)) { options with daemon := true }
      let (m, f, nested) := start m f child options.startImmediately
      ⟨m, answerValueR f (interp.fiberValue child), yielding, .continue_,
        nested ++ [.link .forkIn scope key child (some f.id) (interp.stackAnnotations f.id)]⟩
  | .runIn target scope key =>
    let (m, nested) := linkScope interp m .fiberRunIn scope key target (some target) ReasonAnnotations.empty
    ⟨m, answerValueR (saveValueR f next) interp.voidValue, yielding, outcomeR m false, nested⟩
  | .interrupt target => interruptJoinR interp m (saveValueR f next) yielding target
  | .interruptScoped target =>
    if target = f.id then
      ⟨m, answerValueR (saveValueR f next) interp.voidValue, yielding, .continue_, []⟩
    else interruptJoinR interp m (saveValueR f next) yielding target
  | .interruptAll targets who =>
    let (m, nested) := interruptEach interp (who.getD f.id) (interp.stackAnnotations f.id) targets (m, [])
    let (m, f, parked) := countdownPark interp m (saveValueR f next) targets .void
    ⟨m, f, yielding, outcomeR m parked, nested⟩
  | .awaitAll targets | .awaitAllFailFast targets =>
    let failFast := match op with | .awaitAllFailFast _ => true | _ => false
    let (m, f, parked) := countdownPark interp m (saveValueR f next) targets .exitsValue failFast
    ⟨m, f, yielding, outcomeR m parked, []⟩
  | .snapshotChildren =>
    ⟨m, answerValueR (saveValueR f next) (interp.fibersValue f.children), yielding, .continue_, []⟩
  | .awaitNewChildren snapshot =>
    let targets := f.children.filter fun child => !(snapshot.contains child)
    let (m, f, parked) := countdownPark interp m (saveValueR f next) targets .void
    ⟨m, f, yielding, outcomeR m parked, []⟩
  | .raceAll entrants =>
    let f := saveR f .all next
    let raceId := m.nextRace
    let token := m.nextToken
    let m := { m with nextRace := raceId + 1, nextToken := token + 1 }
    let race : Race EffName EffThunk Val Err Defect FiberId Ann RProgram :=
      ⟨raceId, f.id, token, { Supervision.RaceAllState.initial [] with remaining := entrants.length },
        false, entrants.map fun p => bodyR interp (.at_ p)⟩
    let m := { m with races := m.races ++ [race] }
    let m := m.emit [.raceStarted raceId f.id entrants.length]
    let name := interp.cancelName (interp.raceCancelName raceId) f.id token
    let f := { f with frame := { f.frame with stack := .asyncFinalizer name :: f.frame.stack } }
    let f := f.park ⟨token, none, [], [], .void, false⟩
    ⟨m.emit [.parkedOn f.id token], f, yielding, .parked, [.launch raceId]⟩
  | .mask flag body =>
    let f := saveR f .all next
    let old := f.frame.interruptible
    let stack := if old = flag then f.frame.stack else .restoreMask old :: f.frame.stack
    let frame := { f.frame with interruptible := flag, stack }
    let code := if flag && !old && frame.interruptedCause.isSome then
      .pure (.failure frame.pendingCause) else bodyR interp body
    ⟨m, answerR { f with frame } code, yielding, .continue_, []⟩
  | .scoped body scope =>
    ⟨m, answerR (saveR f .all next) (scopedR interp body scope), yielding, .continue_, []⟩
  | .setContext context =>
    let (maxOpsBeforeYield, preventYield) := interp.budgetOf context
    let f := { saveValueR f next with context, maxOpsBeforeYield, preventYield }
    ⟨m.emit [.contextSet f.id context], answerValueR f interp.voidValue, yielding, .continue_, []⟩
  | .getContext =>
    ⟨m, answerValueR (saveValueR f next) (interp.contextValue f.context), yielding, .continue_, []⟩
  | .getId =>
    ⟨m, answerValueR (saveValueR f next) (interp.fiberValue f.id), yielding, .continue_, []⟩
  | .closeScope scope ex =>
    match interp.closeScope scope ex f.frame.interruptible f.id m.state with
    | none => ⟨m, f, yielding, .stuck (.unknownScope scope), []⟩
    | some (state, code) =>
      ⟨{ m with state }, answerR (saveR f .all next) code, yielding, .continue_, []⟩
  | .refuse cause => ⟨m, answerR f (.pure (.failure cause)), yielding, .continue_, []⟩
  | .dropObservers token =>
    let m := { m with fibers := m.fibers.map fun g =>
      { g with observers := g.observers.filter fun
        | .resumeAwait _ t _ | .countdown _ t => t ≠ token
        | _ => true } }
    ⟨m, answerValueR (saveValueR f next) interp.voidValue, yielding, .continue_, []⟩
  | .cancelRace raceId =>
    let f := saveValueR f next
    match m.race? raceId with
    | none => ⟨m, answerValueR f interp.voidValue, yielding, .continue_, []⟩
    | some race =>
      let (m, nested) := interruptEach interp f.id (interp.stackAnnotations f.id) race.state.live (m, [])
      let (m, f, parked) := countdownPark interp m f race.state.live .void
      ⟨m, f, yielding, outcomeR m parked, nested⟩

/-- Store deliveries retain the shared loop's `answered`/`deliver` split, so
a completing Deferred's synchronous resumes run before its continuation. -/
def evaluateR (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) : RIter :=
  match f.frame.current with
  | .pure ex => deliverR interp m f yielding ex
  | .vis (.inr op) next => evaluateFiberR interp m f yielding op next
  | .vis (.inl op) next =>
    let f := saveValueR f next
    match syncOpStep op m.state with
    | some (state, value) =>
      ⟨{ m with state }, answerValueR f value, yielding, .answered, [.drainDue]⟩
    | none => ⟨m, answerValueR f .unit, yielding, .answered, []⟩

@[reducible] instance termEvaluator :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit where
  evaluate := evaluateR

end Effect4.Program.Sched
