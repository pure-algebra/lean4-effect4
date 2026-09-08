import Effect4.Machine.Approximation
import Effects.Algebra.Program

/-!
# The shared scheduler at an algebra instance

D1: these finite runs use the actual `Effects.Program` carrier, whose
continuations have no decidable equality. The fixture has store and yield
operations. It exercises the production command loop,
resume guard, yield dispatcher and interrupt path. It is not `evaluateR` and
does not claim a relation to compiled Eff or the host (`CORE-FB-SIMULATION`).
-/

set_option autoImplicit false

namespace Test.Runtime.SchedulerCoreContract

open Effect4 Effect4.Machine

abbrev Sig : Effects.Signature.{0, 0} := ⟨Bool, fun _ => Nat⟩
abbrev X := Exit Nat Unit Unit FiberId Unit
abbrev Code := Effects.Program Sig X

structure Saved where
  current : Code
  interruptible : Bool
  interruptedCause : Option (Cause Unit Unit FiberId Unit)
  deferredInterrupt : Bool
  finalizers : List Unit
  answers : List (Nat → Code)

instance algebraCore : FiberCore Unit Nat Unit Unit FiberId Unit Code Saved where
  current := Saved.current
  answerWith := fun f code => { f with current := code }
  start := fun code flag => ⟨code, flag, none, false, [], []⟩
  interruptible := Saved.interruptible
  interruptedCause := Saved.interruptedCause
  deferredInterrupt := Saved.deferredInterrupt
  recordCause := fun f cause => { f with interruptedCause := some cause }
  setDeferred := fun f flag => { f with deferredInterrupt := flag }
  pendingFailure := fun f =>
    { f with
      current := .pure (.failure (f.interruptedCause.getD Cause.empty))
      deferredInterrupt := false }
  pushAsyncFinalizer := fun name f => { f with finalizers := name :: f.finalizers }
  -- the algebra fixture has no generator frames (§20): the push is the identity
  pushIterator := fun _ _ f => f
  clearStack := fun f => { f with finalizers := [], answers := [] }
  success := fun value => .pure (.success value)
  failure := fun cause => .pure (.failure cause)
  onSuccess := fun code _ => code
  yieldBefore := fun code => .vis true (fun _ => code)

abbrev M := RunMachine Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code Saved Unit
abbrev F := RunFiber Unit Unit Nat Unit Unit FiberId Unit Unit Code Saved
abbrev I := RunInterp Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code
abbrev D := RunDecision Unit Unit Nat Unit Unit FiberId Unit
abbrev C := Cmd Unit Unit Nat Unit Unit FiberId Unit Code

def readNext : Code := .vis false (fun n => .pure (.success n))

def interp : I where
  contA := fun _ v => .pure (.success v)
  contE := fun _ c => .pure (.failure c)
  syncValue := fun _ => 0
  suspendBody := fun _ => readNext
  iterNext := fun _ v => ([], .done v)
  loopTest := fun _ _ => false
  loopBody := fun _ v => .pure (.success v)
  loopStep := fun _ _ v => v
  loopDone := fun _ => 0
  finalizerExit := fun _ _ => Exit.void
  reifyExit := fun _ => 0
  cancelThenFail := fun _ c => .pure (.failure c)
  notImplemented := ()
  parkOf := fun _ => none
  parkCode := fun _ => readNext
  interruptCode := fun _ => readNext
  interruptAsCode := fun _ _ => readNext
  interruptAllCode := fun _ => readNext
  withFiberOf := fun _ => none
  syncState := fun _ _ => none
  registerAsync := fun _ _ _ s => (s, none)
  answerCode := fun
    | .ofExit exit => .pure exit
    | .ofRefGet _ => readNext
  dueResumes := fun s => ([], s)
  wakeList := fun _ _ s => s
  cancelName := fun _ _ _ => ()
  abortName := ()
  parkCancelName := ()
  raceCancelName := fun _ => ()
  raceSettle := fun _ _ exit => .pure exit
  finalizerProgram := fun _ _ => none
  restoreName := fun _ => ()
  mergeName := fun _ => ()
  scopeStatus := fun _ _ => none
  scopeLinkFiber := fun _ _ _ _ => none
  dropFinalizer := fun _ _ _ => none
  closeScope := fun _ _ _ _ _ => none
  ambientScope := fun _ => none
  budgetOf := fun _ => (2048, false)
  emptyContext := ()
  contextValue := fun _ => 0
  exitValue := fun exit _ => .pure exit
  fiberValue := FiberId.value
  fiberIdValue := FiberId.value
  fibersValue := List.length
  exitsValue := List.length
  voidValue := 0
  scopeValue := fun _ => 0
  closeDoneName := ()
  encodeFiber := id
  stackAnnotations := fun _ => ReasonAnnotations.empty
  asyncFiberError := ()
  missingScope := ()

instance algebraEvaluator : FiberEvaluator Unit Unit Nat Unit Unit FiberId Unit Unit Nat
    Code Saved Unit where
  evaluate := fun i m f yielding =>
    match f.frame.current with
    | .pure (.success value) =>
      match f.frame.answers with
      | [] => ⟨m, f, yielding, .finished (.success value), []⟩
      | next :: rest =>
        ⟨m, { f with frame := { f.frame with current := next value, answers := rest } },
          yielding, .continue_, []⟩
    | .pure (.failure cause) => ⟨m, f, yielding, .finished (.failure cause), []⟩
    | .vis false next =>
      ⟨{ m with state := m.state + 1 }, { f with frame := { f.frame with current := next m.state } },
        yielding, .continue_, []⟩
    | .vis true next =>
      FiberAction.yieldNow i m
        { f with frame := { f.frame with answers := next :: f.frame.answers } } yielding 0

def initial : M :=
  { (RunMachine.empty 7 : M) with
    fibers := [RunFiber.make ⟨0⟩ readNext true (2048, false) ()], nextId := 1 }

def exitOf (m : M) : Option X := (m.fiber? ⟨0⟩).bind RunFiber.exit
def cmds : List C := [.evaluate ⟨0⟩, .drainDue]
def tape : List D := [.evaluate ⟨0⟩, .flush]

#guard !(settled (driveState interp 0 initial cmds))
#guard (driveState interp 2 initial cmds).1.state = 8
#guard !(settled (driveState interp 2 initial cmds))
#guard exitOf (driveState interp 20 initial cmds).1 = some (.success 7)
#guard settled (driveState interp 20 initial cmds)
#guard Suffices interp 20 tape initial
#guard (replayEval interp 1 tape initial).terminal = false
#guard (replayEval interp 20 tape initial).terminal

-- The existing splitting and tape-stability laws apply to this code carrier.
theorem splitFuel (a b : Nat) :
    driveState interp (a + b) initial cmds =
      driveState interp b (driveState interp a initial cmds).1 (driveState interp a initial cmds).2 :=
  driveState_add interp a b initial cmds

theorem stableTape (k : Nat) :
    replayEval interp (20 + k) tape initial = replayEval interp 20 tape initial :=
  replay_stable interp 20 tape initial (by decide) k

-- This algebra supplies its own yield code through the core. Its adapter retains
-- the continuation while the shared dispatcher resumes with a success answer.
def yielding : M := initial.modify ⟨0⟩ fun f => { f with yieldOverride := some true }
#guard exitOf (replayEval interp 20 [.evaluate ⟨0⟩] yielding).machine = none
#guard (replayEval interp 20 [.evaluate ⟨0⟩] yielding).machine.armed = [⟨0⟩]
#guard exitOf (replayEval interp 20 tape yielding).machine = some (.success 7)
#guard (replayEval interp 20 tape yielding).machine.armed.isEmpty

-- External Completion data and the existing guard are used without a tape translation.
def parked : M := initial.modify ⟨0⟩ fun f => { f with parked := .withGuard 3 }
def answer (token : Nat) : D := .answerAsync ⟨0⟩ token (.ofExit (.success 42))
#guard exitOf (replayEval interp 20 [answer 3] parked).machine = some (.success 42)
#guard exitOf (replayEval interp 20 [answer 4] parked).machine = none
#guard exitOf (replayEval interp 20 [answer 3, answer 3] parked).machine = some (.success 42)

-- The shared interrupt path builds failure code through the chosen core.
#guard exitOf (replayEval interp 20 [.interruptFrom (some ⟨1⟩) ReasonAnnotations.empty ⟨0⟩] initial).machine =
  some (.failure (Cause.interrupt (some ⟨1⟩)))

-- CORE-FB-TRACE: an unconstrained evaluator can erase already recorded events.
@[instance_reducible] def erasesTrace : FiberEvaluator Unit Unit Nat Unit Unit FiberId Unit Unit Nat Code Saved Unit where
  evaluate := fun i m f y =>
    let it := algebraEvaluator.evaluate i m f y
    { it with machine := { it.machine with trace := [] } }

#guard (drive (evaluator := erasesTrace) interp 1 initial cmds).trace.length = 1
#guard (drive (evaluator := erasesTrace) interp 2 initial cmds).trace.length = 0

/-! ## The wake protocol's fixtures (the scheduler surface, 2026-09-08)

The fixtures the dispatch names (`docs/research/2026-09-08-scheduler-surface-dispatch.md` §3),
executed: on the list (`Machine/Wake.lean`) — the two WHATWG capture rules (F6, F7), stale and
duplicate tokens (F2), the cancelled-waiter clause before and after the phase advance (F3),
the coalescing guard (F4), a non-FIFO sweep and a counted wake — and on this machine, at a
store that owes resumes: an inline wake against a scheduled one (F1), a posted batch wake
that resumes both waiters (F4), a stale resume task dispatched inert (F11), and the
unknown-owner frontier (`SCHED-FB-UNKNOWN-OWNER`). Provenance per case is the dispatch's;
nothing here claims a relation to rc.112 beyond the pinned lines the protocol cites
(`SCHED-FB-PRODUCER`: no rc.112 program in this tree posts a `Task.wake` before Latch/Queue
land). -/

section Wake

/-! ### The list -/

def l0 : WakeList Unit := WakeList.empty
def l1 : WakeList Unit := l0.register ⟨1⟩ 3 ()
def l2 : WakeList Unit := l1.register ⟨2⟩ 4 ()

-- F6: a waiter's identity — fiber, token, the phase at registration — is captured at
-- registration; a later advance of the list does not retarget it.
#guard l2.waiters = [⟨⟨1⟩, 3, 0, ()⟩, ⟨⟨2⟩, 4, 0, ()⟩]
#guard (l2.wakeAll).1 = [⟨⟨1⟩, 3, 0, ()⟩, ⟨⟨2⟩, 4, 0, ()⟩]
#guard (l2.wakeAll).2.phase = 1
-- F7: a registration after the advance carries the advanced phase.
#guard ((l2.wakeAll).2.register ⟨3⟩ 5 ()).waiters = [⟨⟨3⟩, 5, 1, ()⟩]
-- F3, before the advance: the pending waiter is spliced out, order kept, nothing owed.
#guard l2.cancel ⟨1⟩ 3 = ({ l2 with waiters := [⟨⟨2⟩, 4, 0, ()⟩] }, false)
-- F3, after the advance: the resumer won, the wake it consumed is owed.
#guard ((l2.wakeAll).2.cancel ⟨1⟩ 3).2 = true
-- F2: a stale token (never registered, or registered under another token) owes likewise —
-- the clause tests presence, and a duplicate cancel is the same answer twice.
#guard (l2.cancel ⟨1⟩ 9).2 = true
#guard ((l2.cancel ⟨1⟩ 3).1.cancel ⟨1⟩ 3).2 = true
-- F4: the first schedule captures the waiters and posts; the second joins and posts nothing;
-- a schedule with nobody pending does nothing.
#guard (l2.schedule).2 = true ∧ (l2.schedule).1.batch = some l2.waiters ∧
  (l2.schedule).1.waiters = [] ∧ (l2.schedule).1.phase = 1
#guard (((l2.schedule).1.register ⟨3⟩ 5 ()).schedule).2 = false
#guard (((l2.schedule).1.register ⟨3⟩ 5 ()).schedule).1.batch =
  some [⟨⟨1⟩, 3, 0, ()⟩, ⟨⟨2⟩, 4, 0, ()⟩, ⟨⟨3⟩, 5, 1, ()⟩]
#guard l0.schedule = (l0, false)
-- the batch runs once and clears
#guard ((l2.schedule).1.runBatch).1 = l2.waiters ∧ ((l2.schedule).1.runBatch).2.batch = none
-- a counted wake (`Pool.wakeWaiters`): the head `n`, the rest kept
#guard (l2.wakeTake 1).1 = [⟨⟨1⟩, 3, 0, ()⟩] ∧ (l2.wakeTake 1).2.waiters = [⟨⟨2⟩, 4, 0, ()⟩]
-- a sweep (`Semaphore.releaseUnsafe`): two free permits, a waiter wanting three is skipped
-- and a later one wanting one succeeds — the list is FIFO, the policy is not
def sem : WakeList Nat := (WakeList.empty.register ⟨1⟩ 1 3).register ⟨2⟩ 2 1
def sweepStep (free : Nat) (w : Waiter Nat) : Option Nat :=
  if w.payload ≤ free then some (free - w.payload) else none
#guard (sem.sweep sweepStep (fun free => free = 0) 2).1 = [⟨⟨2⟩, 2, 0, 1⟩]
#guard (sem.sweep sweepStep (fun free => free = 0) 2).2.1.waiters = [⟨⟨1⟩, 1, 0, 3⟩]
#guard (sem.sweep sweepStep (fun free => free = 0) 2).2.2 = 1
#guard (sem.sweep sweepStep (fun free => free = 0) 0).1 = []

/-! ### The machine, with a store that owes resumes -/

/-- A store: one waiter list whose payload is the row a waiter re-presents (the `Delay`
reply), the permits a take needs, and the resumes it owes. -/
structure WSt where
  list : WakeList Code
  permits : Nat
  due : List (Owed Code)

abbrev WM := RunMachine Unit Unit Nat Unit Unit FiberId Unit Unit WSt Code Saved Unit
abbrev WI := RunInterp Unit Unit Nat Unit Unit FiberId Unit Unit WSt Code

/-- The code a woken waiter resumes with. -/
def seven : Code := .pure (.success 7)

def winterp : WI where
  contA := fun _ v => .pure (.success v)
  contE := fun _ c => .pure (.failure c)
  syncValue := fun _ => 0
  suspendBody := fun _ => readNext
  iterNext := fun _ v => ([], .done v)
  loopTest := fun _ _ => false
  loopBody := fun _ v => .pure (.success v)
  loopStep := fun _ _ v => v
  loopDone := fun _ => 0
  finalizerExit := fun _ _ => Exit.void
  reifyExit := fun _ => 0
  cancelThenFail := fun _ c => .pure (.failure c)
  notImplemented := ()
  parkOf := fun _ => none
  parkCode := fun _ => readNext
  interruptCode := fun _ => readNext
  interruptAsCode := fun _ _ => readNext
  interruptAllCode := fun _ => readNext
  withFiberOf := fun _ => none
  syncState := fun _ _ => none
  registerAsync := fun _ _ _ s => (s, none)
  answerCode := fun
    | .ofExit exit => .pure exit
    | .ofRefGet _ => readNext
  -- the store owes what it holds, and a batch wake owes the batch inline, each waiter its row
  dueResumes := fun s => (s.due, { s with due := [] })
  wakeList := fun _ _ s =>
    let r := s.list.runBatch
    { s with list := r.2, due := s.due ++ r.1.map fun w => ⟨w.fiber, w.token, w.payload, WakeMode.now⟩ }
  cancelName := fun _ _ _ => ()
  abortName := ()
  parkCancelName := ()
  raceCancelName := fun _ => ()
  raceSettle := fun _ _ exit => .pure exit
  finalizerProgram := fun _ _ => none
  restoreName := fun _ => ()
  mergeName := fun _ => ()
  scopeStatus := fun _ _ => none
  scopeLinkFiber := fun _ _ _ _ => none
  dropFinalizer := fun _ _ _ => none
  closeScope := fun _ _ _ _ _ => none
  ambientScope := fun _ => none
  budgetOf := fun _ => (2048, false)
  emptyContext := ()
  contextValue := fun _ => 0
  exitValue := fun exit _ => .pure exit
  fiberValue := FiberId.value
  fiberIdValue := FiberId.value
  fibersValue := List.length
  exitsValue := List.length
  voidValue := 0
  scopeValue := fun _ => 0
  closeDoneName := ()
  encodeFiber := id
  stackAnnotations := fun _ => ReasonAnnotations.empty
  asyncFiberError := ()
  missingScope := ()

/-- The evaluator at this store: the one above, with the store read as a *take*. A permit
present is taken and the row answers `0`; none is the `Delay` reply — the fiber registers on
the list with this row as its payload and parks on a fresh token; the wake re-presents the
row and the take is polled again. -/
instance wakeEvaluator : FiberEvaluator Unit Unit Nat Unit Unit FiberId Unit Unit WSt Code Saved Unit where
  evaluate := fun i m f yielding =>
    match f.frame.current with
    | .pure (.success value) =>
      match f.frame.answers with
      | [] => ⟨m, f, yielding, .finished (.success value), []⟩
      | next :: rest =>
        ⟨m, { f with frame := { f.frame with current := next value, answers := rest } },
          yielding, .continue_, []⟩
    | .pure (.failure cause) => ⟨m, f, yielding, .finished (.failure cause), []⟩
    | .vis false next =>
      if m.state.permits > 0 then
        ⟨{ m with state := { m.state with permits := m.state.permits - 1 } },
          { f with frame := { f.frame with current := next 0 } }, yielding, .continue_, []⟩
      else
        let token := m.nextToken
        let m := { m with
          nextToken := m.nextToken + 1
          state := { m.state with list := m.state.list.delay f.id token f.frame.current } }
        ⟨m.emit [RunEvent.parkedOn f.id token], f.park ⟨token, none, [], [], Resume.void, false⟩,
          yielding, Outcome.parked, []⟩
    | .vis true next =>
      FiberAction.yieldNow i m
        { f with frame := { f.frame with answers := next :: f.frame.answers } } yielding 0

/-- A fiber parked on a token, ready to finish with whatever resumes it. -/
def parkedOn (id : FiberId) (token : Nat) : F :=
  { RunFiber.make id readNext true (2048, false) () with parked := .withGuard token }

/-- The root and two parked waiters, over a store. -/
def machine (s : WSt) : WM :=
  { (RunMachine.empty s : WM) with
    fibers := [RunFiber.make ⟨0⟩ readNext true (2048, false) (), parkedOn ⟨1⟩ 3, parkedOn ⟨2⟩ 4]
    nextId := 3 }

def wexitOf (m : WM) (id : Nat) : Option X := (m.fiber? ⟨id⟩).bind RunFiber.exit
def parkedOf (m : WM) (id : Nat) : Option Parked := (m.fiber? ⟨id⟩).map RunFiber.parked
def queuedOf (m : WM) (id : Nat) : Option Nat :=
  (m.fiber? ⟨id⟩).map fun f => ((f.dispatcher.buckets.map Bucket.tasks).flatten).length

/-- The store owes fiber 1 a resume, delivered by `mode`; permits enough for every take. -/
def owing (mode : WakeMode) : WSt := ⟨WakeList.empty, 100, [⟨⟨1⟩, 3, seven, mode⟩]⟩

-- F1, inline: the drain resumes fiber 1 in the same command sequence; nothing is posted.
#guard wexitOf (driveState winterp 20 (machine (owing .now)) [.drainDue]).1 1 = some (.success 7)
#guard (driveState winterp 20 (machine (owing .now)) [.drainDue]).1.armed = []
#guard queuedOf (driveState winterp 20 (machine (owing .now)) [.drainDue]).1 0 = some 0
-- F1, scheduled: the drain posts a resume task on fiber 0's dispatcher and arms it; fiber 1
-- stays parked until the host fires that dispatcher.
def afterPost : WM := (driveState winterp 20 (machine (owing (.scheduled ⟨0⟩ 0))) [.drainDue]).1
#guard wexitOf afterPost 1 = none
#guard parkedOf afterPost 1 = some (.withGuard 3)
#guard afterPost.armed = [⟨0⟩]
#guard queuedOf afterPost 0 = some 1
#guard wexitOf (replayEval winterp 20 [.fire ⟨0⟩] afterPost).machine 1 = some (.success 7)
#guard (replayEval winterp 20 [.fire ⟨0⟩] afterPost).machine.armed = []
-- the same through the host's `flush`
#guard wexitOf (replayEval winterp 20 [.flush] afterPost).machine 1 = some (.success 7)
-- SCHED-FB-UNKNOWN-OWNER: a scheduled wake addressed to a dispatcher whose fiber is gone is a
-- frontier, never a lost wake
#guard (driveState winterp 20 (machine (owing (.scheduled ⟨9⟩ 0))) [.drainDue]).1.stuck =
  some (Stuck.unknownFiber ⟨9⟩)

-- A dispatcher outlives its fiber's run, as rc.112's object does (`Queue.ts:455` stores it at
-- make): the machine keeps every fiber record, exited or not, so a post addressed to an exited
-- fiber lands on its dispatcher and the host's flush fires it.
def rootExited : WM :=
  { machine (owing (.scheduled ⟨0⟩ 0)) with
    fibers := [{ RunFiber.make ⟨0⟩ seven true (2048, false) () with exit := some (.success 7) },
      parkedOn ⟨1⟩ 3, parkedOn ⟨2⟩ 4] }
def afterExitedPost : WM := (driveState winterp 20 rootExited [.drainDue]).1
#guard wexitOf afterExitedPost 0 = some (.success 7) ∧ afterExitedPost.armed = [⟨0⟩]
#guard queuedOf afterExitedPost 0 = some 1
#guard wexitOf (replayEval winterp 20 [.flush] afterExitedPost).machine 1 = some (.success 7)

-- F4 on the machine: both waiters registered with their rows, the batch scheduled once (one
-- task posted, the second schedule joins it); the posted `Task.wake` runs the batch and
-- resumes both with their rows.
def l2c : WakeList Code := (WakeList.empty.register ⟨1⟩ 3 seven).register ⟨2⟩ 4 seven
def scheduled : WSt := ⟨(l2c.schedule).1, 100, []⟩
def afterWakePost : WM :=
  (machine scheduled).postTask ⟨0⟩ 0 (Task.wake (WakeKey.deferred ⟨0⟩) 1)
#guard afterWakePost.armed = [⟨0⟩] ∧ queuedOf afterWakePost 0 = some 1
def afterWake : WM := (replayEval winterp 40 [.fire ⟨0⟩] afterWakePost).machine
#guard wexitOf afterWake 1 = some (.success 7) ∧ wexitOf afterWake 2 = some (.success 7)
#guard afterWake.state.list.batch = none ∧ afterWake.state.due = []
#guard afterWake.armed = []

-- F11: a resume task for a token the fiber no longer parks on — a cancelled waiter's wake —
-- dispatches inert: the fiber stays parked on its own token, and the real answer still lands.
def stalePost : WM := (machine (owing .now)).postTask ⟨0⟩ 0 (Task.resume ⟨2⟩ 9 seven)
def afterStale : WM := (replayEval winterp 20 [.fire ⟨0⟩] stalePost).machine
#guard wexitOf afterStale 2 = none ∧ parkedOf afterStale 2 = some (.withGuard 4)
#guard wexitOf (replayEval winterp 20 [.answerAsync ⟨2⟩ 4 (.ofExit (.success 42))] afterStale).machine 2 =
  some (.success 42)

-- F5, the `Delay` reply: no permit, so the take registers the row and parks; a signal wakes it
-- with the row, the repoll finds no permit and parks again at the advanced phase (a spurious
-- wake, permitted); a permit and a second signal let the take succeed.
def taker : WM :=
  { (RunMachine.empty (⟨WakeList.empty, 0, []⟩ : WSt) : WM) with
    fibers := [RunFiber.make ⟨1⟩ readNext true (2048, false) ()], nextId := 2, nextToken := 5 }
def delayed : WM := (driveState winterp 20 taker [.evaluate ⟨1⟩]).1
#guard wexitOf delayed 1 = none ∧ parkedOf delayed 1 = some (.withGuard 5)
/-- The waiters as `(fiber, token, phase)` — the payload is a row, compared by what it does. -/
def shapeOf (m : WM) : List (Nat × Nat × Nat) :=
  m.state.list.waiters.map fun w => (w.fiber.value, w.token, w.phase)
#guard shapeOf delayed = [(1, 5, 0)]
/-- A signal: the head waiter owed its row, inline. -/
def signal (m : WM) : WM :=
  { m with state :=
      let r := m.state.list.wakeOne
      { m.state with
        list := r.2
        due := m.state.due ++ (r.1.map fun w => ⟨w.fiber, w.token, w.payload, WakeMode.now⟩).toList } }
def repolled : WM := (driveState winterp 20 (signal delayed) [.drainDue]).1
#guard wexitOf repolled 1 = none ∧ parkedOf repolled 1 = some (.withGuard 6)
#guard shapeOf repolled = [(1, 6, 1)] ∧ repolled.state.due.length = 0
def granted : WM := { repolled with state := { repolled.state with permits := 1 } }
def taken : WM := (driveState winterp 20 (signal granted) [.drainDue]).1
#guard wexitOf taken 1 = some (.success 0) ∧ taken.state.permits = 0
#guard taken.state.list.waiters = [] ∧ taken.state.list.phase = 2

end Wake

end Test.Runtime.SchedulerCoreContract
