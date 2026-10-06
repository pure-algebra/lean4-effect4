import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Program.MaskRuns
import Test.Program.MaskContract
import ProofGraph.Plan

/-!
# Test.Machine.MaskRuns — the saved mask's chain from one pop to a run: finite controls

`src/Effect4/Laws/Machine/MaskRuns.lean` carries the chain `FrameFiber.MaskChain` from the frame
machine's pop along a run, and `src/Effect4/Laws/Program/MaskRuns.lean` states the lift at the
compiled program's interpreter. This battery evaluates their statements on real fibers and on
real machines.

## Part A: the frames

- One sweep, at the alphabets `Nat`: every stack of at most three frames over eight frames, both
  flags, both bases, a pending cause or none, a deferred interrupt or none, and twenty
  primitives as `current`. Each state that holds the chain keeps it through `FrameFiber.step`.
  Each finished step and each pop that answers nothing ends at an empty stack and at the base.
- Four red controls, each red at its own property: a step that pushes a restoring frame and
  keeps the flag; the unanswered pop without the scratch premise; the flag's statement without
  the chain; the finished frame's statement without a finished step.

## Part B: the machine

- **The trap**, on one constructed machine: an arbitrary `Cmd.exitDone` on a live fiber breaks
  the invariant `MaskRuns`. The same machine keeps it under each alternative of the command
  condition `ClearReady`, and `Cmd.finish` keeps it with no condition.
- **Runs of a toy interpreter**, at each command budget and each prefix of a tape: a masked
  parent whose child inherits its mask, and a run that steps an exited fiber. At that reached
  machine the invariant holds, and the form over every fiber of the table is red.
- **A compiled program**: `Test.Program.MaskContract.s6`, with a mask, a masked fork and a
  restore site, replayed by `Api.replay` under the native evaluator. Exactly one table of start
  flags fits every cut.

Placement. Each guard is a finite instance of the proposed registry claim
`saved-mask-chain-runs` (concept `scope-lifetime-finalization`, requirement R11), or of one of
its steps. A machine outside these runs is not checked here: the theorems are the general
statements. Each run is one tape on the Lean machine. No guard states an agreement with a
target, a bracket of a region or a flag of an exited fiber.
-/

set_option autoImplicit false

namespace Test.Machine.MaskRuns

open Effect4 Effect4.FrameFiber Effect4.Machine

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

private def cause : C := ⟨[.interrupt (some 53) .empty]⟩

private def value : P := .onSuccess (.success 2) 3
private def handler : P := .onFailure (.success 4) 5

/-- A frame interpreter with both kinds of value arm that push: loop 1 goes on at its next
cursor, and generator 2 yields under itself. Loop 0 and the generators 0 and 1 stop. -/
private def frames : PrimInterp Nat Nat Nat Nat Nat Nat Nat where
  contA := fun name value => if name = 3 then .success (value + 1) else .sync name
  contE := fun _ cause => .failure cause
  syncValue := fun thunk => thunk
  suspendBody := fun thunk => .success thunk
  finalizerExit := fun _ _ => .success ()
  reifyExit := fun _ => 0
  iterNext := fun generator value =>
    ([], if generator = 0 then .done value else if generator = 1 then .halt cause
      else .resume (.success value) (generator - 1))
  loopEnter := fun loop cursor =>
    if loop = 0 then .finish (.success cursor) else .continue (cursor + 1) (.success cursor)
  loopResume := fun loop cursor value =>
    if loop = 0 then .finish (.success value) else .continue (cursor + 1) (.success value)
  notImplemented := 0
  cancelThenFail := fun _ cause => .failure cause

/-- The chain over a fiber's flag and its stack, decided by the law module's instance. -/
private def holds (base : Bool) (f : F) : Bool := decide (MaskChain base f.interruptible f.stack)

private def bools : List Bool := [true, false]

/-! # Part A: the frames -/

/-! ## The sweep -/

private def alphabet : List P :=
  [.setInterruptible true, .setInterruptible false, .onExit (.success 1) 9 false,
    .asyncFinalizer 7, value, handler, .whileLoop 1 0, .iterator 2 0]

/-- One primitive of each constructor as `current`, and a second one where an interpreter's
answer splits the step. -/
private def currents : List P :=
  [.success 0, .failure cause, .sync 1, .suspend 1, .withFiber 1, .yieldableError 1,
    .iterator 0 0, .iterator 2 0, value, .onSuccessConst (.success 1) (.success 2), handler,
    .onSuccessAndFailure (.success 1) 3 5, .exitFrame (.success 1), .onExit (.success 1) 9 false,
    .setInterruptible true, .whileLoop 0 0, .whileLoop 1 0, .yieldNowWith 0, .async 1 false none,
    .asyncFinalizer 7]

private def stacksUpTo : Nat → List (List P)
  | 0 => [[]]
  | n + 1 => [] :: (stacksUpTo n).flatMap fun stack => alphabet.map (· :: stack)

/-- The states of the sweep that hold the chain, each with its base. -/
private def states (depth : Nat) : List (Bool × F) :=
  (stacksUpTo depth).flatMap fun stack => bools.flatMap fun flag => bools.flatMap fun base =>
    [none, some cause].flatMap fun pendingCause => bools.flatMap fun deferred =>
      currents.filterMap fun current =>
        let f : F := ⟨current, stack, flag, pendingCause, deferred⟩
        if holds base f then some (base, f) else none

/-- A step that goes on keeps the chain, and a finished step retains an empty stack at the
base. -/
private def stepKeeps (base : Bool) (f : F) : Bool :=
  match (f.step frames).fst with
  | .running next => holds base next
  | .finished _ => (frameExitState f).stack.isEmpty && (frameExitState f).interruptible == base

private def finishes (f : F) : Bool :=
  match (f.step frames).fst with
  | .running _ => false
  | .finished _ => true

/-- A pop that answers nothing ends at an empty stack and at the base. -/
private def unansweredKeeps (base : Bool) (pop : FramePop Nat Nat Nat Nat Nat Nat Nat) : Bool :=
  pop.answer != .empty || (pop.fiber.stack.isEmpty && pop.fiber.interruptible == base)

#guard (stacksUpTo 3).length == 585
#guard (states 3).length == 64000

-- `FrameFiber.step` keeps the chain where it goes on, and it finishes at the base.
#guard (states 3).all fun (base, f) => stepKeeps base f
-- Both outcomes are in the sweep.
#guard ((states 3).countP fun (_, f) => finishes f) == 1040

-- Each pop that answers nothing ends at an empty stack and at the base: each demand, each skip
-- flag, a carried cause or none.
#guard (states 3).all fun (base, f) => Arm.all.all fun d => bools.all fun s =>
  unansweredKeeps base (f.getCont d s) && unansweredKeeps base (f.getCont d s (some cause))
-- The same for the pop itself, from an empty scratch stack.
#guard (states 3).all fun (base, f) => Arm.all.all fun d => bools.all fun s =>
  unansweredKeeps base (popFrom d s f.stack { f with stack := [] })
-- The sweep holds pops that answer nothing: the two checks above are not empty.
#guard ((states 3).foldl (fun n (_, f) => n + Arm.all.foldl (fun k d =>
  k + bools.countP fun s => (f.getCont d s).answer == .empty) 0) 0) == 61760

/-! ## The red controls -/

/-! ### 1. A step that pushes a restoring frame and keeps the flag -/

/-- A wrong entry of a region: it pushes the frame that returns the flag, and it keeps the
flag. A real entry pushes that frame only where it changes the flag. -/
private def pushNoMask (f : F) : F :=
  { f with stack := .setInterruptible f.interruptible :: f.stack }

-- It breaks the chain at every state of the sweep. The real entries keep it.
#guard (states 3).all fun (base, f) => !holds base (pushNoMask f)
#guard (states 3).all fun (base, f) => holds base f.uninterruptible

/-! ### 2. The unanswered pop without the scratch premise -/

/-- With no frame to pop, the pop answers nothing and its stack is the scratch stack. So the
statement needs the empty scratch stack. -/
theorem unanswered_needs_empty_scratch :
    ¬ ∀ (demand : Arm) (skip : Bool) (frames : List P) (f : F),
      (popFrom demand skip frames f).answer = ContAnswer.empty →
        (popFrom demand skip frames f).fiber.stack = [] := by
  intro h
  exact absurd (h .contA false [] ⟨.success 0, [value], true, none, false⟩ rfl) (by decide)

/-! ### 3. The flag's statement without the chain -/

/-- An empty stack answers nothing at either flag. So the flag is the base only under the
chain. -/
theorem unanswered_flag_needs_chain :
    ¬ ∀ (base : Bool) (f : F) (demand : Arm) (skip : Bool) (carried : Option C),
      (f.getCont demand skip carried).answer = ContAnswer.empty →
        (f.getCont demand skip carried).fiber.interruptible = base := by
  intro h
  exact absurd (h true ⟨.success 0, [], false, none, false⟩ .contA false none rfl) (by decide)

/-- One flag and one stack give one base: with two flags, two empty stacks have each its own
base. -/
theorem base_needs_flag :
    ¬ ∀ (base base' flag flag' : Bool) (stack : List P),
      MaskChain base flag stack → MaskChain base' flag' stack → base = base' :=
  fun h => Bool.noConfusion (h true false true false [] rfl rfl)

/-! ### 4. The finished frame's statement without a finished step -/

/-- A step that goes on: the value frame answers, and the cause frame under it stays. -/
private def answered : F := ⟨.success 0, [value, handler], true, none, false⟩

-- `frameExitState` alone gives no empty stack: the premise of a finished step is needed.
#guard !finishes answered
#guard (frameExitState answered).stack == [handler]
#guard holds true (frameExitState answered)

/-! ## The statements of part A, pinned

The brief's two statements of part A as they stand, by their types at the alphabets `Nat`. -/

example : ∀ (base : Bool) (interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat) (f : F),
    MaskChain base f.interruptible f.stack → ∀ (next : F),
      (f.step interp).fst = FrameStep.running next → MaskChain base next.interruptible next.stack :=
  step_maskChain

example : ∀ (demand : Arm) (skip : Bool) (frames : List P) (f : F), f.stack = [] →
    (popFrom demand skip frames f).answer = ContAnswer.empty →
      (popFrom demand skip frames f).fiber.stack = [] :=
  popFrom_unanswered_stack

example : ∀ (base : Bool) (demand : Arm) (skip : Bool) (frames : List P) (f : F), f.stack = [] →
    MaskChain base f.interruptible frames →
      (popFrom demand skip frames f).answer = ContAnswer.empty →
        (popFrom demand skip frames f).fiber.interruptible = base :=
  popFrom_unanswered_flag

example : ∀ (base : Bool) (interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat) (f : F),
    MaskChain base f.interruptible f.stack → ∀ (exit : Exit Nat Nat Nat Nat Nat),
      (f.step interp).fst = FrameStep.finished exit →
        (frameExitState f).stack = [] ∧ (frameExitState f).interruptible = base :=
  fun base interp f valid exit finished =>
    ⟨step_finished_stack interp f exit finished,
      step_finished_flag base interp f valid exit finished⟩

/-- A statement in use: a step of a fiber of the sweep keeps the chain. -/
example : ∀ next : F, (answered.step frames).fst = FrameStep.running next →
    MaskChain true next.interruptible next.stack :=
  step_maskChain true frames answered (by decide)

/-! # Part B: the machine -/

private abbrev M := RunMachine Nat Nat Nat Nat Nat Nat Nat Unit Unit
private abbrev R := RunFiber Nat Nat Nat Nat Nat Nat Nat Unit
private abbrev D := RunDecision Nat Nat Nat Nat Nat Nat Nat
private abbrev K := Cmd Nat Nat Nat Nat Nat Nat Nat

/-- The second fiber of the reached machine: it awaits fiber 0, then it evaluates the
registration of race 0, which fiber 0 hosts. -/
private def waiter : P := .onSuccess (.suspend 100) 20

/-- A toy interpreter at the alphabets `Nat`. Its `parkOf` reads two thunks as parks:
`suspend 100` awaits fiber 0, and `suspend (1000 + k)` is the registration of race `k`. Its
`withFiberOf` reads six thunks as actions. A settled race resumes its host into a masked yield. -/
private def toy : RunInterp Nat Nat Nat Nat Nat Nat Nat Unit Unit where
  contA := fun name _ =>
    if name = 10 then .withFiber 2 else if name = 20 then .suspend 1000 else .success 0
  contE := fun _ cause => .failure cause
  syncValue := fun _ => 0
  suspendBody := fun _ => .success 0
  finalizerExit := fun _ _ => .success ()
  reifyExit := fun _ => 0
  iterNext := fun _ _ => ([], .done 0)
  loopEnter := fun _ _ => .finish (.success 0)
  loopResume := fun _ _ _ => .finish (.success 0)
  notImplemented := 0
  cancelThenFail := fun _ cause => .failure cause
  parkOf := fun code =>
    match code with
    | .suspend n =>
      if n = 100 then some (.ok (.join ⟨0⟩ .awaitValue))
      else if 1000 ≤ n then some (.ok (.race (n - 1000)))
      else none
    | _ => none
  parkCode := fun kind =>
    match kind with
    | .race k => .suspend (1000 + k)
    | _ => .success 0
  interruptCode := fun _ => .success 0
  interruptAsCode := fun _ _ => .success 0
  interruptAllCode := fun _ => .success 0
  withFiberOf := fun thunk =>
    if thunk = 1 then some (.fork waiter ⟨true, true, .interruptible⟩)
    else if thunk = 2 then some (.raceAll [.success 7])
    else if thunk = 3 then some (.setInterruptible (.yieldNowWith 0) false)
    else if thunk = 4 then some (.setInterruptible (.withFiber 5) false)
    else if thunk = 5 then some (.fork (.withFiber 6) ⟨true, true, .inherit⟩)
    else if thunk = 6 then some (.setInterruptible (.yieldNowWith 0) true)
    else none
  syncState := fun _ _ => none
  registerAsync := fun _ _ _ st => (st, none)
  answerCode := fun _ => .success 0
  dueResumes := fun st => ([], st)
  wakeList := fun _ _ st => st
  clockStep := fun _ st => (none, st)
  cancelName := fun name _ _ => name
  abortName := 0
  parkCancelName := 0
  raceCancelName := fun _ => 0
  raceSettle := fun _ _ _ => .withFiber 3
  finalizerProgram := fun _ _ => none
  restoreName := fun _ => 0
  mergeName := fun _ => 0
  scopeStatus := fun _ _ => none
  scopeLinkFiber := fun _ _ _ _ => none
  dropFinalizer := fun _ _ _ => none
  closeScope := fun _ _ _ _ _ => none
  ambientScope := fun _ => none
  budgetOf := fun _ => (1000000, true)
  emptyContext := ()
  contextValue := fun _ => 0
  exitValue := fun _ _ => .success 0
  fiberValue := fun id => id.value
  fiberIdValue := fun id => id.value
  restoreValue := fun _ => 0
  fibersValue := fun _ => 0
  exitsValue := fun _ => 0
  voidValue := 0
  scopeValue := fun n => n
  closeDoneName := 0
  encodeFiber := fun id => id.value
  stackAnnotations := fun _ => ReasonAnnotations.empty
  asyncFiberError := 0
  missingScope := 0

/-- The saved flags of a stack, from the top: the flags of its restoring frames. -/
private def savedFlags {ν σ β ε δ ι α : Type} (stack : List (Prim ν σ β ε δ ι α)) : List Bool :=
  stack.filterMap fun p => match p with
    | Prim.setInterruptible saved => some saved
    | _ => none

/-- The invariant at a table, decided by the law module's instance. -/
private def runs (bases : List Bool) (m : M) : Bool := decide (MaskRuns bases m)

/-! ## The trap, and the same machine under the condition -/

/-- A machine with one fiber, at id 0, which started at flag true. -/
private def single (frame : F) (exit : Option (Exit Nat Nat Nat Nat Nat)) : M :=
  { (RunMachine.empty () : M) with
    fibers := [{ (RunFiber.make ⟨0⟩ (.success 0) true (1000000, true) () : R) with
      frame := frame, exit := exit }]
    nextId := 1 }

/-- A masked frame under the frame that returns the flag: the chain holds at base true. -/
private def maskedFrame : F := ⟨.success 0, [.setInterruptible true], false, none, false⟩

/-- **The trap**: a live fiber at flag false under one restoring frame. -/
private def trap : M := single maskedFrame none
/-- The same fiber, published. -/
private def published : M := single maskedFrame (some (.success 0))
/-- A live fiber at an empty stack. -/
private def emptied : M := single ⟨.success 0, [], true, none, false⟩ none
/-- A live fiber at its base, over a neutral frame. -/
private def atBase : M := single ⟨.success 0, [value], true, none, false⟩ none

/-- An arbitrary `Cmd.exitDone` for fiber 0. -/
private def clear (m : M) : M := (driveStep toy m (Cmd.exitDone ⟨0⟩) []).1

-- Each machine holds the invariant at the table `[true]`.
#guard runs [true] trap && runs [true] published && runs [true] emptied && runs [true] atBase
-- The trap: the clearing breaks the invariant. The stack is empty, and the flag is not the base.
#guard !runs [true] (clear trap)
#guard (clear trap).fibers.map (fun f => (f.frame.interruptible, f.frame.stack.length)) ==
  [(false, 0)]
-- The same machine under each alternative of the condition keeps it.
#guard runs [true] (clear published) && runs [true] (clear emptied) && runs [true] (clear atBase)
-- `Cmd.finish` asks for nothing: it publishes the trap's fiber before it clears it.
#guard runs [true] (driveStep toy trap (Cmd.finish ⟨0⟩ (.success 0)) []).1
-- A live fiber has one entry: the other table is red at the trap. An exited fiber's entry is
-- free, so both tables hold at the published fiber.
#guard !runs [false] trap
#guard runs [false] published

/-- **The trap, proved.** Without the command condition the statement is false: an arbitrary
`Cmd.exitDone` clears a live fiber's stack and keeps its flag. No table that extends `[true]`
holds the invariant after it. -/
theorem exitDone_needs_ready :
    ¬ ∀ (bases : List Bool) (m : M) (c : K) (rest : List K), MaskRuns bases m →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep toy m c rest).1 := by
  intro h
  obtain ⟨bases', le, kept⟩ := h [true] trap (Cmd.exitDone ⟨0⟩) [] (by decide)
  have same : [true] = bases' := le.eq_of_length kept.1.symm
  subst same
  exact absurd kept (by decide)

/-- The trap does not meet the condition: the fiber is live, its stack holds a frame, and its
flag is not its base. -/
example : ¬ ClearReady [true] trap (Cmd.exitDone ⟨0⟩) := by
  intro ready
  rcases ready _ rfl with exited | empty | based
  · cases exited
  · cases empty
  · cases based

/-- The condition's first alternative, at the published fiber: the theorem keeps the invariant. -/
example : ∃ bases', [true] <+: bases' ∧ MaskRuns bases' (clear published) :=
  driveStep_maskRuns toy (evaluatePrim_evaluatorKeepsMask toy) [true] published _ [] (by decide)
    (fun f found => by
      obtain rfl := Option.some.inj found
      exact Or.inl rfl)

/-- The second alternative, at the empty stack. -/
example : ∃ bases', [true] <+: bases' ∧ MaskRuns bases' (clear emptied) :=
  driveStep_maskRuns toy (evaluatePrim_evaluatorKeepsMask toy) [true] emptied _ [] (by decide)
    (fun f found => by
      obtain rfl := Option.some.inj found
      exact Or.inr (Or.inl rfl))

/-- The third alternative, at the base. -/
example : ∃ bases', [true] <+: bases' ∧ MaskRuns bases' (clear atBase) :=
  driveStep_maskRuns toy (evaluatePrim_evaluatorKeepsMask toy) [true] atBase _ [] (by decide)
    (fun f found => by
      obtain rfl := Option.some.inj found
      exact Or.inr (Or.inr rfl))

/-! ## Runs of the toy interpreter -/

/-- A machine with one root at id 0, not yet evaluated. A root starts at flag true. -/
private def rooted (program : P) : M :=
  { (RunMachine.empty () : M) with
    fibers := [RunFiber.make ⟨0⟩ program true (toy.budgetOf ()) ()]
    nextId := 1 }

private def machineOf : ReplayResult Nat Nat Nat Nat Nat Nat Nat Unit Unit → M
  | .finished m => m
  | .frontier _ m => m
  | .stuck _ m => m

/-- The machine that a tape reaches at one command budget. -/
private def reach (program : P) (fuel : Nat) (tape : List D) : M :=
  machineOf (replayEval toy fuel tape (rooted program))

/-- Each prefix of a tape, the empty one first. -/
private def prefixes (tape : List D) : List (List D) :=
  (List.range (tape.length + 1)).map tape.take

/-- What a fiber shows: its id, its flag, its saved flags from the top, and whether it has
exited. -/
private def seen (m : M) : List (Nat × Bool × List Bool × Bool) :=
  m.fibers.map fun f =>
    (f.id.value, f.frame.interruptible,
      savedFlags f.frame.stack,
      f.exit.isSome)

/-- The form of the invariant over every fiber of the table, exited or not. It is the red
control's form: the law does not state it. -/
private def everyFiber (bases : List Bool) (m : M) : Bool :=
  m.fibers.all fun f =>
    match bases[f.id.value]? with
    | some base => decide (MaskChain base f.frame.interruptible f.frame.stack)
    | none => false

/-! ### A masked parent, and a child that inherits its mask -/

/-- The root masks itself and forks a child that inherits the mask. The child opens an
`interruptible` region and yields there. -/
private def inherits : P := .withFiber 4

private def inheritTape : List D := [.evaluate ⟨0⟩, .fire ⟨1⟩]

-- After the root's evaluation the child is parked in its region: its base is false, its flag is
-- true, and its stack holds the frame that returns false. The root has exited at its base.
#guard seen (reach inherits 400 [.evaluate ⟨0⟩]) ==
  [(0, true, [], true), (1, true, [false], false)]
-- After the child's resume it has exited at its base, false.
#guard seen (reach inherits 400 inheritTape) == [(0, true, [], true), (1, false, [], true)]
-- The table is `[true, false]`: the child's entry is the flag that it inherited.
#guard (List.range 40).all fun fuel => (prefixes inheritTape).all fun tape =>
  let m := reach inherits fuel tape
  runs ([true, false].take m.nextId) m
-- The cuts hold a live masked root and a live child in its region: the check is not empty.
#guard (List.range 40).any fun fuel =>
  seen (reach inherits fuel [.evaluate ⟨0⟩]) == [(0, false, [true], false), (1, false, [], false)]
-- Red: the child's entry is no arbitrary bit. The table `[true, true]` fails where the child is
-- live.
#guard !runs [true, true] (reach inherits 400 [.evaluate ⟨0⟩])

/-- The theorem at this run: a table extends the root's, and it holds the invariant. -/
example : ∃ bases', [true] <+: bases' ∧
    MaskRuns bases' (replayEval toy 400 inheritTape (rooted inherits)).machine :=
  replayEval_maskRuns toy (evaluatePrim_evaluatorKeepsMask toy) 400 inheritTape [true]
    (rooted inherits) (by decide)

/-! ### The reached machine: an exited fiber that a second fiber steps

Fiber 0 forks fiber 1, then it hosts race 0. The race settles into a masked yield, and fiber 0
exits after it. Fiber 1 awaits fiber 0. At fiber 0's exit its observer resumes fiber 1, which
evaluates the registration of race 0. `Cmd.registrationDone` continues the race's host, so
fiber 0 enters the masked yield again, between its publication and its `Cmd.exitDone`. -/

private def hosts : P := .onSuccess (.withFiber 1) 10

private def hostTape : List D := [.evaluate ⟨0⟩, .fire ⟨0⟩]

/-- The machine that the driver's own commands reach. -/
private def reached : M := reach hosts 400 hostTape

-- It is no stuck machine, and its race is settled.
#guard reached.stuck.isNone
#guard reached.races.map (fun r => (r.id, r.host.value, r.settled)) == [(0, 0, true)]
-- Fiber 0 has exited. Its stack is empty and its flag is false. It started at true.
#guard seen reached == [(0, false, [], true), (1, true, [], false), (2, true, [], true)]
-- So the form over every fiber is red at a reached machine, at the run's own table.
#guard !everyFiber [true, true, true] reached
-- No table that extends the root's rescues that form: fiber 0's entry is its start flag.
#guard [[true, true, true], [true, true, false], [true, false, true], [true, false, false]].all
  fun bases => !everyFiber bases reached
-- The invariant holds there: it ranges over the fibers that have not exited.
#guard runs [true, true, true] reached
-- Before the second fire both forms hold: fiber 0 is live and masked, under its restoring frame.
#guard seen (reach hosts 400 [.evaluate ⟨0⟩]) ==
  [(0, false, [true], false), (1, true, [], false), (2, true, [], true)]
#guard everyFiber [true, true, true] (reach hosts 400 [.evaluate ⟨0⟩])
-- At every command budget and every prefix of the tape, the invariant holds.
#guard (List.range 80).all fun fuel => (prefixes hostTape).all fun tape =>
  let m := reach hosts fuel tape
  runs ([true, true, true].take m.nextId) m

/-- The theorem at the reached machine. -/
example : ∃ bases', [true] <+: bases' ∧
    MaskRuns bases' (replayEval toy 400 hostTape (rooted hosts)).machine :=
  replayEval_maskRuns toy (evaluatePrim_evaluatorKeepsMask toy) 400 hostTape [true]
    (rooted hosts) (by decide)

/-! ## A compiled program: a mask, a masked fork and a restore site

`Test.Program.MaskContract.s6` (`Test/Program/MaskContract.lean`): the root runs a mask, forks a
child that starts masked and waits at a restore site, and forks a second child that interrupts
the first. The one build admits it, and `Api.replay` runs it under the native evaluator. `s3` is
a second program: a fork of nested masks. Each control is finite: one tape, cut at each command
budget below a bound and at the full budget. -/

section Compiled

open Effect4.Program Effect4.Program.Authoring Test.Program.MaskContract

private def flushes : List Api.Decision := [Api.evaluate, Api.flush, Api.flush, Api.flush]

/-- The machines that a compiled program's replay reaches, cut at each command budget below
`upTo` and at the full budget. -/
private def cuts (src : Src NativeOp) (upTo : Nat) : List Api.Machine :=
  match buildOf (mk src) with
  | none => []
  | some p => (List.range upTo ++ [fuel]).map fun n => (Api.replay p n flushes [] [] fuel).machine

private def tablesOf : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (tablesOf n).flatMap fun table => [table ++ [true], table ++ [false]]

/-- The tables of one length at which every cut holds the invariant, each cut at the table's
prefix of its own allocator. One growing table for the whole run is what the law states. -/
private def fitting (machines : List Api.Machine) (n : Nat) : List (List Bool) :=
  (tablesOf n).filter fun bases => machines.all fun m => decide (MaskRuns (bases.take m.nextId) m)

private def shown (m : Api.Machine) : List (Nat × Bool × List Bool × Bool) :=
  m.fibers.map fun f =>
    (f.id.value, f.frame.interruptible,
      savedFlags f.frame.stack,
      f.exit.isSome)

-- The program builds, and its run allocates three fibers.
#guard (cuts s6 160).length == 161
#guard ((cuts s6 160).map (·.nextId)).eraseDups == [1, 2, 3]
-- Exactly one table fits every cut: the root started at true, the masked child at false, and
-- the second child at true. Each other table is red at some cut.
#guard fitting (cuts s6 160) 3 == [[true, false, true]]
-- The cuts hold live fibers inside regions: the root under its mask's frame, the masked child
-- at its restore site, and the child masked again over both saved flags.
#guard ((cuts s6 160).map shown).contains [(0, false, [true], false)]
#guard ((cuts s6 160).map shown).contains [(0, true, [], false), (1, true, [false], false)]
#guard ((cuts s6 160).map shown).contains
  [(0, true, [], false), (1, false, [true, false], false), (2, true, [], false)]
-- At the full budget every fiber has exited: the invariant asks nothing of it there.
#guard (cuts s6 160).getLast?.map shown ==
  some [(0, true, [], true), (1, false, [], true), (2, true, [], true)]
-- A second program, with a fork of nested masks: one table again.
#guard fitting (cuts s3 200) 3 == [[true, true, true]]

/-- The theorem at the program interface: it takes no premise on the program. -/
example (p : Api.Program) (budget : Nat) :
    ∃ bases, [true] <+: bases ∧ MaskRuns bases (Api.replay p budget flushes [] [] fuel).machine :=
  Api.replay_maskRuns p budget flushes [] [] fuel

end Compiled

/-! ## The statements of part B, pinned -/

/-- The general form at the alphabets `Nat`. -/
private theorem atNat : MaskChainRuns Nat Nat Nat Nat Nat Nat Nat Unit Unit :=
  saved_mask_chain_runs Nat Nat Nat Nat Nat Nat Nat Unit Unit

example : ∀ (interp : RunInterp Nat Nat Nat Nat Nat Nat Nat Unit Unit) (bases : List Bool) (m : M)
    (c : K) (rest : List K), MaskRuns bases m → ClearReady bases m c →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (driveStep interp m c rest).1 :=
  atNat.command

example : ∀ (interp : RunInterp Nat Nat Nat Nat Nat Nat Nat Unit Unit) (fuel : Nat)
    (tape : List D) (bases : List Bool) (m : M), MaskRuns bases m →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases' (replayEval interp fuel tape m).machine :=
  atNat.replay

example : ∀ (interp : RunInterp Nat Nat Nat Nat Nat Nat Nat Unit Unit) (m : M) (f : R) (y : Bool)
    (exit : Exit Nat Nat Nat Nat Nat),
    (evaluatePrim interp m f y).outcome = Outcome.finished exit →
      (evaluatePrim interp m f y).fiber.frame.stack = [] :=
  atNat.finished

example : ∀ (bases bases' : List Bool) (m : M) (f : R), MaskRuns bases m → MaskRuns bases' m →
    f ∈ m.fibers → f.exit = none → bases[f.id.value]? = bases'[f.id.value]? :=
  atNat.sameBase

/-- The placed statement, as it stands: the compiled program's interpreter under the native
evaluator. -/
example : ∀ (root : Program.NativeEff) (table : Program.RowTable) (fuel : Nat)
    (tape : List Api.Decision) (bases : List Bool) (m : Api.Machine), MaskRuns bases m →
      ∃ bases', bases <+: bases' ∧ MaskRuns bases'
        (replayEval (evaluator := Program.evaluatorFor root table) (Program.interpOf root table)
          fuel tape m).machine :=
  Program.compiled_mask_chain_runs

/-- A field in use: the empty machine, then a root at flag true. -/
example : MaskRuns [true] (rooted hosts) :=
  atNat.start [] (RunMachine.empty ()) hosts true (toy.budgetOf ()) () (atNat.empty ())

/-! ## The pinned outputs

The axioms of the statements, and the standing of the two placed theorems as the plan derives
it from their proofs. The counts are of this battery's tree, which holds no step of a proof. -/

/-- info: 'Effect4.FrameFiber.step_maskChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_maskChain

/-- info: 'Effect4.FrameFiber.popFrom_unanswered_stack' depends on axioms: [propext] -/
#guard_msgs in
#print axioms popFrom_unanswered_stack

/-- info: 'Effect4.FrameFiber.popFrom_unanswered_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms popFrom_unanswered_flag

/-- info: 'Effect4.Machine.step_finished_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_finished_stack

/-- info: 'Effect4.Machine.step_finished_flag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_finished_flag

/-- info: 'Effect4.Program.compiled_mask_chain_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Program.compiled_mask_chain_runs

/-- info: 'Effect4.Api.replay_maskRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Api.replay_maskRuns

/-- info: 'Effect4.Machine.saved_mask_chain_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms saved_mask_chain_runs

/-- info: 'Effect4.Machine.driveStep_maskRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms driveStep_maskRuns

/-- info: 'Effect4.Machine.maskRuns_stepKeeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms maskRuns_stepKeeps

/--
info: Effect4.Program.compiled_mask_chain_runs: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Program.compiled_mask_chain_runs

/--
info: Effect4.Machine.saved_mask_chain_runs: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status saved_mask_chain_runs

end Test.Machine.MaskRuns
