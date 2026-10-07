import Effect4.Laws.Machine.MaskBracket
import Effect4.Laws.Program.MaskBracket
import Test.Program.MaskContract
import ProofGraph.Plan

/-!
# Test.Machine.MaskBracket — a region ends with its entry flag: finite controls

`src/Effect4/Laws/Machine/MaskBracket.lean` states the bracket of a region on the frame machine
and along a run, and `src/Effect4/Laws/Program/MaskBracket.lean` states it at the compiled
program's interpreter, with the second fact: a fiber that a pending command steps has not
exited. This battery evaluates their statements on real fibers, on real machines and on the
cuts of real command loops.

## Part A: the frames

- One sweep, at the alphabets `Nat`: every stack of at most three frames over eight frames,
  split at each point into own frames and frames under them. The chain splits at each point at
  exactly one flag. The pop of the two lists is the joined pop, from each scratch stack. A step
  that goes on keeps the frames under the region. Each pop of the own frames that answers
  nothing ends the region at the entry's stack and at the entry flag, and the pop goes on from
  the region's end.
- Five red controls: the end is no cut between two steps; a pop that an own frame answers; the
  own frames at the fiber's base; two bases; the ending step with its code unchanged.

## Part B: the machine

- Two red controls on constructed machines, one for each fact: a pair of cuts with two stacks
  has two flags, and a fiber that has exited at the second cut has the entry's stack and
  another flag.
- A toy interpreter's run steps an exited fiber, at two cuts of one command loop. The second
  fact is false there.

## Part C: compiled programs

- Three programs, read at the cuts of the root's first command loop: a region that changes no
  flag, whose body changes the flag and returns, inside a nested region; a region whose body is
  interrupted; the mask's derived form under a masked caller.
- At each cut a fiber that a pending command steps is live, and the machine holds the chain's
  invariant at one table. On each pair of cuts the own frames hold the chain at the entry flag,
  and each pop of the own frames that answers nothing ends the region at the entry's stack and
  at the entry flag.
- The decision cuts of the same runs show no fiber inside a region.

Placement. Each guard is a finite instance of the proposed registry claims
`saved-mask-region-bracket` and `stepped-fiber-live` (concept `scope-lifetime-finalization`,
requirement R11), or of one of their steps. A run outside these is not checked here: the
theorems are the general statements. Each run is one schedule on the Lean machine. No guard
states an agreement with a target, a cleanup, a delivery or a budget. No guard states that a
body's run keeps the stack shape `above ++ below`. The cuts of these runs show it, and no theorem
gives it.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Machine.MaskBracket

open Effect4 Effect4.FrameFiber Effect4.Machine

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

private def cause : C := ⟨[.interrupt (some 53) .empty]⟩

private def value : P := .onSuccess (.success 2) 3
private def handler : P := .onFailure (.success 4) 5

/-- The frame interpreter of `Test/Machine/MaskRuns.lean`: loop 1 goes on at its next cursor, and
generator 2 yields under itself. A cause continuation fails with the cause that it is given. -/
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

/-- The chain over a flag and a stack, decided by the law module's instance. -/
private def chain (base flag : Bool) (stack : List P) : Bool := decide (MaskChain base flag stack)

private def bools : List Bool := [true, false]

/-! # Part A: the frames -/

/-! ## The sweep -/

private def alphabet : List P :=
  [.setInterruptible true, .setInterruptible false, .onExit (.success 1) 9 false,
    .asyncFinalizer 7, value, handler, .whileLoop 1 0, .iterator 2 0]

private def stacksUpTo : Nat → List (List P)
  | 0 => [[]]
  | n + 1 => [] :: (stacksUpTo n).flatMap fun stack => alphabet.map (· :: stack)

/-- Each split of each stack: the own frames, and the frames under them. -/
private def splits (depth : Nat) : List (List P × List P) :=
  (stacksUpTo depth).flatMap fun stack =>
    (List.range (stack.length + 1)).map fun k => (stack.take k, stack.drop k)

#guard (stacksUpTo 3).length == 585
#guard (splits 3).length == 2257

/-! ### The chain splits at each point, at exactly one flag -/

/-- The flags at which the chain splits: the chain over the own frames at that flag as their
base, and the chain over the frames under them at that flag. -/
private def mids (base flag : Bool) (above below : List P) : List Bool :=
  bools.filter fun mid => chain mid flag above && chain base mid below

-- `MaskChain.append_iff`: the chain over the whole stack holds exactly where it splits, and it
-- splits at one flag.
#guard (splits 3).all fun (above, below) => bools.all fun base => bools.all fun flag =>
  (mids base flag above below).length == (if chain base flag (above ++ below) then 1 else 0)
-- Both outcomes are in the sweep.
#guard ((splits 3).foldl (fun n (above, below) => n + (bools.flatMap fun base =>
  bools.filter fun flag => chain base flag (above ++ below)).length) 0) == 3068
-- `MaskChain.above`: each flag that holds the chain over the frames under the region, at the
-- base, is the base of the own frames.
#guard (splits 3).all fun (above, below) => bools.all fun base => bools.all fun flag =>
  bools.all fun entry =>
    !(chain base flag (above ++ below) && chain base entry below) || chain entry flag above

/-! ### The pop of two lists of frames -/

/-- The pop of `above ++ below`, written from the pop of `above`: what
`popFrom_append_answered` and `popFrom_append_unanswered` state. -/
private def joined (demand : Arm) (skip : Bool) (above below : List P) (f : F)
    (carried : Option C) : FramePop Nat Nat Nat Nat Nat Nat Nat :=
  let head := popFrom demand skip above f carried
  if head.answer == .empty then
    let tail := popFrom demand skip below head.fiber head.carriedCause
    ⟨tail.answer, head.popped ++ tail.popped, head.events ++ tail.events, tail.fiber,
      tail.carriedCause⟩
  else { head with fiber := { head.fiber with stack := head.fiber.stack ++ below } }

/-- The fibers that a pop starts from: both flags, a pending cause or none, and a scratch stack
that is empty or holds one frame. -/
private def starts : List F :=
  bools.flatMap fun flag => [none, some cause].flatMap fun pending =>
    [[], [value]].map fun scratch => ⟨.success 0, scratch, flag, pending, false⟩

-- The pop's law, at each demand, skip flag and carried cause. It asks for no scratch premise.
#guard (splits 3).all fun (above, below) => starts.all fun f =>
  [Arm.contA, Arm.contE].all fun d => bools.all fun s => [none, some cause].all fun carried =>
    popFrom d s (above ++ below) f carried == joined d s above below f carried
-- Both shapes are in the sweep: pops of the own frames that answer, and pops that do not.
#guard ((splits 3).foldl (fun n (above, _) => n + (starts.filter fun f =>
  (popFrom Arm.contA false above f).answer == .empty).length) 0) == 6295
#guard ((splits 3).foldl (fun n (above, _) => n + (starts.filter fun f =>
  (popFrom Arm.contA false above f).answer != .empty).length) 0) == 11761

/-! ### Between the cuts: a step that goes on keeps the frames under the region -/

/-- One primitive of each constructor as the code, and a second one where an interpreter's
answer splits the step. -/
private def codes : List P :=
  [.success 0, .failure cause, .sync 1, .suspend 1, .withFiber 1, .yieldableError 1,
    .iterator 0 0, .iterator 2 0, value, .onSuccessConst (.success 1) (.success 2), handler,
    .onSuccessAndFailure (.success 1) 3 5, .exitFrame (.success 1), .onExit (.success 1) 9 false,
    .setInterruptible true, .whileLoop 0 0, .whileLoop 1 0, .yieldNowWith 0, .async 1 false none,
    .asyncFinalizer 7]

/-- The own fibers of the sweep: each code, both flags, a pending cause or none, a deferred
interrupt or none. -/
private def owns (above : List P) : List F :=
  codes.flatMap fun code => bools.flatMap fun flag => [none, some cause].flatMap fun pending =>
    bools.map fun deferred => ⟨code, above, flag, pending, deferred⟩

/-- `step_under` at one own fiber: where its step goes on, the step over `below` is that step
with `below` under the next stack. -/
private def stepKeeps (f : F) (below : List P) : Bool :=
  match (f.step frames).fst with
  | .running next => ((f.under below).step frames).fst == .running (next.under below)
  | .finished _ => true

private def goesOn (f : F) : Bool :=
  match (f.step frames).fst with
  | .running _ => true
  | .finished _ => false

#guard (splits 3).all fun (above, below) => (owns above).all fun f => stepKeeps f below
-- Steps that go on and steps that finish are both in the sweep.
#guard ((splits 3).foldl (fun n (above, _) => n + ((owns above).filter goesOn).length) 0) == 342452
#guard ((splits 3).foldl (fun n (above, _) => n + ((owns above).filter (!goesOn ·)).length) 0) ==
  18668

/-! ### The region's end -/

/-- `RegionEnds` at one input, as a Boolean: the stack and the flag of the region's end, and the
pop of the fiber against the pop of the region's end. -/
private def endsAt {ν σ β ε δ ι α : Type} [DecidableEq ν] [DecidableEq σ] [DecidableEq β]
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (entryStack : List (Prim ν σ β ε δ ι α)) (entryFlag : Bool) (g : FrameFiber ν σ β ε δ ι α)
    (above : List (Prim ν σ β ε δ ι α)) (demand : Arm) (skip : Bool)
    (carried : Option (Cause ε δ ι α)) : Bool :=
  let ended := regionEnd (g.own above) entryStack demand skip carried
  let rest := ended.getCont demand skip ((g.own above).getCont demand skip carried).carriedCause
  ended.stack == entryStack && ended.interruptible == entryFlag &&
    (g.getCont demand skip carried).answer == rest.answer &&
    (g.getCont demand skip carried).fiber == rest.fiber &&
    (g.getCont demand skip carried).carriedCause == rest.carriedCause

/-- The fibers inside a region: both flags, a pending cause or none, a deferred interrupt or
none, over the stack `above ++ below`. -/
private def insides (above below : List P) : List F :=
  bools.flatMap fun flag => [none, some cause].flatMap fun pending =>
    bools.map fun deferred => ⟨.success 0, above ++ below, flag, pending, deferred⟩

/-- The pop of the own frames answers nothing. -/
private def unanswered (g : F) (above : List P) (demand : Arm) (skip : Bool)
    (carried : Option C) : Bool :=
  ((g.own above).getCont demand skip carried).answer == .empty

/-- The inputs of the sweep at which a region ends: the fiber holds the chain at a base, the
entry flag holds it over the frames under the region, and the pop of the own frames answers
nothing. -/
private def ending : List (Bool × F × List P × List P × Arm × Bool × Option C) :=
  (splits 3).flatMap fun (above, below) => (insides above below).flatMap fun g =>
    bools.flatMap fun base => bools.flatMap fun entry =>
      if chain base g.interruptible g.stack && chain base entry below then
        [Arm.contA, Arm.contE].flatMap fun d => bools.flatMap fun s =>
          [none, some cause].filterMap fun carried =>
            if unanswered g above d s carried then some (entry, g, above, below, d, s, carried)
            else none
      else []

-- `regionEnds_of_base`: at each such input the region ends at the entry's stack and at the
-- entry flag, and the pop of the fiber goes on as the pop of the region's end.
#guard ending.length == 37984
#guard ending.all fun (entry, g, above, below, d, s, carried) =>
  endsAt below entry g above d s carried
-- The check is not empty of regions that change the flag: at some inputs the fiber's flag at the
-- cut is not the entry flag, and the region's end still has the entry flag.
#guard (ending.filter fun (entry, g, _, _, _, _, _) => g.interruptible != entry).length == 5692

/-! ## The red controls of part A -/

/-! ### 1. The end is no cut between two steps -/

/-- The states of a frame run, the first one first. -/
private def trail : Nat → F → List F
  | 0, f => [f]
  | n + 1, f =>
    match (f.step frames).fst with
    | .running next => f :: trail n next
    | .finished _ => [f]

/-- A region over the entry stack `[value]`, whose body is a handler over a value. -/
private def handled : F := ⟨handler, [value], true, none, false⟩

-- The stacks of the run have lengths 1, 2 and 0. The handler passes inside the pop that delivers
-- the value, so no state after the entry has the entry's stack.
#guard (trail 5 handled).map (fun f => f.stack.length) == [1, 2, 0]
#guard ((trail 5 handled).drop 1).all fun f => f.stack != [value]
-- The region's end is inside the second step: the pop of the own frame `[handler]` answers
-- nothing, and the region's end has the entry's stack and the entry flag.
#guard (trail 5 handled)[1]?.map (fun g => (g.stack, unanswered g [handler] .contA false none)) ==
  some ([handler, value], true)
#guard ((trail 5 handled)[1]?.map fun g => endsAt [value] true g [handler] .contA false none) ==
  some true

/-! ### 2. A pop that an own frame answers -/

/-- A masked fiber over a value frame and a restoring frame. The value frame answers a value. -/
private def answering : F := ⟨.success 0, [value, .setInterruptible true], false, none, false⟩

-- The pop of the own frames answers, so the region has not ended. The pop's fiber is masked,
-- over one own frame, and the entry flag is true.
#guard chain true false [value, .setInterruptible true]
#guard !unanswered answering [value, .setInterruptible true] .contA false none
#guard (regionEnd (answering.own [value, .setInterruptible true]) [handler] .contA false).stack ==
  [.setInterruptible true, handler]
#guard !endsAt [handler] true ({ answering with stack := answering.stack ++ [handler] })
  [value, .setInterruptible true] .contA false none

/-- **The unanswered pop is needed.** Without it the bracket's statement is false: an own frame
answers, and the region's end is no end. -/
theorem ends_needs_unanswered :
    ¬ ∀ (base : Bool) (entry g : F) (above : List P) (demand : Arm) (skip : Bool)
      (carried : Option C), g.stack = above ++ entry.stack →
        MaskChain base entry.interruptible entry.stack → MaskChain base g.interruptible g.stack →
          RegionEnds entry g above demand skip carried := by
  intro h
  have ends := h true ⟨.success 0, [handler], true, none, false⟩
    ⟨.success 0, [value, .setInterruptible true, handler], false, none, false⟩
    [value, .setInterruptible true] .contA false none rfl (by decide) (by decide)
  exact absurd ends.flag (by decide)

/-! ### 3. The own frames at the fiber's base, and two bases -/

-- A fiber at base true, inside an `uninterruptible` region: the entry's stack holds the frame
-- that returns true, and the entry flag is false. With no own frame, the chain over the own
-- frames holds at the entry flag, and not at the fiber's base.
#guard chain true false [.setInterruptible true]
#guard chain false false ([] : List P) && !chain true false ([] : List P)

/-- **The entry flag is the base of the own frames, and the fiber's base is not.** -/
theorem above_at_entry_not_base :
    ¬ ∀ (base entry flag : Bool) (above below : List P), MaskChain base flag (above ++ below) →
      MaskChain base entry below → MaskChain base flag above := by
  intro h
  exact absurd (h true false false [] [.setInterruptible true] (by decide) (by decide))
    (by decide)

/-- **One base is needed.** Two chains at two bases give no chain of the own frames at the entry
flag. -/
theorem above_needs_one_base :
    ¬ ∀ (base base' entry flag : Bool) (above below : List P),
      MaskChain base flag (above ++ below) → MaskChain base' entry below →
        MaskChain entry flag above := by
  intro h
  exact absurd (h true false false true [] [] (by decide) (by decide)) (by decide)

/-! ### 4. The ending step with its code unchanged -/

/-- A typed failure. -/
private def failing : C := Cause.fail 7

/-- An interruptible fiber with an interrupt pending, whose code is a typed failure, over one
handler: the failure path skips the handler, and it rewrites the carried cause. -/
private def skipping : F := ⟨.failure failing, [handler], true, some cause, false⟩

/-- The frames under it: a frame that masks again, and a handler that answers then. -/
private def under9 : List P := [.setInterruptible false, .onFailure (.success 4) 6]

private def finishedWith (f : F) : Option (Exit Nat Nat Nat Nat Nat) :=
  match (f.step frames).fst with
  | .running _ => none
  | .finished exit => some exit

-- The own fiber's step finishes: the region ends at this step.
#guard (finishedWith skipping).isSome
-- A dropped candidate: the step that ends a region is the step of the region's end, with its
-- code unchanged. It is false here: the skipped handler rewrote the carried cause, and the
-- handler under the region answers the rewritten one.
#guard ((skipping.under under9).step frames).fst !=
  (((frameExitState skipping).under under9).step frames).fst
-- With the delivered exit as the code, the two steps agree on this input. No theorem states it.
#guard (finishedWith skipping).map (fun exit =>
  ((skipping.under under9).step frames).fst ==
    (({ (frameExitState skipping).under under9 with current := Prim.ofExit exit } : F).step
      frames).fst) == some true
-- The pop's form holds, as the bracket states it.
#guard endsAt under9 true (skipping.under under9) [handler] .contE true (some failing)

/-! # Part B: the machine -/

private abbrev M := RunMachine Nat Nat Nat Nat Nat Nat Nat Unit Unit
private abbrev R := RunFiber Nat Nat Nat Nat Nat Nat Nat Unit
private abbrev D := RunDecision Nat Nat Nat Nat Nat Nat Nat
private abbrev K := Cmd Nat Nat Nat Nat Nat Nat Nat

/-- The invariant at a table, decided by the law module's instance. -/
private def runs (bases : List Bool) (m : M) : Bool := decide (MaskRuns bases m)

/-- A machine with one fiber, at id 0, which started at flag true. -/
private def single (frame : F) (exit : Option (Exit Nat Nat Nat Nat Nat)) : M :=
  { (RunMachine.empty () : M) with
    fibers := [{ (RunFiber.make ⟨0⟩ (.success 0) true (1000000, true) () : R) with
      frame := frame, exit := exit }]
    nextId := 1 }

/-! ## A pair of cuts with two stacks, and a fiber that has exited at the second cut -/

/-- The entry: a live fiber at flag true over an empty stack. -/
private def atEntry : M := single ⟨.success 0, [], true, none, false⟩ none
/-- A cut inside an `uninterruptible` region: flag false, over the frame that returns true. -/
private def inRegion : M := single ⟨.success 0, [.setInterruptible true], false, none, false⟩ none
/-- A second cut whose fiber has exited: flag false over the entry's stack. -/
private def exited : M := single ⟨.success 0, [], false, none, false⟩ (some (.success 0))

#guard runs [true] atEntry && runs [true] inRegion && runs [true] exited

-- A pair of cuts with two stacks has two flags: the flag at a cut inside a region is not the
-- entry flag. The region's end has it.
#guard atEntry.fibers.map (fun f => (f.frame.interruptible, f.frame.stack.length)) == [(true, 0)]
#guard inRegion.fibers.map (fun f => (f.frame.interruptible, f.frame.stack.length)) == [(false, 1)]
#guard inRegion.fibers.all fun g =>
  unanswered g.frame [.setInterruptible true] .contA false none &&
    endsAt [] true g.frame [.setInterruptible true] .contA false none

/-- **The stack's premise is needed for one flag.** Two cuts of one run with two stacks have two
flags: the first fact is about the region's end, and not about each cut inside the region. -/
theorem flag_needs_stack :
    ¬ ∀ (bases bases' : List Bool) (m m' : M) (f g : R), MaskRuns bases m → MaskRuns bases' m' →
      bases <+: bases' → f ∈ m.fibers → g ∈ m'.fibers → g.id = f.id → f.exit = none →
        g.exit = none → f.frame.interruptible = g.frame.interruptible := by
  intro h
  have flags := h [true] [true] atEntry inRegion _ _ (by decide) (by decide)
    (List.prefix_refl _) (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl) rfl rfl rfl
  exact absurd flags (by decide)

/-- The bracket at that pair: the region's end has the entry's stack and the entry flag. -/
example : ∀ f ∈ atEntry.fibers, ∀ g ∈ inRegion.fibers,
    RegionEnds f.frame g.frame [.setInterruptible true] .contA false none := by
  intro f mem g mem'
  have same := List.mem_singleton.mp mem
  have same' := List.mem_singleton.mp mem'
  subst same
  subst same'
  exact MaskRuns.bracket (bases := [true]) (bases' := [true]) (m := atEntry) (m' := inRegion)
    (by decide) (by decide) (List.prefix_refl _) (List.mem_singleton.mpr rfl)
    (List.mem_singleton.mpr rfl) rfl rfl rfl rfl .contA false none (by decide)

-- A fiber that has exited at the second cut: it has the entry's stack, and another flag.
#guard exited.fibers.all fun g => g.exit.isSome && g.frame.stack == [] &&
  unanswered g.frame [] .contA false none && !endsAt [] true g.frame [] .contA false none

/-- **A live fiber at the second cut is needed.** Without it the bracket's statement is false: an
exited fiber has the entry's stack and another flag. The invariant ranges over the live
fibers. -/
theorem bracket_needs_live :
    ¬ ∀ (bases bases' : List Bool) (m m' : M) (f g : R) (above : List P) (demand : Arm)
      (skip : Bool) (carried : Option C), MaskRuns bases m → MaskRuns bases' m' →
      bases <+: bases' → f ∈ m.fibers → g ∈ m'.fibers → g.id = f.id → f.exit = none →
        g.frame.stack = above ++ f.frame.stack →
          ((g.frame.own above).getCont demand skip carried).answer = ContAnswer.empty →
            RegionEnds f.frame g.frame above demand skip carried := by
  intro h
  have ends := h [true] [true] atEntry exited _ _ [] .contA false none (by decide) (by decide)
    (List.prefix_refl _) (List.mem_singleton.mpr rfl) (List.mem_singleton.mpr rfl) rfl rfl rfl
    (by decide)
  exact absurd ends.flag (by decide)

/-! ## A run that steps an exited fiber

The toy interpreter and the run of `Test/Machine/MaskRuns.lean`. Fiber 0 forks fiber 1, then it
hosts race 0. Fiber 1 awaits fiber 0, and then it evaluates the registration of race 0.
`Cmd.registrationDone` continues the race's host, so the command loop steps fiber 0 after its
exit. No compiled program has such an interpreter: only a race's host evaluates its
registration there, and `Program.stepped_live` is the theorem. -/

private def waiter : P := .onSuccess (.suspend 100) 20

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

/-- The cuts of one command loop: each machine with its pending commands, before each command,
up to a budget. -/
private def toyCuts : Nat → M → List K → List (M × List K)
  | 0, m, cmds => [(m, cmds)]
  | _ + 1, m, [] => [(m, [])]
  | n + 1, m, c :: rest =>
    (m, c :: rest) ::
      (if m.stuck.isSome then [] else
        let next := driveStep toy m c rest
        toyCuts n next.1 next.2)

/-- The cuts of a `fire`: each task's command loop, in order, as `fireState` runs them. -/
private def fireCuts (fuel : Nat) (m : M) (owner : FiberId) : List (M × List K) :=
  match m.fiber? owner with
  | none => []
  | some o =>
    ((o.dispatcher.drain).1.foldl (fun (acc : List (M × List K) × M) task =>
      let cuts := toyCuts fuel (acc.2.emit [RunEvent.ranTask owner task]) (taskCmds task)
      (acc.1 ++ cuts, (cuts.getLast?.map (·.1)).getD acc.2))
      ([], (m.update { o with dispatcher := (o.dispatcher.drain).2 }).disarm owner)).1

private def rooted (program : P) : M :=
  { (RunMachine.empty () : M) with
    fibers := [RunFiber.make ⟨0⟩ program true (toy.budgetOf ()) ()]
    nextId := 1 }

private def hosts : P := .onSuccess (.withFiber 1) 10

/-- The machine after the root's evaluation. -/
private def afterEvaluate : M := (stepDecisionState toy 400 (rooted hosts) (.evaluate ⟨0⟩)).1

/-- What a fiber shows: its id, whether it has exited, its flag and its stack's length. -/
private def seen (m : M) : List (Nat × Bool × Bool × Nat) :=
  m.fibers.map fun f => (f.id.value, f.exit.isSome, f.frame.interruptible, f.frame.stack.length)

/-- The fiber that a command steps. It is `Machine.Steps`, as a function. -/
private def steppedBy {ν σ β ε δ ι α κ : Type} : Cmd ν σ β ε δ ι α κ → Option FiberId
  | Cmd.loop id _ => some id
  | Cmd.deliver id _ => some id
  | _ => none

/-- A pending command of the cut steps a fiber that has exited. -/
private def stepsExited (cut : M × List K) : Bool :=
  cut.2.any fun c => match steppedBy c with
    | some id => ((cut.1.fiber? id).map (·.exit.isSome)).getD false
    | none => false

-- The tracer reaches the machine that the decision reaches.
#guard (fireCuts 400 afterEvaluate ⟨0⟩).getLast?.map (fun cut => seen cut.1) ==
  some (seen (stepDecisionState toy 400 afterEvaluate (.fire ⟨0⟩)).1)
-- The second decision's command loops have 17 cuts. At two of them a pending command steps
-- fiber 0, which has exited: once at its start flag over an empty stack, and once masked over
-- the frame that returns true.
#guard (fireCuts 400 afterEvaluate ⟨0⟩).length == 17
#guard ((fireCuts 400 afterEvaluate ⟨0⟩).filter stepsExited).map (fun cut => seen cut.1) ==
  [[(0, true, true, 0), (1, false, true, 0), (2, true, true, 0)],
   [(0, true, false, 1), (1, false, true, 0), (2, true, true, 0)]]
-- The first decision steps live fibers only.
#guard (toyCuts 400 (rooted hosts) [Cmd.evaluate ⟨0⟩, Cmd.drainDue]).all (!stepsExited ·)
-- At the reached machine fiber 0 has exited, at flag false over an empty stack. It started at
-- flag true over an empty stack: the entry's stack, and another flag.
#guard seen (rooted hosts) == [(0, false, true, 0)]
#guard seen (stepDecisionState toy 400 afterEvaluate (.fire ⟨0⟩)).1 ==
  [(0, true, false, 0), (1, false, true, 0), (2, true, true, 0)]
-- The invariant holds at each cut of that loop: it ranges over the live fibers.
#guard (fireCuts 400 afterEvaluate ⟨0⟩).all fun cut =>
  runs ([true, true, true].take cut.1.nextId) cut.1

/-! # Part C: compiled programs -/

section Compiled

open Effect4.Program Effect4.Program.Authoring Effect4.Program.Guard Test.Program.MaskContract

private abbrev NF := FrameFiber EffName EffThunk Val Err Defect FiberId Ann

/-- The cuts of one command loop of a compiled program: each machine with its pending commands,
before each command, up to a budget. -/
private def loopCuts (p : NativeEff) :
    Nat → NativeMachine → List NCmd → List (NativeMachine × List NCmd)
  | 0, m, cmds => [(m, cmds)]
  | _ + 1, m, [] => [(m, [])]
  | n + 1, m, c :: rest =>
    (m, c :: rest) ::
      (if m.stuck.isSome then [] else
        let next := driveStep (evaluator := evaluatorFor p []) (interpOf p []) m c rest
        loopCuts p n next.1 next.2)

/-- The cuts of the root's first command loop: the loaded machine under
`[Cmd.evaluate root, Cmd.drainDue]`. -/
private def cutsOf (src : Src NativeOp) (n : Nat) : List (NativeMachine × List NCmd) :=
  match buildOf (mk src) with
  | none => []
  | some p => loopCuts p n (Api.load p fuel []) [Cmd.evaluate Api.root, Cmd.drainDue]

/-- The decision cut of the same run: the machine after the root's evaluation. -/
private def decided (src : Src NativeOp) : Option NativeMachine :=
  (buildOf (mk src)).map fun p => (Api.replay p fuel [Api.evaluate] [] [] fuel).machine

/-- The saved flags of a stack, from the top: the flags of its restoring frames. -/
private def savedFlags (stack : List NCode) : List Bool :=
  stack.filterMap fun p => match p with
    | Prim.setInterruptible saved => some saved
    | _ => none

/-- What a fiber shows: its id, whether it has exited, its flag, its saved flags from the top
and its stack's length. -/
private def shown (m : NativeMachine) : List (Nat × Bool × Bool × List Bool × Nat) :=
  m.fibers.map fun f =>
    (f.id.value, f.exit.isSome, f.frame.interruptible, savedFlags f.frame.stack,
      f.frame.stack.length)

/-- The frame of a fiber that the cut reads: a pending command steps it. -/
private def readAt (cut : NativeMachine × List NCmd) (id : Nat) : Option NF :=
  if cut.2.any (fun c => steppedBy c == some ⟨id⟩) then (cut.1.fiber? ⟨id⟩).map (·.frame)
  else none

/-- At a cut each fiber that a pending command steps is live: `Program.stepped_live`. -/
private def steppedLive (cut : NativeMachine × List NCmd) : Bool :=
  cut.2.all fun c => match steppedBy c with
    | some id => ((cut.1.fiber? id).map (·.exit.isNone)).getD true
    | none => true

/-- The own frames of a stack over an entry's stack, where the stack has that shape. -/
private def aboveOf (stack below : List NCode) : Option (List NCode) :=
  if below.length ≤ stack.length && stack.drop (stack.length - below.length) == below then
    some (stack.take (stack.length - below.length))
  else none

/-- The pop that delivers a fiber's code, where the code is an exit. -/
private def demandOf (code : NCode) : Option (Effect4.Arm × Bool × Option CauseV) :=
  match code with
  | .success _ => some (Effect4.Arm.contA, false, none)
  | .failure cause => some (Effect4.Arm.contE, true, some cause)
  | _ => none

/-- Each pair of an earlier and a later cut, with a fiber that both read. The later one is
inside the region of the earlier one: its stack is own frames over the earlier one's stack. -/
private def pairs (cuts : List (NativeMachine × List NCmd)) (ids : List Nat) :
    List (NF × NF × List NCode) :=
  ((List.range cuts.length).flatMap fun i => (List.range cuts.length).flatMap fun j =>
    if i ≤ j then
      ids.filterMap fun id =>
        match cuts[i]?.bind (readAt · id), cuts[j]?.bind (readAt · id) with
        | some f, some g => (aboveOf g.stack f.stack).map fun above => (f, g, above)
        | _, _ => none
    else [])

/-- The pairs at which the region ends: the later cut's code is an exit, and the pop of the own
frames that delivers it answers nothing. -/
private def endings (cuts : List (NativeMachine × List NCmd)) (ids : List Nat) :
    List (NF × NF × List NCode × Effect4.Arm × Bool × Option CauseV) :=
  (pairs cuts ids).filterMap fun (f, g, above) =>
    (demandOf g.current).bind fun (d, s, carried) =>
      if ((g.own above).getCont d s carried).answer == .empty then some (f, g, above, d, s, carried)
      else none

/-- The checks of one run, at one table of start flags: the second fact at each cut, the chain's
invariant at each cut, the chain of the own frames at the entry flag on each pair, and the
bracket at each ending. -/
private def holdsOn (cuts : List (NativeMachine × List NCmd)) (bases : List Bool)
    (ids : List Nat) : Bool :=
  cuts.all steppedLive &&
    (cuts.all fun cut => decide (MaskRuns (bases.take cut.1.nextId) cut.1)) &&
    ((pairs cuts ids).all fun (f, g, above) =>
      decide (MaskChain f.interruptible g.interruptible above)) &&
    ((endings cuts ids).all fun (f, g, above, d, s, carried) =>
      endsAt f.stack f.interruptible g above d s carried)

/-! ## A region that changes no flag, a body that changes the flag, a nested region

The root masks itself. Inside, a second `uninterruptible` region changes no flag and pushes no
frame. Its body opens an `interruptible` region, which changes the flag and returns, and then it
reads the flag. After the inner region the root reads the flag again. -/

private def nested : Src NativeOp := eff do
  let a ← uninterruptible (eff do
    let b ← uninterruptible (eff do
      let x ← interruptible flag
      let y ← flag
      return tuple [x, y])
    let c ← flag
    return tuple [b, c])
  let d ← flag
  return tuple [a, d]

-- The flags that the program reads: true inside the `interruptible` region, false after it,
-- false after the inner region, and true after the outer one.
#guard exitOf nested ==
  some (.success (.list [.list [.list [open_, masked], masked], open_]))
-- The root's first command loop has 25 cuts, and the tracer reaches the decision's machine.
#guard (cutsOf nested 200).length == 25
#guard (cutsOf nested 200).getLast?.map (fun cut => shown cut.1) == (decided nested).map shown
-- The second fact, the invariant, the chain of the own frames and the bracket, on each cut and
-- each pair of cuts.
#guard holdsOn (cutsOf nested 200) [true] [0]
-- The checks are not empty.
#guard (pairs (cutsOf nested 200) [0]).length == 96
#guard (endings (cutsOf nested 200) [0]).length == 20
-- The inner region's entry: flag false over the entry's stack, which holds the frame that
-- returns true. Inside it a cut has flag true, over the frame that returns false.
#guard ((cutsOf nested 200).map fun cut => shown cut.1).contains [(0, false, false, [true], 3)]
#guard ((cutsOf nested 200).map fun cut => shown cut.1).contains
  [(0, false, true, [false, true], 5)]
-- A region that changes the flag ends inside a pop: at some ending the later cut's flag is not
-- the entry flag, and the region's end has the entry flag.
#guard ((endings (cutsOf nested 200) [0]).filter fun (f, g, _, _, _, _) =>
  f.interruptible != g.interruptible).length == 3
-- A pair of cuts with two stacks has two flags.
#guard (pairs (cutsOf nested 200) [0]).any fun (f, g, above) =>
  !above.isEmpty && f.interruptible != g.interruptible
-- The decision cut of the run shows no fiber inside a region: the root has exited there. So a
-- journal's rows do not show this region's entry or its end.
#guard (decided nested).map shown == some [(0, true, true, [], 0)]
#guard ((cutsOf nested 200).filter fun cut => (readAt cut 0).any (!·.stack.isEmpty)).length == 17

/-! ## A region whose body is interrupted

The root forks a child that starts at once. The child masks itself, opens an `interruptible`
region and waits there. The root interrupts it. The park's finalizer masks the child and runs
its cancel, and then the failure goes on. Its pop passes each frame of the stack: a restoring
frame's replacement is discarded while the fiber is interrupted. So one pop ends the inner
region, the outer region and the fiber. -/

private def interrupted : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let child ← fork (uninterruptible (eff do
      let _ ← interruptible (Deferred.await d)
      return unit))
    ⟨true, false, .interruptible⟩
  let _ ← withFiber (Action.interrupt child)
  let e ← await child
  return app "causeIsInterrupt" [e]

#guard exitOf interrupted == some (.success (.bool true))
#guard (cutsOf interrupted 400).getLast?.map (fun cut => shown cut.1) ==
  (decided interrupted).map shown
-- Both fibers started at flag true. The checks hold on each cut and each pair, for both fibers.
#guard holdsOn (cutsOf interrupted 400) [true, true] [0, 1]
#guard (endings (cutsOf interrupted 400) [1]).length == 12
-- The second fact alone, at each cut: each fiber that a pending command steps is live. At some
-- cuts two fibers have a pending step: the child runs, and the root's next step waits.
#guard (cutsOf interrupted 400).all steppedLive
#guard ((cutsOf interrupted 400).filter fun cut =>
  (readAt cut 0).isSome && (readAt cut 1).isSome).length == 4
-- The child waits inside the `interruptible` region: flag true, over the park's finalizer, the
-- frame that masks again, the body's frame and the frame that returns true.
#guard ((cutsOf interrupted 400).map fun cut => shown cut.1).contains
  [(0, false, true, [], 1), (1, false, true, [false, true], 4)]
-- The entry of the `interruptible` region: flag false, over two frames. After the interrupt a
-- cut has a failure as its code, and its own frames save true and false: the park's finalizer
-- pushed the first. The failure's pop passes both, so the region ends inside the pop, at the
-- entry flag false.
#guard ((endings (cutsOf interrupted 400) [1]).filter fun (f, g, above, d, _, _) =>
  d == Effect4.Arm.contE && !f.interruptible && f.stack.length == 2 &&
    savedFlags f.stack == [true] && !g.interruptible &&
    savedFlags above == [true, false]).length == 1
-- The same pop ends the outer region and the child's whole run: an ending has the child's start
-- stack and its start flag as its entry, with all four frames as own frames.
#guard ((endings (cutsOf interrupted 400) [1]).filter fun (f, _, above, d, _, _) =>
  d == Effect4.Arm.contE && f.interruptible && f.stack.isEmpty && above.length == 4).length == 1

/-! ## The mask's derived form under a masked caller

Under a masked caller the form changes no flag and pushes no frame, and its restore is the
identity. Its body opens an `interruptible` region at the restore site. After the form the
caller reads the flag: it is masked, as at the form's entry. -/

private def formUnderMask : Src NativeOp := eff do
  uninterruptible (eff do
    let x ← uninterruptibleMaskWith fun restore => restore (interruptible flag)
    let z ← flag
    return tuple [x, z])

#guard exitOf formUnderMask == some (.success (.list [open_, masked]))
#guard holdsOn (cutsOf formUnderMask 200) [true] [0]
#guard (endings (cutsOf formUnderMask 200) [0]).length == 13
#guard (cutsOf formUnderMask 200).getLast?.map (fun cut => shown cut.1) ==
  (decided formUnderMask).map shown

/-! ## The theorems in use -/

/-- `Machine.Steps` is the function that the controls read. -/
example (id fiber : FiberId) (y : Bool) :
    Steps id (Cmd.loop fiber y : NCmd) ↔ steppedBy (Cmd.loop fiber y : NCmd) = some id :=
  ⟨fun h => congrArg some h, fun h => Option.some.inj h⟩

example (id fiber : FiberId) (y : Bool) :
    Steps id (Cmd.deliver fiber y : NCmd) ↔ steppedBy (Cmd.deliver fiber y : NCmd) = some id :=
  ⟨fun h => congrArg some h, fun h => Option.some.inj h⟩

/-- Each cut of the root's first command loop is a cut, at each budget and with no premise on
the program. -/
example (p : NativeEff) (n : Nat) :
    ∃ bases, [true] <+: bases ∧ LoopCut p [] bases
      (driveState (evaluator := evaluatorFor p []) (interpOf p []) n (Api.load p fuel [])
        [Cmd.evaluate Api.root, Cmd.drainDue]).1
      (driveState (evaluator := evaluatorFor p []) (interpOf p []) n (Api.load p fuel [])
        [Cmd.evaluate Api.root, Cmd.drainDue]).2 :=
  (LoopCut.load p [] fuel []).drive n

/-- The second fact at such a cut: a fiber that a pending command steps has not exited. -/
example (p : NativeEff) (bases : List Bool) (m : NativeMachine) (cmds : List NCmd)
    (cut : LoopCut p [] bases m cmds) (id : FiberId) (y : Bool) (pending : Cmd.loop id y ∈ cmds)
    (f : NFiber) (found : m.fiber? id = some f) : f.exit = none :=
  stepped_live p [] cut.state cut.queue pending rfl found

/-- The bracket between two cuts of one command loop, each with a pending step of the fiber. It
takes no premise on an exit. -/
example (p : NativeEff) (bases bases' : List Bool) (m m' : NativeMachine)
    (cmds cmds' : List NCmd) (entry : LoopCut p [] bases m cmds)
    (later : LoopCut p [] bases' m' cmds') (grown : bases <+: bases') (id : FiberId)
    (y y' : Bool) (pending : Cmd.loop id y ∈ cmds) (pending' : Cmd.loop id y' ∈ cmds')
    (f g : NFiber) (found : m.fiber? id = some f) (found' : m'.fiber? id = some g)
    (above : List NCode) (inside : g.frame.stack = above ++ f.frame.stack) (value : Val)
    (unanswered : ((g.frame.own above).getCont Effect4.Arm.contA false none).answer =
      ContAnswer.empty) (_code : g.frame.current = Prim.success value) :
    (regionEnd (g.frame.own above) f.frame.stack Effect4.Arm.contA false).interruptible =
      f.frame.interruptible :=
  (compiled_region_bracket p [] entry later grown pending pending' rfl rfl found found' inside
    Effect4.Arm.contA false none unanswered).flag

/-- The general form at the alphabets `Nat`. -/
private theorem atNat : RegionBracket Nat Nat Nat Nat Nat Nat Nat Unit Unit :=
  saved_mask_region_bracket Nat Nat Nat Nat Nat Nat Nat Unit Unit

example : ∀ (base entry flag : Bool) (above below : List P), MaskChain base flag (above ++ below) →
    MaskChain base entry below → MaskChain entry flag above :=
  atNat.chain

example : ∀ (interp : PrimInterp Nat Nat Nat Nat Nat Nat Nat) (f : F) (below : List P) (next : F),
    (f.step interp).fst = FrameStep.running next →
      ((f.under below).step interp).fst = FrameStep.running (next.under below) :=
  atNat.between

example : ∀ (bases bases' : List Bool) (m m' : M) (f g : R) (above : List P), MaskRuns bases m →
    MaskRuns bases' m' → bases <+: bases' → f ∈ m.fibers → g ∈ m'.fibers → g.id = f.id →
      f.exit = none → g.exit = none → g.frame.stack = above ++ f.frame.stack →
        MaskChain f.frame.interruptible g.frame.interruptible above :=
  atNat.inside

end Compiled

end Test.Machine.MaskBracket
