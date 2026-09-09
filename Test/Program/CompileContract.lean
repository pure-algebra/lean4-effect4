import Effect4.Program.Compile
import Effect4.Laws.Machine.Witnesses

/-!
# Compile contract — `Eff` programs through the frame machine, pinned

Plan: `docs/research/2026-09-04-eff-compile.md`. `src/Effect4/Program/Compile.lean` takes a
`NativeEff` and a `Point` to a primitive of the reference machine over the `EffName` /
`EffThunk` alphabet, and `interpOf root` gives those names their meaning by compiling the
subterm each point addresses. This battery runs compiled programs on explicit decision
tapes, in the idiom of `src/Effect4/Laws/Machine/Witnesses.lean`, and pins what the machine does.

Every program is also pinned well-typed (`typeOf nativeSignature`), except the two that are
deliberately ill-typed and pinned refused. Every helper below is structural, and every pin is
a `#guard`, so a pin is a finite probe of the compile at one tape and nothing more
(`AGENTS.md`). No helper touches a `String` or a rendering: the axiom gate holds
`Test.*` at `propext`/`Quot.sound`, and Lean's UTF-8 folds reach `Classical.choice`.

Two findings this battery made on 2026-09-04, both closed the same day and pinned below at
their sites (`finding A3-1`, `finding A3-2`):

* **A3-1** — `contEOf` sent `EffName.onCause p` to child `1`, `matchCause`'s *value* arm;
  the cause arm is child `2`. Fixed in `contEOf`.
* **A3-2** — a generator's else block is addressed `pc ++ [0, 1]`, and `splitPc` read the
  trailing `1` as a position, so leaving an else block (by its end or by `breakLoop`) lost
  control. Fixed by reading a program counter from the front (`walkPc`), where a descent is
  always `0` followed by the block selector.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Syntax.CompileContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## Harness

The witnesses' harness at the compile's alphabet: one root fiber over the empty store and the
empty context, a decision tape, and the trace projections the pins read. -/

abbrev MC := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev DC := RunDecision EffName EffThunk Val Err Defect FiberId Ann

/-- The fuel every pin runs with, both the compile's `Point.fuel` and the machine's.
Exhaustion is a live frontier (DB-04), never a failure. -/
def fuel : Nat := 400

/-- One root fiber `⟨0⟩` over `emptyCtx`, not yet evaluated, running the root program compiled
at `fuel` with `decisions` on its `choose` tape. `Witnesses.spawnRoot` with `RunFiber.make`,
at this alphabet. -/
def spawnTape (root : NativeEff) (decisions : List Bool) : MC :=
  { (RunMachine.empty Stores.empty : MC) with
    fibers := [RunFiber.make ⟨0⟩ (compile root fuel decisions) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

/-- The common case: no `choose` decisions. -/
def spawn (root : NativeEff) : MC := spawnTape root []

/-- Replay a decision tape against a root program compiled with `decisions` on its tape. All
three `ReplayResult` arms answer the machine; `stuckOf` and `replayArm` are how a pin observes
which arm it landed on. -/
def replayEffTape (root : NativeEff) (decisions : List Bool) (tape : List DC) : MC :=
  letI := evaluatorFor root
  match replayEval (interpOf root) fuel tape (spawnTape root decisions) with
  | ReplayResult.finished m => m
  | ReplayResult.frontier m => m
  | ReplayResult.stuck _ m => m

/-- The common case: no `choose` decisions. -/
def replayEff (root : NativeEff) (tape : List DC) : MC := replayEffTape root [] tape

/-- The arm the tape landed on: `0` finished, `1` frontier, `2` stuck. -/
def replayArm (root : NativeEff) (decisions : List Bool) (tape : List DC) : Nat :=
  letI := evaluatorFor root
  match replayEval (interpOf root) fuel tape (spawnTape root decisions) with
  | ReplayResult.finished _ => 0
  | ReplayResult.frontier _ => 1
  | ReplayResult.stuck _ _ => 2

/-- The exit of fiber `id`, if it has one; `none` is "still live". -/
def exitOf (m : MC) (id : Nat) : Option ExitV := (m.fiber? ⟨id⟩).bind RunFiber.exit

/-- Why the machine halted, if it did (M7). -/
def stuckOf (m : MC) : Option Stuck := m.stuck

/-- How many fibers the machine holds. -/
def fiberCount (m : MC) : Nat := m.fibers.length

/-- The Ref heap the run left behind. -/
def refsOf (m : MC) : List Val := m.state.refs

/-- How many `finalizerProgram` rows a fiber contributed. -/
def finalizerRuns (m : MC) (id : Nat) : Nat :=
  (m.trace.filter fun
    | RunEvent.finalizerProgram f _ _ => decide (f = ⟨id⟩)
    | _ => false).length

/-- The `interruptRecorded` rows, as (interruptor, target). -/
def interruptRows (m : MC) : List (Option Nat × Nat) :=
  m.trace.filterMap fun
    | RunEvent.interruptRecorded who target => some (who.map FiberId.value, target.value)
    | _ => none

/-- The `childrenInterrupted` rows of the exit path. -/
def childrenInterruptedRows (m : MC) : List (Nat × List Nat) :=
  m.trace.filterMap fun
    | RunEvent.childrenInterrupted parent children =>
      some (parent.value, children.map FiberId.value)
    | _ => none

/-- The `scopeLinked` (`0`) and `scopeClosedOnLink` (`1`) rows. -/
def scopeRows (m : MC) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.scopeLinked mode scope key fiber =>
      some [0, (match mode with
        | Supervision.ScopeMode.forkIn => 0
        | Supervision.ScopeMode.fiberRunIn => 1), scope, key, fiber.value]
    | RunEvent.scopeClosedOnLink scope fiber => some [1, scope, fiber.value]
    | _ => none

/-- The `raceLaunched` (`0`) and `raceSettled` (`2`) rows. -/
def raceRows (m : MC) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.raceLaunched race entrant => some [0, race, entrant.value]
    | RunEvent.raceSettled race _ => some [2, race]
    | _ => none

/-! ### Shared tape and fork vocabulary -/

def evaluateRoot : DC := RunDecision.evaluate ⟨0⟩
def fireRoot : DC := RunDecision.fire ⟨0⟩
def interruptChild : DC :=
  RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩

/-- `forkChild(..., { startImmediately: true })`. -/
def immediateChild : Supervision.ForkOptions := ⟨true, false, Supervision.MaskMode.inherit⟩

/-- The same, deferred onto the parent's dispatcher. -/
def deferredChild : Supervision.ForkOptions := ⟨false, false, Supervision.MaskMode.inherit⟩

/-- `forkScoped`'s daemon child. -/
def scopedChild : Supervision.ForkOptions := ⟨true, true, Supervision.MaskMode.inherit⟩

/-- `forkDaemon`'s child: untracked, so it outlives its parent's exit (R2-6). -/
def daemonChild : Supervision.ForkOptions := ⟨true, true, Supervision.MaskMode.inherit⟩

/-- The exit of `target` interrupted by `who` from `who`'s own stack: the `fiberInterrupt` /
`fiberInterruptAll` family carries the caller's stack annotations (R2-5). -/
def interruptedFrom (who target : FiberId) : ExitV :=
  Effect4.Machine.Witnesses.interruptedWith who target (stores.stackAnnotations who)

/-! ## Exits, thunks and sequencing -/

def pSucceed : NativeEff := .succeed (.lit (.nat 42))

#guard (typeOf nativeSignature pSucceed).isSome
#guard exitOf (replayEff pSucceed [evaluateRoot]) 0 = some (Exit.success (Val.nat 42))

/-- `Effect.flatMap(Effect.sync(() => 1), (a0) => Effect.succeed(succ(a0)))`. -/
def pBindSync : NativeEff :=
  .bind (.sync (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))

#guard (typeOf nativeSignature pBindSync).isSome
#guard exitOf (replayEff pBindSync [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

def pFail : NativeEff := .fail (.lit (.nat 7))

#guard (typeOf nativeSignature pFail).isSome
#guard exitOf (replayEff pFail [evaluateRoot]) 0
  = some (Exit.failure (Cause.fail (Err.tag 7)))

/-- `Effect.fail(pair("SqlError", "boom"))`: a pair of strings is the tagged package error of
DB-15; any other non-numeric value stays `boom`. -/
def pFailTagged : NativeEff :=
  .fail (.app "pair" (.cons (.lit (.str "SqlError")) (.cons (.lit (.str "boom")) .nil)))

#guard (typeOf nativeSignature pFailTagged).isSome
#guard exitOf (replayEff pFailTagged [evaluateRoot]) 0
  = some (Exit.failure (Cause.fail (Err.tagged "SqlError" "boom")))
#guard errOf (Val.list [Val.str "SqlError", Val.str "boom"]) = Err.tagged "SqlError" "boom"
#guard errOf (Val.list [Val.str "SqlError"]) = Err.boom
#guard errOf (Val.list [Val.str "SqlError", Val.nat 1]) = Err.boom
#guard errOf (Val.bool true) = Err.boom

/-- `Effect.catchCause`: the handler receives the reified cause and answers `9`. -/
def pCatch : NativeEff := .catchCause pFail (.succeed (.lit (.nat 9)))

#guard (typeOf nativeSignature pCatch).isSome
#guard exitOf (replayEff pCatch [evaluateRoot]) 0 = some (Exit.success (Val.nat 9))

/-- `Effect.matchCauseEffect` on a succeeding body: the value arm receives the value as
`a0`. -/
def pMatchValue : NativeEff :=
  .matchCause (.succeed (.lit (.nat 4))) (.succeed (.app "succ" (.cons (.var 0) .nil)))
    (.succeed (.lit (.nat 2)))

#guard (typeOf nativeSignature pMatchValue).isSome
#guard exitOf (replayEff pMatchValue [evaluateRoot]) 0 = some (Exit.success (Val.nat 5))

/-- `Effect.matchCauseEffect` on a failing body: the cause arm should run. -/
def pMatchCause : NativeEff :=
  .matchCause pFail (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))

#guard (typeOf nativeSignature pMatchCause).isSome

-- finding A3-1 (closed): `matchCause (fail 7) (succeed 1) (succeed 2)` runs the cause arm.
#guard exitOf (replayEff pMatchCause [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

/-- The same body under a cause arm that reads the reified cause as `a0`: the arm the machine
runs binds the reified cause either way, which is what makes finding A3-1 observable at all —
`succeed (var 0)` answers the cause value from *both* arms. -/
def pMatchCauseReified : NativeEff :=
  .matchCause pFail (.succeed (.var 0)) (.succeed (.var 0))

#guard (typeOf nativeSignature pMatchCauseReified).isSome
#guard exitOf (replayEff pMatchCauseReified [evaluateRoot]) 0
  = some (Exit.success (Val.exitErr (Cause.fail (Err.tag 7))))

/-- `Effect.exit`: the body's failed exit becomes an ordinary value. -/
def pExit : NativeEff := .exit pFail

#guard (typeOf nativeSignature pExit).isSome
#guard exitOf (replayEff pExit [evaluateRoot]) 0
  = some (Exit.success (Val.exitErr (Cause.fail (Err.tag 7))))

/-- `Effect.onExit` whose finalizer performs `Ref.update(cell, incr)` on a cell made
earlier, then reads the cell back. -/
def pOnExit : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.onExit (.succeed (.lit (.nat 1)))
              (.perform (.refUpdate FnName.incr) (.var 0)))
      (.perform .refGet (.var 0)))

#guard (typeOf nativeSignature pOnExit).isSome
#guard exitOf (replayEff pOnExit [evaluateRoot]) 0 = some (Exit.success (Val.nat 1))
#guard finalizerRuns (replayEff pOnExit [evaluateRoot]) 0 = 1
#guard refsOf (replayEff pOnExit [evaluateRoot]) = [Val.nat 1]

/-- `Effect.failCause(Cause.die(3))`. -/
def pDie : NativeEff := .failCause (.die (.lit (.nat 3)))

#guard (typeOf nativeSignature pDie).isSome
#guard exitOf (replayEff pDie [evaluateRoot]) 0
  = some (Exit.failure (Cause.die (Defect.user 3)))

/-! ## Refs -/

/-- `Ref.make(5)`, `Ref.set(ref, 7)`, `Ref.get(ref)`. -/
def pRefSet : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 5)))
    (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
      (.perform .refGet (.var 0)))

#guard (typeOf nativeSignature pRefSet).isSome
#guard exitOf (replayEff pRefSet [evaluateRoot]) 0 = some (Exit.success (Val.nat 7))

/-- `Ref.make(5)`, `Ref.update(ref, incr)`, `Ref.get(ref)`. -/
def pRefUpdate : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 5)))
    (.bind (.perform (.refUpdate FnName.incr) (.var 0)) (.perform .refGet (.var 0)))

#guard (typeOf nativeSignature pRefUpdate).isSome
#guard exitOf (replayEff pRefUpdate [evaluateRoot]) 0 = some (Exit.success (Val.nat 6))

/-- `Ref.modify(ref, takeAndBump)` answers the old value and leaves the bumped one. -/
def pRefModify : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 5)))
    (.perform (.refModify FnName.takeAndBump) (.var 0))

#guard (typeOf nativeSignature pRefModify).isSome
#guard exitOf (replayEff pRefModify [evaluateRoot]) 0 = some (Exit.success (Val.nat 5))
#guard refsOf (replayEff pRefModify [evaluateRoot]) = [Val.nat 6]

/-! ## Deferred: W4's shape

The parent makes a Deferred, forks a child that awaits it, completes it with `7`, and joins
the child. The completion resumes the waiter inside the completing `sync` (M1), so the join
finds the child already exited. -/

def pDeferred : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.callback .deferredAwait (.var 0)) immediateChild))
      (.bind (.perform .deferredSucceed
                (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
        (.awaitFiber (.var 1) Supervision.ObserverMode.joinEffect)))

#guard (typeOf nativeSignature pDeferred).isSome
#guard exitOf (replayEff pDeferred [evaluateRoot]) 1 = some (Exit.success (Val.nat 7))
#guard exitOf (replayEff pDeferred [evaluateRoot]) 0 = some (Exit.success (Val.nat 7))
#guard fiberCount (replayEff pDeferred [evaluateRoot]) = 2

/-! ## Fork and join: W1's shape -/

/-- A deferred-start fork joined by the parent; the tape's `fire` starts the child. -/
def pForkJoin : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 42))) deferredChild))
    (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect)

#guard (typeOf nativeSignature pForkJoin).isSome
#guard exitOf (replayEff pForkJoin [evaluateRoot, fireRoot]) 0
  = some (Exit.success (Val.nat 42))
#guard exitOf (replayEff pForkJoin [evaluateRoot, fireRoot]) 1
  = some (Exit.success (Val.nat 42))
#guard fiberCount (replayEff pForkJoin [evaluateRoot, fireRoot]) = 2

-- The cross-check: the compiled `Eff` program and `Deep.Witnesses`' hand-built `ProgName`
-- program reach the same exit on the same tape.
#guard exitOf (replayEff pForkJoin [evaluateRoot, fireRoot]) 0
  = Effect4.Machine.Witnesses.exitOf Effect4.Machine.Witnesses.w1DeferredJoin 0

/-- `Fiber.await` on a failing child: the exit is a *value*, so the parent succeeds. -/
def pAwaitFailing : NativeEff :=
  .bind (.withFiber (.fork pFail immediateChild))
    (.awaitFiber (.var 0) Supervision.ObserverMode.awaitValue)

#guard (typeOf nativeSignature pAwaitFailing).isSome
#guard exitOf (replayEff pAwaitFailing [evaluateRoot]) 0
  = some (Exit.success (Val.exitErr (Cause.fail (Err.tag 7))))

/-- `Fiber.join` on the same child: the exit is an *effect*, so the parent fails. -/
def pJoinFailing : NativeEff :=
  .bind (.withFiber (.fork pFail immediateChild))
    (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect)

#guard (typeOf nativeSignature pJoinFailing).isSome
#guard exitOf (replayEff pJoinFailing [evaluateRoot]) 0
  = some (Exit.failure (Cause.fail (Err.tag 7)))

/-! ## `raceAll`: W3's `successThenSecond`

The first entrant's success settles the race and the second is never forked (the register
loop breaks once done, `:1527`; R2-11): two fibers, nothing interrupted. -/

def pRace : NativeEff :=
  .withFiber (.raceAll (.cons (.succeed (.lit (.nat 1)))
    (.cons (.succeed (.lit (.nat 2))) .nil)))

#guard (typeOf nativeSignature pRace).isSome
#guard exitOf (replayEff pRace [evaluateRoot]) 0 = some (Exit.success (Val.nat 1))
#guard raceRows (replayEff pRace [evaluateRoot]) = [[0, 0, 1], [2, 0]]
#guard fiberCount (replayEff pRace [evaluateRoot]) = 2
#guard interruptRows (replayEff pRace [evaluateRoot]) = []
#guard exitOf (replayEff pRace [evaluateRoot]) 2 = none

/-! ## The children middleware: W5's shape

A parent forks a child parked on the `await` of a Deferred nobody completes, then succeeds.
The non-daemon `fork` latches the interrupt-children middleware itself (R2-6), so the
parent's exit interrupts the child whether or not the tape installs it. -/

def pMiddleware : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.callback .deferredAwait (.var 0)) immediateChild))
      (.succeed (.lit .unit)))

#guard (typeOf nativeSignature pMiddleware).isSome

def middlewareTape : List DC := [RunDecision.installMiddleware, evaluateRoot]

#guard exitOf (replayEff pMiddleware middlewareTape) 0 = some (Exit.success Val.unit)
#guard exitOf (replayEff pMiddleware middlewareTape) 1 = some (interruptedFrom ⟨0⟩ ⟨1⟩)
#guard childrenInterruptedRows (replayEff pMiddleware middlewareTape) = [(0, [1])]
#guard interruptRows (replayEff pMiddleware middlewareTape) = [(some 0, 1)]

-- The fork alone latches it (R2-6).
#guard (replayEff pMiddleware [evaluateRoot]).middlewareInstalled = true
#guard exitOf (replayEff pMiddleware [evaluateRoot]) 0 = some (Exit.success Val.unit)
#guard exitOf (replayEff pMiddleware [evaluateRoot]) 1 = some (interruptedFrom ⟨0⟩ ⟨1⟩)
#guard childrenInterruptedRows (replayEff pMiddleware [evaluateRoot]) = [(0, [1])]
#guard interruptRows (replayEff pMiddleware [evaluateRoot]) = [(some 0, 1)]

/-- A daemon child is untracked and does not latch the middleware: it survives the parent's
exit (`forkDaemon`). -/
def pDaemon : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.callback .deferredAwait (.var 0)) daemonChild))
      (.succeed (.lit .unit)))

#guard (typeOf nativeSignature pDaemon).isSome
#guard (replayEff pDaemon [evaluateRoot]).middlewareInstalled = false
#guard exitOf (replayEff pDaemon [evaluateRoot]) 0 = some (Exit.success Val.unit)
#guard exitOf (replayEff pDaemon [evaluateRoot]) 1 = none
#guard childrenInterruptedRows (replayEff pDaemon [evaluateRoot]) = []
#guard interruptRows (replayEff pDaemon [evaluateRoot]) = []

/-! ## `scoped` with `forkScoped`

The scope is made by the `sync` the compile binds first, the context is provided, the child is
linked to the scope by a keyed fiber finalizer, the body ends with the child's handle, and the
scope's close interrupts the child. The finalizer key is the identity the store allocates at
this registration (`E4-CHECK-CE-016`, `internal/effect.ts:5366`): the scoped entry takes name
`0` for the scope handle, so the registration takes `1`. -/

def pScoped : NativeEff :=
  .scoped (.bind (.perform .deferredMake (.lit .unit))
    (.withFiber (.forkScoped (.callback .deferredAwait (.var 0)) scopedChild)))

#guard (typeOf nativeSignature pScoped).isSome
#guard scopeRows (replayEff pScoped [evaluateRoot]) = [[0, 0, 0, 1, 1]]
#guard exitOf (replayEff pScoped [evaluateRoot]) 1 = some (interruptedFrom ⟨0⟩ ⟨1⟩)
#guard exitOf (replayEff pScoped [evaluateRoot]) 0 = some (Exit.success (Val.fiber ⟨1⟩))
#guard fiberCount (replayEff pScoped [evaluateRoot]) = 2
#guard stuckOf (replayEff pScoped [evaluateRoot]) = none

/-! ## Generators -/

/-- Two yields: the advanced generator name is what makes the second resume land after the
first (`IterStep.resume next continueAs`, the 2026-09-04 correction). -/
def pGenTwoYields : NativeEff :=
  .gen (.cons (.bindYield (.perform .refMake (.lit (.nat 1))))
    (.cons (.bindYield (.perform .refGet (.var 0)))
      (.cons (.ret (.app "succ" (.cons (.var 1) .nil))) .nil)))

#guard (typeOf nativeSignature pGenTwoYields).isSome
#guard exitOf (replayEff pGenTwoYields [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

/-- `if` on a `Ref.get` result with a `return` in each branch, the test true. -/
def pGenIfThen : NativeEff :=
  .gen (.cons (.bindYield (.perform .refMake (.lit (.nat 0))))
    (.cons (.bindYield (.perform .refGet (.var 0)))
      (.cons (.ifElse (.app "isZero" (.cons (.var 1) .nil))
              (.cons (.ret (.lit (.nat 10))) .nil)
              (.cons (.ret (.lit (.nat 20))) .nil)) .nil)))

#guard (typeOf nativeSignature pGenIfThen).isSome
#guard exitOf (replayEff pGenIfThen [evaluateRoot]) 0 = some (Exit.success (Val.nat 10))

/-- The same generator with the cell at `1`, so the else branch's `return` runs. -/
def pGenIfElse : NativeEff :=
  .gen (.cons (.bindYield (.perform .refMake (.lit (.nat 1))))
    (.cons (.bindYield (.perform .refGet (.var 0)))
      (.cons (.ifElse (.app "isZero" (.cons (.var 1) .nil))
              (.cons (.ret (.lit (.nat 10))) .nil)
              (.cons (.ret (.lit (.nat 20))) .nil)) .nil)))

#guard (typeOf nativeSignature pGenIfElse).isSome
#guard exitOf (replayEff pGenIfElse [evaluateRoot]) 0 = some (Exit.success (Val.nat 20))

/-- A generator whose second yield fails: `runStmts` halts with the yielded cause. -/
def pGenFail : NativeEff :=
  .gen (.cons (.bindYield (.succeed (.lit (.nat 1))))
    (.cons (.bindYield (.fail (.lit (.nat 7))))
      (.cons (.ret (.var 0)) .nil)))

#guard (typeOf nativeSignature pGenFail).isSome
#guard exitOf (replayEff pGenFail [evaluateRoot]) 0
  = some (Exit.failure (Cause.fail (Err.tag 7)))

/-! ### finding A3-2 — leaving an `ifElse`'s else block

`runStmts` addresses the then-block `pc ++ [0, 0]` and the else-block `pc ++ [0, 1]`, but
`splitPc` reads *every* trailing `1` of a program counter as "position within the block". The
else-block's own selector `1` is therefore eaten: `blockExit` and `loopExit` decode the block
as the enclosing `stmt` node, `blockAt` answers `none` (a `stmt`, not a `stmts`), the
`_ :: 0 :: outer` match fails, and control is lost. The then-block, whose selector is `0`, is
decoded correctly, so only the else side is affected. -/

/-- The minimal witness: an `if` whose else block is empty, followed by a `return`. -/
def pGenElseEnds : NativeEff :=
  .gen (.cons (.ifElse (.lit (.bool false))
                (.cons (.ret (.lit (.nat 1))) .nil) .nil)
    (.cons (.ret (.lit (.nat 2))) .nil))

#guard (typeOf nativeSignature pGenElseEnds).isSome

-- finding A3-2 (a) (closed): leaving the empty else block continues after the `if`.
#guard exitOf (replayEff pGenElseEnds [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

/-- The mirror image, decoded correctly: the *then* block is the empty one. -/
def pGenThenEnds : NativeEff :=
  .gen (.cons (.ifElse (.lit (.bool true)) .nil
                (.cons (.ret (.lit (.nat 1))) .nil))
    (.cons (.ret (.lit (.nat 2))) .nil))

#guard (typeOf nativeSignature pGenThenEnds).isSome
#guard exitOf (replayEff pGenThenEnds [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

/-- The counting loop the plan asks for: `while (true)` bumping a cell through
`Ref.update(cell, incr)` and breaking when `eq` says the cell reached `3`, returning the
cell's value. -/
def pGenLoop : NativeEff :=
  .gen (.cons (.bindYield (.perform .refMake (.lit (.nat 0))))
    (.cons (.whileTrue
        (.cons (.bindYield (.perform (.refUpdate FnName.incr) (.var 0)))
          (.cons (.bindYield (.perform .refGet (.var 0)))
            (.cons (.ifElse (.app "eq" (.cons (.var 2) (.cons (.lit (.nat 3)) .nil)))
                    (.cons .breakLoop .nil) .nil) .nil))))
      (.cons (.bindYield (.perform .refGet (.var 0)))
        (.cons (.ret (.var 1)) .nil))))

#guard (typeOf nativeSignature pGenLoop).isSome

-- finding A3-2 (b) (closed): the loop's continue path is the empty else block; it counts to 3.
#guard exitOf (replayEff pGenLoop [evaluateRoot]) 0 = some (Exit.success (Val.nat 3))
#guard refsOf (replayEff pGenLoop [evaluateRoot]) = [Val.nat 3]

/-- The same loop with the branches swapped, so the *continue* path is the (correctly decoded)
then block and only the `break` sits in the else block: the loop does count to `3`, and the
`break` is where control is lost instead. -/
def pGenLoopBreakInElse : NativeEff :=
  .gen (.cons (.bindYield (.perform .refMake (.lit (.nat 0))))
    (.cons (.whileTrue
        (.cons (.bindYield (.perform (.refUpdate FnName.incr) (.var 0)))
          (.cons (.bindYield (.perform .refGet (.var 0)))
            (.cons (.ifElse (.app "lt" (.cons (.var 2) (.cons (.lit (.nat 3)) .nil)))
                    .nil (.cons .breakLoop .nil)) .nil))))
      (.cons (.bindYield (.perform .refGet (.var 0)))
        (.cons (.ret (.var 1)) .nil))))

#guard (typeOf nativeSignature pGenLoopBreakInElse).isSome

-- finding A3-2 (c) (closed): a `break` in the else block leaves the loop.
#guard exitOf (replayEff pGenLoopBreakInElse [evaluateRoot]) 0 = some (Exit.success (Val.nat 3))
#guard refsOf (replayEff pGenLoopBreakInElse [evaluateRoot]) = [Val.nat 3]

/-! ## `whileLoop`

The cursor is the frame's `β`: `var 1` in the test and in the body, `var 1`/`var 2` the
cursor and the body's answer in the step. -/

def pWhileLoop : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.whileLoop (.lit (.nat 0))
              (.app "lt" (.cons (.var 1) (.cons (.lit (.nat 3)) .nil)))
              (.app "succ" (.cons (.var 1) .nil))
              (.perform (.refUpdate FnName.incr) (.var 0)))
      (.perform .refGet (.var 0)))

#guard (typeOf nativeSignature pWhileLoop).isSome
#guard exitOf (replayEff pWhileLoop [evaluateRoot]) 0 = some (Exit.success (Val.nat 3))
#guard refsOf (replayEff pWhileLoop [evaluateRoot]) = [Val.nat 3]

/-! ### The host's eager constructors (P0 record rows D1–D3, 2026-09-06)

`Effect.exit` of a body that is already an `Exit` is `exitSucceed(self)`
(`internal/effect.ts:3621-3622`); `Effect.gen` is a `Suspend` around the iterator
(`:1175-1196`); the printed `whileLoop` is a `Suspend` around the `While` frame
(`Codegen/Print.lean:158-168`). The compile follows the host, and `suspendBodyAt` answers
the iterator or the loop frame; the exits of every program above are unchanged. -/

def pLoopBare : NativeEff :=
  .whileLoop (.lit (.nat 0)) (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
    (.app "succ" (.cons (.var 0) .nil)) (.succeed (.lit .unit))

#guard compile (.exit pSucceed) fuel = Prim.success (Val.exitOk (Val.nat 42))
#guard compile pExit fuel = Prim.success (Val.exitErr (Cause.fail (Err.tag 7)))
#guard compile (.exit (.exit pSucceed)) fuel = Prim.success (Val.exitOk (Val.exitOk (Val.nat 42)))
#guard (compile (.exit pBindSync) fuel).asExit? = none
#guard compile (.exit pBindSync) fuel = Prim.exitFrame (compileEff pBindSync ((rootPoint fuel).child 0))
#guard compile pGenTwoYields fuel = Prim.suspend (EffThunk.body (rootPoint fuel))
#guard suspendBodyAt pGenTwoYields (EffThunk.body (rootPoint fuel)) =
  Prim.iterator (EffName.gen (rootPoint fuel) [] false) Val.unit
#guard compile pLoopBare fuel = Prim.suspend (EffThunk.body (rootPoint fuel))
#guard suspendBodyAt pLoopBare (EffThunk.body (rootPoint fuel)) =
  Prim.whileLoop (EffName.loop (rootPoint fuel)) (Val.nat 0)
#guard exitOf (replayEff pLoopBare [evaluateRoot]) 0 = some (Exit.success Val.unit)
#guard exitOf (replayEff (.exit (.exit pSucceed)) [evaluateRoot]) 0
  = some (Exit.success (Val.exitOk (Val.exitOk (Val.nat 42))))

/-! ## Control by value: `branch` and `choose` -/

def pBranchTrue : NativeEff :=
  .branch (.lit (.bool true)) (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))

def pBranchFalse : NativeEff :=
  .branch (.lit (.bool false)) (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))

#guard (typeOf nativeSignature pBranchTrue).isSome
#guard (typeOf nativeSignature pBranchFalse).isSome
#guard exitOf (replayEff pBranchTrue [evaluateRoot]) 0 = some (Exit.success (Val.nat 1))
#guard exitOf (replayEff pBranchFalse [evaluateRoot]) 0 = some (Exit.success (Val.nat 2))

/-- `choose` is answered by the point's tape (D2); an exhausted tape is a live frontier. -/
def pChoose : NativeEff :=
  .choose 0 (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))

#guard (typeOf nativeSignature pChoose).isSome
#guard exitOf (replayEffTape pChoose [true] [evaluateRoot]) 0
  = some (Exit.success (Val.nat 1))
#guard exitOf (replayEffTape pChoose [false] [evaluateRoot]) 0
  = some (Exit.success (Val.nat 2))
#guard exitOf (replayEffTape pChoose [] [evaluateRoot]) 0 = none
#guard stuckOf (replayEffTape pChoose [] [evaluateRoot]) = none
#guard replayArm pChoose [] [evaluateRoot] = 1

/-! ## Scheduling: `yieldNow` -/

def pYieldNow : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat 5)))

#guard (typeOf nativeSignature pYieldNow).isSome
#guard exitOf (replayEff pYieldNow [evaluateRoot]) 0 = none
#guard exitOf (replayEff pYieldNow [evaluateRoot, fireRoot]) 0
  = some (Exit.success (Val.nat 5))

/-! ## The masks

A daemon child (so the parent's exit leaves it; R2-6) parked on a `Deferred.await` inside
`Effect.uninterruptible`: the interrupt is recorded and not applied, and is delivered by the
restoring frame when the park is answered (W2's and W10's shape). -/

def pMasked : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.uninterruptible (.callback .deferredAwait (.var 0)))
              daemonChild))
      (.succeed (.lit .unit)))

def maskTapePending : List DC := [evaluateRoot, interruptChild]

def maskTapeAnswered : List DC :=
  [evaluateRoot, interruptChild, RunDecision.answerAsync ⟨1⟩ 0 (.ofExit (.success Val.unit))]

#guard (typeOf nativeSignature pMasked).isSome
#guard exitOf (replayEff pMasked maskTapePending) 1 = none
#guard interruptRows (replayEff pMasked maskTapePending) = [(some 0, 1)]
#guard exitOf (replayEff pMasked maskTapeAnswered) 1
  = some (Effect4.Machine.Witnesses.interruptedBy ⟨0⟩ ⟨1⟩)
#guard exitOf (replayEff pMasked maskTapeAnswered) 0 = some (Exit.success Val.unit)

/-- The same child under `Effect.interruptible`: the interrupt applies at once. -/
def pUnmasked : NativeEff :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.withFiber (.fork (.interruptible (.callback .deferredAwait (.var 0)))
              daemonChild))
      (.succeed (.lit .unit)))

#guard (typeOf nativeSignature pUnmasked).isSome
#guard exitOf (replayEff pUnmasked maskTapePending) 1
  = some (Effect4.Machine.Witnesses.interruptedBy ⟨0⟩ ⟨1⟩)

/-! ## The refused park

`awaitFiber` on a value that is not a fiber handle: the compile answers `badShape`, so the
fiber dies with `Defect.badName` rather than parking. The typing refuses the program for the
same reason (`fiberTy .nat = none`), which is the pin here: this is the one program in the
battery that is deliberately ill-typed. -/

def pBadPark : NativeEff :=
  .bind (.succeed (.lit (.nat 1))) (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect)

#guard (typeOf nativeSignature pBadPark).isNone
#guard exitOf (replayEff pBadPark [evaluateRoot]) 0
  = some (Exit.failure (Cause.die Defect.badName))

/-! ## The `finalizerOr` regression net, on the compile route (the join, 2026-09-07)

The Layer machine's five guards (`git:4aae12f:src/Effect4/Machine/Layer.lean:2051-2074`, the
machine defect that spike found; the file retired with the join): `scoped` must close its scope whether or not another `OnExit` frame
sits under it, and every build sits under `updateContext`'s restoring frame
(`internal/effect.ts:2092`). Re-spelled here program for program on the compile route, where
`scoped`'s exit is the atomic native callback (V1, `exitScoped`) rather than a finalizer
program: the counted rows are the region restores, `Effect.provide`'s scope close and the
releases, never `scoped`'s own close, and what the net pins is that every scope a run
allocates is closed on the way out. -/

/-- Every scope the run allocated, with whether it is closed (Layer.lean's `witnessScopes`). -/
def scopeStates (m : MC) : List (Nat × Bool) :=
  m.state.scopes.entries.map fun e => (e.key, e.scope.isClosed)

def netRun (p : NativeEff) : MC := replayEff p [evaluateRoot]

/-- A number-typed service key (code `4`, `nativeServiceTy`). -/
def netKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

-- One `scoped`: its scope closes.
#guard scopeStates (netRun (.scoped (.succeed (.lit (.nat 7))))) = [(0, true)]
-- Two adjacent: both close.
#guard scopeStates (netRun (.scoped (.scoped (.succeed (.lit (.nat 7)))))) = [(0, true), (1, true)]
-- Separated by a continuation frame, both close as well.
#guard scopeStates (netRun
    (.scoped (.bind (.scoped (.succeed (.lit (.nat 1)))) (.succeed (.lit (.nat 7)))))) =
  [(0, true), (1, true)]

/-- The shape every build has: `Effect.provide`'s scope under `scoped`, the build under the
`CurrentMemoMap` region's restoring frame (`Layer.ts:762`). Both scopes close; the two
finalizer programs are the region's restore and the provide scope's close — the body is an
exit, so `provideContext` adds no region (`internal/effect.ts:2196`). -/
def netBuild : NativeEff :=
  .scoped (.provideLayer (.succeed netKey (.nat 1)) false (.succeed (.lit (.nat 7))))

#guard (typeOf nativeSignature netBuild).isSome
#guard scopeStates (netRun netBuild) = [(0, true), (1, true)]
#guard finalizerRuns (netRun netBuild) 0 = 2

/-- A memoized leaf under `provide` under `scoped`: `scoped`'s scope, the provide scope, the
`fromBuild` child and the layer scope (`2` and `4` are the memo map and the entry's deferred,
minted from the same counter) all close, and the service reads through. -/
def netMemo : NativeEff :=
  .scoped (.provideLayer (.effect netKey (.succeed (.lit (.nat 1)))) false (.service netKey))

#guard (typeOf nativeSignature netMemo).isSome
#guard scopeStates (netRun netMemo) = [(0, true), (1, true), (3, true), (5, true)]
#guard finalizerRuns (netRun netMemo) 0 = 6
#guard exitOf (netRun netMemo) 0 = some (Exit.success (Val.nat 1))

-- `scope.acquire-release` (Layer.lean's W10): the release registered on the ambient scope
-- runs at the close, and the acquire's value is the answer.
#guard scopeStates (netRun
    (.scoped (.acquireRelease (.succeed (.lit (.nat 5))) (.succeed (.lit .unit))))) = [(0, true)]
#guard exitOf (netRun
    (.scoped (.acquireRelease (.succeed (.lit (.nat 5))) (.succeed (.lit .unit))))) 0 =
  some (Exit.success (Val.nat 5))

/-! ## The timer on the program route (A4, commit 2)

`Effect.sleep(d)` is the async row's callback: `0` is the counted yield (`internal/effect.ts:6054`),
the rest parks on the logical clock until an `advance` fires it (`Machine/Timer.lean`,
DB-14). `Effect.currentTimeMillis` reads the clock. The two shapes the machine-level
fixtures could not spell (`SchedulerCoreContract` §Timer): a woken fiber reads the staged
clock, and a woken fiber's sleep fires in the same advance (finding 4 of the timer note). -/

def pSleep : NativeEff := .callback .sleep (.lit (.nat 5))
def pSleepZero : NativeEff := .callback .sleep (.lit (.nat 0))
def pSleepNow : NativeEff := .bind (.callback .sleep (.lit (.nat 3))) (.perform .clockNow (.lit .unit))
def pSleepTwice : NativeEff := .bind (.callback .sleep (.lit (.nat 1))) (.callback .sleep (.lit (.nat 1)))
def pClockNow : NativeEff := .perform .clockNow (.lit .unit)

#guard (typeOf nativeSignature pSleep).isSome ∧ (typeOf nativeSignature pSleepNow).isSome
#guard (typeOf nativeSignature pSleepTwice).isSome ∧ (typeOf nativeSignature pClockNow).isSome
-- a sleep parks; an advance short of the deadline leaves it parked; the deadline fires it
#guard exitOf (replayEff pSleep [evaluateRoot]) 0 = none
#guard exitOf (replayEff pSleep [evaluateRoot, .advance 4]) 0 = none
#guard exitOf (replayEff pSleep [evaluateRoot, .advance 5]) 0 = some (.success .unit)
#guard exitOf (replayEff pSleep [evaluateRoot, .advance 4, .advance 1]) 0 = some (.success .unit)
-- `sleep 0` is the counted yield: the flush resumes it, no advance needed
#guard exitOf (replayEff pSleepZero [evaluateRoot]) 0 = none
#guard exitOf (replayEff pSleepZero [evaluateRoot, .flush]) 0 = some (.success .unit)
-- the woken fiber reads the clock staged at its deadline, not the advance's end
#guard exitOf (replayEff pSleepNow [evaluateRoot, .advance 10]) 0 = some (.success (.nat 3))
-- finding 4: the sleep a woken fiber registers fires in the same advance when due by its end
#guard exitOf (replayEff pSleepTwice [evaluateRoot, .advance 2]) 0 = some (.success .unit)
#guard exitOf (replayEff pSleepTwice [evaluateRoot, .advance 1]) 0 = none
#guard exitOf (replayEff pSleepTwice [evaluateRoot, .advance 1, .advance 1]) 0 = some (.success .unit)
-- the clock read: zero at the start, the sum of the advances after
#guard exitOf (replayEff pClockNow [evaluateRoot]) 0 = some (.success (.nat 0))
#guard exitOf (replayEff pClockNow [.advance 7, .advance 0, evaluateRoot]) 0 = some (.success (.nat 7))

end Test.Syntax.CompileContract
