import Effect4.Meta.Derive

/-!
# Concurrency.FiberFamily

`Fibers`: a traced family over rc.112's `Effect.forkChild` / `Effect.forkDetach`
/ `Fiber.join` / `Fiber.await` / `Fiber.interrupt`, with the Lean handler that
is the honest *sequential projection* of a two-fiber run (packet M3,
`docs/research/2026-09-03-reification-plan.md`).

## The refusal this module is built around

`Effect4/Concurrency/Scheduler.lean`'s `Machine` carries fibers, masks and a
decision tape, but it carries **no program**: a `FiberState` has no residual
term, so nothing in the Lean tree can step two fibers against each other. The
Lean face of two fibers is therefore a projection in which at most one child
runs at a time, and *when* a child is given the processor is read off a tape
rather than derived. Scheduler-order agreement with rc.112 stays a host
protocol until a two-fiber model exists — a new model, not an extension of
`Machine`. Nothing here is a theorem about the host.

## The projection, exactly

A child is `queued` (forked, never given the processor), `live` (started, has
not published) or `exited` (published; `none` for an interrupted child). The
model keeps them in fork order.

- `fork` and `forkDetach` enqueue a child and then consult the tape at the
  fork's site (its ordinal among the run's forks). On `true` the model
  *drains*: every queued child is given the processor, in fork order, and each
  runs to completion if its body can complete (`bodyOutcome`) and otherwise
  becomes `live`. On `false` nothing runs.
- `join`, `awaitValue` and `awaitError` drain **only when their target has not
  published**: the parent blocks, so the run loop gets a slot. Awaiting an
  already published child runs nothing.
- `interrupt` never drains. A `queued` child is interrupted before it ever
  runs, so its cleanup does not run; a `live` child's cleanup runs; an
  `exited` child is unchanged.
- `started` and `cleanups` are pure observations and never drain.
- When the parent exits (`FiberTable.parentExit`, after the last traced row) it
  interrupts and waits for every *tracked* child and leaves daemons running,
  which is `Supervision.interruptAllRequests` / `awaitAllChildren` and
  `commitFork_daemon_untracked` as handler behaviour.

Every one of those five clauses was read off the pinned rc.112 install first
and written down here second; `harness/trace/fiber-tail.ts` and the goldens
under `generated/traces/fiber/` are the standing evidence.

## What the projection cannot do, stated here rather than discovered later

- **`join` of an interrupted child.** The host fails the parent with an
  `Interrupt` cause and the run ends `{"interrupted":true}`; this family's
  abort channel is `Nat`, so the model could only invent a failure code and
  end `{"failure":n}`. Every mask keeps the outcome, so the two faces cannot
  agree. The model refuses instead: it sets `FiberTable.stuck`, and a golden
  is not emitted for a program that sets it.
  counterexample: E4-SEM-CE-010
- **The tape's `false` is not stable at rc.112's own yield floor.** With
  `MaxOpsBeforeYield` at the floor of 3 the run loop yields on its own and a
  deferred child starts with no decision row to account for it. The `fiber`
  section of `scripts/check-trace-host.sh` therefore runs at the default
  threshold only. counterexample: E4-SEM-CE-011
- **A child that can never publish and is never interrupted.** `join` or an
  await on it is a deadlock on the host and has no answer here; the model sets
  `stuck` rather than inventing one.

## Two refusals of spelling, recorded where they bite

- `await` is a reserved word in the generated-binding profile
  (`TypeScript.reservedIdentifiers`), so `Fiber.await` is spelled here as two
  operations rather than one method named `await`.
- Stratum V admits type spellings of depth two, so `Option (Except Nat Nat)` —
  the exact shape of an rc.112 `Exit` under this alphabet — is not a spelling
  the DSL has. Rather than widen the stratum or hand-roll a tag encoding into
  a `List Nat`, the trichotomy is spelled with the alphabet's own formers as
  two operations: `awaitValue` answers `some v` exactly when the child
  succeeded, `awaitError` answers `some e` exactly when it failed with a typed
  error, and a child that was interrupted answers `none` to both. Neither
  operation ever invents a code.

The error channel is `Nat`, not `String`: this module is under `Effect4/` and
is audited by `#effect4_axiom_gate`, so its semantics carry no string folds.
The only `String`s it holds are the literals `effect_signature` and
`effect_program` emit for the target renderer.
-/

set_option autoImplicit false

namespace Effect4.FiberFamily

open Effects Effect4 Effect4.Meta

/-! ## The signature -/

effect_signature Fibers where
  | fork (body : Nat) : Handle "Fiber.Fiber<number, number>"
      ⟪ "fork a tracked child running body number `body`", "the child's handle" ⟫
  | forkDetach (body : Nat) : Handle "Fiber.Fiber<number, number>"
      ⟪ "fork a daemon running body number `body`", "the daemon's handle" ⟫
  | join (fiber : Handle "Fiber.Fiber<number, number>") : Nat !! Nat
      ⟪ "join the child, resuming its exit in this fiber", "the child's value", "the child's failure, resumed here" ⟫
  | awaitValue (fiber : Handle "Fiber.Fiber<number, number>") : Option Nat
      ⟪ "await the child and answer its success value", "some v when it succeeded, none otherwise" ⟫
  | awaitError (fiber : Handle "Fiber.Fiber<number, number>") : Option Nat
      ⟪ "await the child and answer its typed failure", "some e when it failed, none otherwise" ⟫
  | interrupt (fiber : Handle "Fiber.Fiber<number, number>") : Unit
      ⟪ "interrupt the child" ⟫
  | started : List Nat
      ⟪ "the bodies that have been given the processor, in start order" ⟫
  | cleanups : List Nat
      ⟪ "the bodies whose cleanup has run, in cleanup order" ⟫

/-! ## The child bodies

A body is a number, not a program: this family has no former for a child that
performs operations of its own, so a child is opaque and only its start, its
cleanup and its exit are observable. `harness/trace/fiber-tail.ts` carries the
same table as rc.112 effects. -/

/-- What body `code` does once it has the processor: `some exit` when it runs
to completion, `none` when it blocks forever (rc.112 `Effect.never`). -/
def bodyOutcome : Nat → Option (Except Nat Nat)
  | 0 => some (.ok 11)
  | 1 => some (.ok 22)
  | 2 => some (.error 1)
  | 3 => some (.error 2)
  | _ => none

/-! ## The table -/

/-- Where a child is in the projection. `exited none` is an interrupted child:
the outer `Option` is publication, the inner one is the exit it published. -/
inductive ChildState
  | queued
  | live
  | exited (result : Option (Except Nat Nat))

/-- One forked child: its body code, whether the parent's exit is supposed to
reach it, and where it is. -/
structure Child where
  body : Nat
  daemon : Bool
  state : ChildState

/-- The projection's whole state. `tape` answers one decision per fork, in fork
order; `decisions` records what it answered, so the traced wrapper can emit the
`decide` rows between a fork's `op` row and its `answer` row. -/
structure FiberTable where
  children : List Child := []
  startOrder : List Nat := []
  cleanupOrder : List Nat := []
  tape : List Bool := []
  decisions : List (Nat × Bool) := []
  /-- Set when the projection is asked something it has no answer for: a
  `join` of an interrupted child, or a `join` or await of a child that can
  never publish. A golden is refused for a program that sets it. -/
  stuck : Bool := false

namespace FiberTable

/-- Give the processor to child `index` if it is queued; a child that can run
to completion publishes and its cleanup runs at once, and one that cannot
becomes `live`. -/
def start (table : FiberTable) (index : Nat) : FiberTable :=
  match table.children[index]? with
  | none => table
  | some child =>
      match child.state with
      | .queued =>
          match bodyOutcome child.body with
          | some result =>
              { table with
                children := table.children.set index { child with state := .exited (some result) },
                startOrder := table.startOrder ++ [child.body],
                cleanupOrder := table.cleanupOrder ++ [child.body] }
          | none =>
              { table with
                children := table.children.set index { child with state := .live },
                startOrder := table.startOrder ++ [child.body] }
      | _ => table

/-- The run loop's slot: every queued child is given the processor, in fork
order. rc.112 drains the whole queue at a yield, not only the child forked
last, which is what this mirrors. -/
def drain (table : FiberTable) : FiberTable :=
  (List.range table.children.length).foldl FiberTable.start table

/-- Interrupt child `index`. A queued child never runs, so nothing of it is
cleaned; a live child's cleanup runs; a published child is unchanged. -/
def interruptAt (table : FiberTable) (index : Nat) : FiberTable :=
  match table.children[index]? with
  | none => table
  | some child =>
      match child.state with
      | .queued =>
          { table with children := table.children.set index { child with state := .exited none } }
      | .live =>
          { table with
            children := table.children.set index { child with state := .exited none },
            cleanupOrder := table.cleanupOrder ++ [child.body] }
      | .exited _ => table

/-- The exit child `index` published, if it has published one. -/
def result? (table : FiberTable) (index : Nat) : Option (Option (Except Nat Nat)) :=
  match table.children[index]? with
  | some { state := .exited result, .. } => some result
  | _ => none

/-- Drain only when the target has not published: that is the parent blocking. -/
def blockOn (table : FiberTable) (index : Nat) : FiberTable :=
  if (table.result? index).isNone then table.drain else table

/-- The parent's own exit, from `Effect4/Concurrency/Supervision.lean`: it
requests interruption of every *tracked* child and then waits for each of them
(`interruptAllRequests_eq`, `awaitAllChildren_eq`), and it leaves daemons
running (`commitFork_daemon_untracked`). That is the supervision fact this
family carries as handler behaviour.

No program can observe it — the run's `done` row is the last row of a golden,
and this happens after it — but it is why `fiberDaemonSurvivesParentExit`
returns at all: the same program with a tracked `never` child would make the
parent wait for a child that never publishes. It is also why every program of
the corpus terminates on the host with no child left tracked and live. -/
def parentExit (table : FiberTable) : FiberTable :=
  (List.range table.children.length).foldl
    (fun current index =>
      match current.children[index]? with
      | none => current
      | some child => if child.daemon then current else current.interruptAt index)
    table

/-- The bodies of the children still running when the parent exits: after
`parentExit` this is the daemons and nothing else. -/
def liveBodies (table : FiberTable) : List Nat :=
  table.children.filterMap fun child =>
    match child.state with
    | .exited _ => none
    | _ => some child.body

end FiberTable

/-! ## The handler -/

/-- The monad the projection runs in: one abort channel for a resumed child
failure, over the table. -/
abbrev FiberM := ExceptT Nat (StateT FiberTable Id)

/-- Enqueue a child, consult the tape at this fork's site, and drain when it
answers `true`. -/
def forkAt (body : Nat) (daemon : Bool) :
    FiberM (Handle "Fiber.Fiber<number, number>") := do
  let table ← get
  let index := table.children.length
  let site := table.decisions.length
  let branch := (table.tape[site]?).getD false
  let queued : FiberTable :=
    { table with
      children := table.children ++ [{ body := body, daemon := daemon, state := .queued }],
      decisions := table.decisions ++ [(site, branch)] }
  set (if branch then queued.drain else queued)
  pure ⟨index⟩

/-- The Lean handler: the projection and nothing else. -/
def fibersLive : Fibers.Service FiberM := fun name =>
  match name with
  | .fork => fun body => forkAt body false
  | .forkDetach => fun body => forkAt body true
  | .join => fun handle => do
      modify (fun table => table.blockOn handle.index)
      let table ← get
      match table.result? handle.index with
      | some (some (.ok value)) => pure value
      | some (some (.error error)) => throw error
      | some none => do
          -- E4-SEM-CE-010: the host ends `{"interrupted":true}` here and this
          -- channel cannot say that. Refuse rather than invent a code.
          modify (fun table => { table with stuck := true })
          throw 0
      | none => do
          modify (fun table => { table with stuck := true })
          throw 0
  | .awaitValue => fun handle => do
      modify (fun table => table.blockOn handle.index)
      let table ← get
      match table.result? handle.index with
      | some (some (.ok value)) => pure (some value)
      | some _ => pure none
      | none => do
          modify (fun table => { table with stuck := true })
          pure none
  | .awaitError => fun handle => do
      modify (fun table => table.blockOn handle.index)
      let table ← get
      match table.result? handle.index with
      | some (some (.error error)) => pure (some error)
      | some _ => pure none
      | none => do
          modify (fun table => { table with stuck := true })
          pure none
  | .interrupt => fun handle => modify (fun table => table.interruptAt handle.index)
  | .started => fun _ => do let table ← get; pure table.startOrder
  | .cleanups => fun _ => do let table ← get; pure table.cleanupOrder

/-! ## The traced face

`Family.Service.tracedExcept` appends `op` and then `answer` or `failed`, which
is all a family whose operations make no decisions needs. A fork *does* make
one, and the host records it between `traceService`'s `op` row and its `answer`
row, so the wrapper here is spelled out rather than derived: it emits the
decisions the operation consumed, in the same slot. -/

def fibersTraced (service : Fibers.Service FiberM) :
    Fibers.Service (ExceptT Nat (StateT Effect4.Trace.Log (StateT FiberTable Id))) :=
  fun name param => ExceptT.mk fun log table =>
    let step := ((service name param).run table).run
    let result := step.1
    let after := step.2
    let decided : Effect4.Trace.Log :=
      (after.decisions.drop table.decisions.length).map fun entry =>
        Effects.Trace.Event.decide entry.1 entry.2
    let closing : Effect4.Trace.Log :=
      match result with
      | .ok answer => [.answer (Fibers.Name.spelling name) (Fibers.encodeAnswer name answer)]
      | .error error => [.failed (Fibers.Name.spelling name) (.nat error)]
    ((result,
      log ++ [.op (Fibers.Name.spelling name) (Fibers.encodeParam name param)] ++ decided ++ closing),
     after)

/-! ## The nine programs

Each is named after the assertion of `harness/fiber-supervision/runtime-check.ts`
it re-expresses. The tenth assertion of that file,
`race-reentrant-nonempty-set-includes-late-insertion`, is refused: it is
distinguished from the empty-set case only by cleanups run *from inside* the
winning entrant's own completion callback, and this family has no former for a
child that completes another child, so at this alphabet it collapses onto
`fiberRaceReentrantEmptySetBypasses`. -/

-- race-immediate-success-stops-launch: the first entrant is given the
-- processor and completes; the later entrant is never launched.
effect_program fiberRaceImmediateSuccessStopsLaunch (n : Nat) over Fibers : List Nat :=
  let a ← Fibers.fork(0)
  let b ← Fibers.fork(1)
  let s ← Fibers.started()
  let _ ← Fibers.interrupt(b)
  return s

-- race-failure-allows-next-launch: a first completion that *failed* does not
-- stop the source loop, so the later entrant does launch.
effect_program fiberRaceFailureAllowsNextLaunch (n : Nat) over Fibers : List Nat :=
  let a ← Fibers.fork(2)
  let e ← Fibers.awaitError(a)
  let b ← Fibers.fork(1)
  let s ← Fibers.started()
  return s

-- race-all-failures-retain-order-and-duplicates: three entrants, two of them
-- failing with the same code; completion order and duplicates both survive.
effect_program fiberRaceAllFailuresRetainOrder (n : Nat) over Fibers : List Nat :=
  let a ← Fibers.fork(2)
  let b ← Fibers.fork(3)
  let c ← Fibers.fork(2)
  let _ ← Fibers.awaitError(a)
  let _ ← Fibers.awaitError(b)
  let _ ← Fibers.awaitError(c)
  let s ← Fibers.cleanups()
  return s

-- empty-race-pending-until-interrupted: with no decision to launch it the
-- entrant stays pending; the explicit cancellation is what finishes it, and it
-- finishes without ever having run.
effect_program fiberEmptyRacePendingUntilInterrupted (n : Nat) over Fibers : List Nat :=
  let a ← Fibers.fork(4)
  let s ← Fibers.started()
  let _ ← Fibers.interrupt(a)
  let v ← Fibers.awaitValue(a)
  let e ← Fibers.awaitError(a)
  let c ← Fibers.cleanups()
  return c

-- parent-publishes-after-tracked-child-cleanup: the child's exit is not
-- observable until its cleanup has run.
effect_program fiberParentPublishesAfterChildCleanup (n : Nat) over Fibers : List Nat :=
  let a ← Fibers.fork(4)
  let b ← Fibers.cleanups()
  let _ ← Fibers.interrupt(a)
  let v ← Fibers.awaitValue(a)
  let c ← Fibers.cleanups()
  return c

-- daemon-survives-parent-exit: a detached child is running and uncleaned when
-- the parent returns, and the parent returns anyway. A *tracked* child in the
-- same position would make this program wait for it forever.
effect_program fiberDaemonSurvivesParentExit (n : Nat) over Fibers : List Nat :=
  let d ← Fibers.forkDetach(4)
  let s ← Fibers.started()
  let c ← Fibers.cleanups()
  return c

-- await-value-distinct-from-join-effect: the same failed child, delivered
-- three times. The awaits answer its exit as a value and the run continues;
-- `join` resumes it and the run ends failed.
effect_program fiberAwaitValueDistinctFromJoinEffect (n : Nat) over Fibers : Nat :=
  let a ← Fibers.fork(2)
  let v ← Fibers.awaitValue(a)
  let e ← Fibers.awaitError(a)
  let y ← Fibers.join(a)
  return y

-- race-reentrant-empty-set-bypasses-late-insertion: awaiting a winner that has
-- already published runs nothing, so the late entrant is still unlaunched and
-- survives; the explicit interrupt is what finishes it.
effect_program fiberRaceReentrantEmptySetBypasses (n : Nat) over Fibers : List Nat :=
  let w ← Fibers.fork(0)
  let l ← Fibers.fork(4)
  let x ← Fibers.awaitValue(w)
  let s ← Fibers.started()
  let _ ← Fibers.interrupt(l)
  let y ← Fibers.awaitValue(l)
  return s

-- parent-interrupt-during-child-wait-changes-result: an interrupt after
-- publication cannot change the exit, and an interrupt before publication
-- replaces it.
effect_program fiberParentInterruptDuringChildWait (n : Nat) over Fibers : Option Nat :=
  let a ← Fibers.fork(0)
  let _ ← Fibers.interrupt(a)
  let x ← Fibers.awaitValue(a)
  let b ← Fibers.fork(4)
  let _ ← Fibers.interrupt(b)
  let y ← Fibers.awaitValue(b)
  return y

/-! ## Golden logs -/

/-- One fiber program: its script, the tape its forks are answered from, its
traced log, and whether the projection refused anything on the way. -/
structure FiberEntry where
  name : String
  script : Effect4.Target.EffectV4.Script
  tape : List (Nat × Bool)
  log : Effect4.Trace.Log
  stuck : Bool

/-- The traced run of one fiber program under one tape. -/
def fiberRun {α : Type} [Effects.Trace.ToVal α]
    (program : Effects.Program Fibers.Sig α) (tape : List (Nat × Bool)) :
    (Except Nat α × Effect4.Trace.Log) × FiberTable :=
  (((Effects.interpret (fibersTraced fibersLive).toHandler program).run.run []).run
    { tape := tape.map (·.2) }).run

/-- The traced log with the outcome appended: a resumed child failure is the
run's failure, exactly as `Fiber.join` makes it on the host. -/
def fiberGoldenLog {α : Type} [Effects.Trace.ToVal α]
    (program : Effects.Program Fibers.Sig α) (tape : List (Nat × Bool)) : Effect4.Trace.Log :=
  let result := fiberRun program tape
  result.1.2 ++ [.done (match result.1.1 with
    | .ok value => .success (Effects.Trace.ToVal.toVal value)
    | .error error => .failure (.nat error))]

/-- Whether the projection refused something during the run. -/
def fiberStuck {α : Type} [Effects.Trace.ToVal α]
    (program : Effects.Program Fibers.Sig α) (tape : List (Nat × Bool)) : Bool :=
  (fiberRun program tape).2.stuck

def fiberEntry {α : Type} [Effects.Trace.ToVal α] (name : String)
    (script : Effect4.Target.EffectV4.Script)
    (program : Effects.Program Fibers.Sig α) (tape : List (Nat × Bool)) : FiberEntry :=
  { name := name, script := script, tape := tape,
    log := fiberGoldenLog program tape, stuck := fiberStuck program tape }

/-- The nine programs, each with the tape its forks are answered from. -/
def fiberPrograms : List FiberEntry :=
  [ fiberEntry "raceImmediateSuccessStopsLaunch"
      fiberRaceImmediateSuccessStopsLaunch.script
      (fiberRaceImmediateSuccessStopsLaunch 0) [(0, true), (1, false)]
  , fiberEntry "raceFailureAllowsNextLaunch"
      fiberRaceFailureAllowsNextLaunch.script
      (fiberRaceFailureAllowsNextLaunch 0) [(0, true), (1, true)]
  , fiberEntry "raceAllFailuresRetainOrder"
      fiberRaceAllFailuresRetainOrder.script
      (fiberRaceAllFailuresRetainOrder 0) [(0, true), (1, true), (2, true)]
  , fiberEntry "emptyRacePendingUntilInterrupted"
      fiberEmptyRacePendingUntilInterrupted.script
      (fiberEmptyRacePendingUntilInterrupted 0) [(0, false)]
  , fiberEntry "parentPublishesAfterChildCleanup"
      fiberParentPublishesAfterChildCleanup.script
      (fiberParentPublishesAfterChildCleanup 0) [(0, true)]
  , fiberEntry "daemonSurvivesParentExit"
      fiberDaemonSurvivesParentExit.script
      (fiberDaemonSurvivesParentExit 0) [(0, true)]
  , fiberEntry "awaitValueDistinctFromJoinEffect"
      fiberAwaitValueDistinctFromJoinEffect.script
      (fiberAwaitValueDistinctFromJoinEffect 0) [(0, true)]
  , fiberEntry "raceReentrantEmptySetBypasses"
      fiberRaceReentrantEmptySetBypasses.script
      (fiberRaceReentrantEmptySetBypasses 0) [(0, true), (1, false)]
  , fiberEntry "parentInterruptDuringChildWait"
      fiberParentInterruptDuringChildWait.script
      (fiberParentInterruptDuringChildWait 0) [(0, true), (1, true)] ]

end Effect4.FiberFamily
