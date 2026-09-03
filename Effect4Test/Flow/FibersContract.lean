/-
Contract packet: M3 (`docs/research/2026-09-03-reification-plan.md`). Kernel
receipts for the `Fibers` family's Lean face: the exact rows of each of the
nine goldens under `generated/traces/fiber/`, and the five clauses of the
sequential projection they rest on.

These are `#guard`s, evaluated by the kernel, not proofs. Nothing here is a
statement about the host: the same rows are compared with rc.112 by
`scripts/check-trace-host.sh`'s `fiber` section through
`harness/trace/fiber-tail.ts`, and that comparison is evidence, never a
theorem. Doc comments cannot precede `#guard`, so the receipts carry line
comments.
-/

import Effect4.Concurrency.FiberFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.FibersContract

open Effect4.FiberFamily

#check @Effect4.FiberFamily.Fibers
#check (@Effect4.FiberFamily.Fibers.rows : Effect4.Target.EffectV4.ServiceRow)
#check @Effect4.FiberFamily.fibersLive
#check @Effect4.FiberFamily.fibersTraced
#check @Effect4.FiberFamily.fiberGoldenLog

/-! ## The corpus -/

-- Nine programs, one per assertion of `harness/fiber-supervision/runtime-check.ts`
-- that this alphabet can carry. The tenth,
-- `race-reentrant-nonempty-set-includes-late-insertion`, is refused in the
-- module comment of `Effect4/Concurrency/FiberFamily.lean`.
#guard fiberPrograms.length == 9

#guard fiberPrograms.map (·.name) ==
  [ "raceImmediateSuccessStopsLaunch", "raceFailureAllowsNextLaunch"
  , "raceAllFailuresRetainOrder", "emptyRacePendingUntilInterrupted"
  , "parentPublishesAfterChildCleanup", "daemonSurvivesParentExit"
  , "awaitValueDistinctFromJoinEffect", "raceReentrantEmptySetBypasses"
  , "parentInterruptDuringChildWait" ]

-- No program of the corpus asks the projection something it has no answer for,
-- so every one of the nine has a golden. counterexample: E4-SEM-CE-010
#guard fiberPrograms.all (fun entry => !entry.stuck)

/-! ## The rows of each golden -/

/-- The wire rows of one program's Lean log, exactly as the golden carries
them. An unknown name answers a row that no golden can match. -/
def rowsOf (name : String) : List String :=
  match fiberPrograms.find? (·.name == name) with
  | some entry => entry.log.map Effect4.Target.TypeScript.Trace.row
  | none => ["unknown fiber program"]

/-- The tape one program's forks are answered from. -/
def tapeOf (name : String) : List (Nat × Bool) :=
  match fiberPrograms.find? (·.name == name) with
  | some entry => entry.tape
  | none => []

-- race-immediate-success-stops-launch: the first fork's `true` hands the
-- processor over and body 0 completes; the second fork's `false` leaves body 1
-- queued, so `started` sees only `[0]`.
#guard tapeOf "raceImmediateSuccessStopsLaunch" == [(0, true), (1, false)]
#guard rowsOf "raceImmediateSuccessStopsLaunch" ==
  [ "op\tfork\t0", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tfork\t1", "decide\t1\tfalse", "answer\tfork\t1"
  , "op\tstarted\t[]", "answer\tstarted\t[0, []]"
  , "op\tinterrupt\t1", "answer\tinterrupt\t[]"
  , "done\t{\"success\":[0, []]}" ]

-- race-failure-allows-next-launch: the first entrant completed by *failing*,
-- which does not stop the launch of the second.
#guard tapeOf "raceFailureAllowsNextLaunch" == [(0, true), (1, true)]
#guard rowsOf "raceFailureAllowsNextLaunch" ==
  [ "op\tfork\t2", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tawaitError\t0", "answer\tawaitError\t{\"some\":1}"
  , "op\tfork\t1", "decide\t1\ttrue", "answer\tfork\t1"
  , "op\tstarted\t[]", "answer\tstarted\t[2, [1, []]]"
  , "done\t{\"success\":[2, [1, []]]}" ]

-- race-all-failures-retain-order-and-duplicates: three entrants, two failing
-- with the same code, and both the completion order and the duplicate survive
-- in `cleanups` and in the three `awaitError` answers.
#guard rowsOf "raceAllFailuresRetainOrder" ==
  [ "op\tfork\t2", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tfork\t3", "decide\t1\ttrue", "answer\tfork\t1"
  , "op\tfork\t2", "decide\t2\ttrue", "answer\tfork\t2"
  , "op\tawaitError\t0", "answer\tawaitError\t{\"some\":1}"
  , "op\tawaitError\t1", "answer\tawaitError\t{\"some\":2}"
  , "op\tawaitError\t2", "answer\tawaitError\t{\"some\":1}"
  , "op\tcleanups\t[]", "answer\tcleanups\t[2, [3, [2, []]]]"
  , "done\t{\"success\":[2, [3, [2, []]]]}" ]

-- empty-race-pending-until-interrupted: no decision launches the entrant, so
-- it is pending; the explicit interrupt finishes it, and it finishes without
-- ever having run, which is why `cleanups` is still empty at the end.
#guard tapeOf "emptyRacePendingUntilInterrupted" == [(0, false)]
#guard rowsOf "emptyRacePendingUntilInterrupted" ==
  [ "op\tfork\t4", "decide\t0\tfalse", "answer\tfork\t0"
  , "op\tstarted\t[]", "answer\tstarted\t[]"
  , "op\tinterrupt\t0", "answer\tinterrupt\t[]"
  , "op\tawaitValue\t0", "answer\tawaitValue\t{\"none\":true}"
  , "op\tawaitError\t0", "answer\tawaitError\t{\"none\":true}"
  , "op\tcleanups\t[]", "answer\tcleanups\t[]"
  , "done\t{\"success\":[]}" ]

-- parent-publishes-after-tracked-child-cleanup: nothing is cleaned while the
-- child is live, and by the time its exit is observable its cleanup has run.
#guard rowsOf "parentPublishesAfterChildCleanup" ==
  [ "op\tfork\t4", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tcleanups\t[]", "answer\tcleanups\t[]"
  , "op\tinterrupt\t0", "answer\tinterrupt\t[]"
  , "op\tawaitValue\t0", "answer\tawaitValue\t{\"none\":true}"
  , "op\tcleanups\t[]", "answer\tcleanups\t[4, []]"
  , "done\t{\"success\":[4, []]}" ]

-- daemon-survives-parent-exit: the daemon is started and uncleaned when the
-- program returns, and the program returns anyway.
#guard rowsOf "daemonSurvivesParentExit" ==
  [ "op\tforkDetach\t4", "decide\t0\ttrue", "answer\tforkDetach\t0"
  , "op\tstarted\t[]", "answer\tstarted\t[4, []]"
  , "op\tcleanups\t[]", "answer\tcleanups\t[]"
  , "done\t{\"success\":[]}" ]

-- await-value-distinct-from-join-effect: the same failed child three times.
-- The awaits answer its exit as a value and the run continues; `join` resumes
-- it and the run ends failed. This is `E4-CONC-CE-016` at the trace face.
#guard rowsOf "awaitValueDistinctFromJoinEffect" ==
  [ "op\tfork\t2", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tawaitValue\t0", "answer\tawaitValue\t{\"none\":true}"
  , "op\tawaitError\t0", "answer\tawaitError\t{\"some\":1}"
  , "op\tjoin\t0", "failed\tjoin\t1"
  , "done\t{\"failure\":1}" ]

-- race-reentrant-empty-set-bypasses-late-insertion: awaiting a winner that has
-- already published runs nothing, so the late entrant is still unlaunched.
#guard tapeOf "raceReentrantEmptySetBypasses" == [(0, true), (1, false)]
#guard rowsOf "raceReentrantEmptySetBypasses" ==
  [ "op\tfork\t0", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tfork\t4", "decide\t1\tfalse", "answer\tfork\t1"
  , "op\tawaitValue\t0", "answer\tawaitValue\t{\"some\":11}"
  , "op\tstarted\t[]", "answer\tstarted\t[0, []]"
  , "op\tinterrupt\t1", "answer\tinterrupt\t[]"
  , "op\tawaitValue\t1", "answer\tawaitValue\t{\"none\":true}"
  , "done\t{\"success\":[0, []]}" ]

-- parent-interrupt-during-child-wait-changes-result: an interrupt after
-- publication cannot change the exit (`some 11` stands), and one before
-- publication replaces it (`none`).
#guard rowsOf "parentInterruptDuringChildWait" ==
  [ "op\tfork\t0", "decide\t0\ttrue", "answer\tfork\t0"
  , "op\tinterrupt\t0", "answer\tinterrupt\t[]"
  , "op\tawaitValue\t0", "answer\tawaitValue\t{\"some\":11}"
  , "op\tfork\t4", "decide\t1\ttrue", "answer\tfork\t1"
  , "op\tinterrupt\t1", "answer\tinterrupt\t[]"
  , "op\tawaitValue\t1", "answer\tawaitValue\t{\"none\":true}"
  , "done\t{\"success\":{\"none\":true}}" ]

/-! ## The five clauses of the projection

Each of these was read off the pinned rc.112 install before it was written into
`FiberTable`; the receipts here pin the Lean half. -/

/-- A table of queued children with the given body codes, none of them started. -/
def queuedTable (bodies : List Nat) : FiberTable :=
  { children := bodies.map (fun body => { body := body, daemon := false, state := .queued }) }

/-- A child's publication as a comparable pair: `(0, v)` succeeded with `v`,
`(1, e)` failed with the typed error `e`, `(2, 0)` was interrupted, `(3, 0)`
has not published. `Except` carries no `BEq`, so the receipts compare this. -/
def publication : Option (Option (Except Nat Nat)) → Nat × Nat
  | some (some (.ok value)) => (0, value)
  | some (some (.error error)) => (1, error)
  | some none => (2, 0)
  | none => (3, 0)

/-- A body's outcome as a comparable pair, in the same code, with `(9, 0)` for
a body that cannot complete at all. -/
def completion : Option (Except Nat Nat) → Nat × Nat
  | some (.ok value) => (0, value)
  | some (.error error) => (1, error)
  | none => (9, 0)

-- A drain gives the processor to *every* queued child, in fork order, not only
-- to the one forked last: rc.112 empties its run queue at a yield.
#guard (queuedTable [0, 1, 2]).drain.startOrder == [0, 1, 2]
#guard (queuedTable [0, 1, 2]).drain.cleanupOrder == [0, 1, 2]

-- A body that cannot complete becomes live: it started, and nothing of it has
-- been cleaned.
#guard (queuedTable [4]).drain.startOrder == [4]
#guard (queuedTable [4]).drain.cleanupOrder == []

-- Interrupting a queued child finishes it without ever running it, so no
-- cleanup of it runs.
#guard ((queuedTable [4]).interruptAt 0).startOrder == []
#guard ((queuedTable [4]).interruptAt 0).cleanupOrder == []
#guard publication (((queuedTable [4]).interruptAt 0).result? 0) == (2, 0)

-- Interrupting a live child runs its cleanup.
#guard ((queuedTable [4]).drain.interruptAt 0).cleanupOrder == [4]

-- Interrupting a published child changes nothing.
#guard publication (((queuedTable [0]).drain.interruptAt 0).result? 0) == (0, 11)

-- Blocking on a child that has published runs nothing; blocking on one that
-- has not drains the whole queue.
#guard ((queuedTable [0, 4]).drain.blockOn 0).startOrder == [0, 4]
#guard ((queuedTable [0, 4]).blockOn 0).startOrder == [0, 4]

/-- A published child, with a second child queued behind it. -/
def publishedThenQueued : FiberTable :=
  let table := (queuedTable [0]).drain
  { table with children := table.children ++
      [{ body := 4, daemon := false, state := .queued }] }

#guard (publishedThenQueued.blockOn 0).startOrder == [0]
#guard (publishedThenQueued.blockOn 1).startOrder == [0, 4]

/-! ## The parent's exit

`Supervision.interruptAllRequests` / `awaitAllChildren` and
`commitFork_daemon_untracked` as handler behaviour. It happens after the last
traced row, so no golden shows it; what it explains is why every program of the
corpus terminates, and why `daemonSurvivesParentExit` terminates with its child
still running. -/

/-- One daemon running a body that never completes. -/
def daemonTable : FiberTable :=
  { children := [{ body := 4, daemon := true, state := .queued }] }

-- A tracked child that is still live when the parent exits is interrupted and
-- cleaned, and nothing is left running.
#guard ((queuedTable [4]).drain.parentExit).cleanupOrder == [4]
#guard ((queuedTable [4]).drain.parentExit).liveBodies == []

-- A tracked child that never started is finished without ever running.
#guard ((queuedTable [4]).parentExit).startOrder == []
#guard ((queuedTable [4]).parentExit).cleanupOrder == []
#guard publication (((queuedTable [4]).parentExit).result? 0) == (2, 0)

-- A daemon in the same position survives the parent's exit uncleaned, which is
-- the whole content of `daemonSurvivesParentExit`.
#guard (daemonTable.drain.parentExit).cleanupOrder == []
#guard (daemonTable.drain.parentExit).liveBodies == [4]

-- The body table, which the host tail carries character for character.
#guard (List.range 6).map (fun code => completion (bodyOutcome code)) ==
  [(0, 11), (0, 22), (1, 1), (1, 2), (9, 0), (9, 0)]

end Effect4Test.Flow.FibersContract
