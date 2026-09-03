/-
# `Deferreds` counterexamples

Two attacks on the traced one-shot-cell family
(`harness/trace/Generate.lean`, `Effect4Test/Flow/DeferredsContract.lean`),
register rows `E4-SEM-CE-012` and `E4-SEM-CE-013`.

Both are about the same gap: rc.112's `Deferred.await` on a *pending* cell
suspends the fiber until another fiber completes it, and the sequential
projection has neither suspension nor another fiber. Each theorem is finite and
proves only its named attack; neither is a production law.

Pinned source: `effect@4.0.0-rc.112`, `Deferred.ts` (`_await` registers a
resume on `self.resumes` and parks; `poll` answers `None` and does not park).
-/

import Effect4.Semantics.Observation

set_option autoImplicit false

namespace Effect4Test.Counterexamples.Flow.Deferreds

open Effects

/-! ## `E4-SEM-CE-012` — a pending await is not a failure

The attacked statement: *an operation that cannot answer has failed, so the
traced service may report a pending `await` through its declared error channel*
— which is what `Family.Service.tracedExcept` would do, since it writes a
`failed` row for every abort, and what the outcome would be if the stall were
the program's error.

The attack: the error channel of `awaitValue` is `Nat`, so the failure reading
has to choose a payload. Whatever it chooses, some genuine failure carries it,
and the two runs render identically — under every registered mask. On the host
one of them returned and the other never will.
-/

/-- The cell completed with the failure `0`; `awaitValue` aborts, and the run
ends in that failure. This run terminates on rc.112. -/
def failedWithZero : Effect4.Trace.Log :=
  [ .op "awaitValue" (.nat 0)
  , .failed "awaitValue" (.nat 0)
  , .done (.failure (.nat 0)) ]

/-- The attacked reading of a *pending* await on the same handle: a `failed`
row through the declared error channel, and the stall as the outcome. On
rc.112 this run has not ended and will not end. -/
def stallAsFailure : Effect4.Trace.Log :=
  [ .op "awaitValue" (.nat 0)
  , .failed "awaitValue" (.nat 0)
  , .done (.failure (.nat 0)) ]

/-- The failure reading collapses the two runs: the logs are equal, so no mask
can separate them and no host comparison can catch the difference. -/
theorem stall_as_failure_is_indistinguishable : stallAsFailure = failedWithZero := rfl

/-- Every registered mask agrees on them, including `m2`, which keeps
everything. Agreement is the whole evidence the host gate has. -/
theorem stall_as_failure_agrees_under_every_mask :
    Effect4.Trace.maskTable.all
      (fun entry => Effect4.Trace.agree entry.2 stallAsFailure failedWithZero) = true := by
  decide

/-- The frozen reading: the `op` row, then nothing. No answer, no failure, no
outcome — the trace stops where the information stops. -/
def stallAsFrontier : Effect4.Trace.Log :=
  [ .op "awaitValue" (.nat 0)
  , .frontier ]

/-- It separates the stall from the genuine failure under the coarsest mask
there is, which keeps only outcomes and frontiers. -/
theorem frontier_separates_under_the_outcome_mask :
    Effect4.Trace.agree Trace.Mask.outcomeOnly stallAsFrontier failedWithZero = false := by
  decide

/-- And under every other mask as well. -/
theorem frontier_separates_under_every_mask :
    Effect4.Trace.maskTable.all
      (fun entry => !Effect4.Trace.agree entry.2 stallAsFrontier failedWithZero) = true := by
  decide

/-- The frontier reading writes no outcome row at all: a frontier annotates a
run that has not ended, and an outcome says how a run ended. -/
theorem frontier_log_has_no_outcome :
    stallAsFrontier.all (fun event =>
      match event with | .done _ => false | _ => true) = true := by
  decide

/-! ## `E4-SEM-CE-013` — the sequential projection is not the whole behaviour

The attacked statement: *the projection's step is a function of its table, so a
golden that stops at a frontier records everything the program can do.*

The attack: on rc.112 the same parked await resumes when another fiber
completes the cell, and the table at the moment of the await is the same in
both runs. No function of that table can answer `none` in one and `some 7` in
the other, so the frontier is a limit of the *projection*, not of the program.
The two-fiber golden that would record the resumption is owed
(`harness/trace/Generate.lean`, the note on `DeferredEntry`): `effect_program`
binds one family per program, so a program that forks a child and awaits a cell
the child completes cannot yet be spelled.
-/

/-- A miniature table: one cell, pending or completed with a value. -/
abbrev MiniTable := List (Option Nat)

/-- The parent's await as the sequential projection has it: a function of the
table alone. -/
def awaitSeq (table : MiniTable) : Option Nat := (table[0]?).getD none

/-- The same await with one other fiber, which may complete the cell while the
parent is parked. `none` is the sequential run. -/
def awaitWithChild (child : Option Nat) (table : MiniTable) : Option Nat :=
  awaitSeq (match child with | none => table | some value => table.set 0 (some value))

/-- Two runs from the same table: parked forever, or answered by the child. -/
theorem the_child_changes_the_answer :
    awaitSeq [none] = none ∧ awaitWithChild (some 7) [none] = some 7 := by
  decide

/-- No function of the table alone matches both, so the projection cannot be
completed into the host's behaviour by reading more of its own state. -/
theorem no_state_function_matches_both (f : MiniTable → Option Nat) :
    ¬ (f [none] = awaitSeq [none] ∧ f [none] = awaitWithChild (some 7) [none]) := by
  rintro ⟨sequential, withChild⟩
  rw [sequential] at withChild
  exact absurd withChild (by decide)

/-- What the projection may still say: the frontier is reached at exactly the
handle the parent awaited, and the rows before it are the rows both runs
share. That prefix is what the golden freezes. -/
theorem the_shared_prefix_is_the_frontier_log :
    stallAsFrontier.take 1 = [Trace.Event.op "awaitValue" (Trace.Val.nat 0)] := rfl

end Effect4Test.Counterexamples.Flow.Deferreds
