/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), the `Deferreds` family.
Light ceremony by operator ruling D2: contract, battery and code land together.

Frozen: the sixteen operation rows of the one-shot cell family, the sequential
projection it runs under in Lean, and the traced log of every program the
harness carries a golden for (`generated/traces/deferred/*.tsv`).

**The family is imported now, not re-declared.** Before lowering lane L3 the
signature, the store and the six programs were written out twice — once in
`harness/trace/Generate.lean` and once here — and this header said so. Two
copies of a handler can drift while every receipt about either still passes,
which is what made the duplication worth removing rather than documenting (deep
plan §5, decision 3). The one declaration site is
`Effect4/Stateful/DeferredFamily.lean`, which is under `Effect4/` and therefore
audited by `#effect4_axiom_gate`; the script imports it, and so does this
battery.

Nine rows were added to the seven the goldens were generated from, one per
remaining rc.112 entry point. The seven keep their spelling, their order and
their answers exactly, so **all six goldens under `generated/traces/deferred/`
are unchanged** and the receipts below are byte-identical to the ones the
four-row era carried.

What this battery does *not* say: anything about rc.112. The host facts the
Lean face cannot express are register rows `E4-SEM-CE-012` and `E4-SEM-CE-013`,
witnessed in `Effect4Test/Counterexamples/Flow/Deferreds.lean`.
-/

import Effect4.Stateful.DeferredFamily
import Effect4.Semantics.Observation

set_option linter.unusedVariables false

namespace Effect4Test.Flow.DeferredsContract

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4
open Effect4.DeferredFamily

#check @Effect4.DeferredFamily.Deferreds
#check (@Effect4.DeferredFamily.Deferreds.rows : ServiceRow)
#check @Effect4.DeferredFamily.deferredStep
#check @Effect4.DeferredFamily.deferredsTraced
#check @Effect4.DeferredFamily.deferredGoldenLog

/-! ## The frozen rows

The names and their order, the arities, and the TypeScript spellings the
profile emits. `poll` is the Stratum V spelling that carries the whole state of
a cell in one answer; `awaitValue`/`awaitError` are the aborting reading; and
`awaitDeferred` is rc.112's `_await` under a name the generated-binding profile
admits (`await` is reserved, `Effect4/Target/TypeScript/EffectV4.lean`
`bindingName`). -/

#guard Deferreds.rows.name = "Deferreds"

#guard Deferreds.rows.ops.map (·.name) =
  ["make", "succeed", "fail", "isDone", "poll", "awaitValue", "awaitError", "awaitDeferred",
   "failCause", "die", "interrupt", "interruptWith", "complete", "completeWith", "done", "into"]

-- The first seven are the frozen prefix: order, arity and answer are exactly
-- what `generated/traces/deferred/` was generated against.
#guard (Deferreds.rows.ops.take 7).map (·.name) =
  ["make", "succeed", "fail", "isDone", "poll", "awaitValue", "awaitError"]

#guard Deferreds.rows.ops.map (·.params.length) =
  [0, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2]

#guard Deferreds.rows.ops.map (·.tsAnswer) =
  ["Deferred.Deferred<number, number>", "boolean", "boolean", "boolean",
   "Option.Option<Result.Result<number, number>>", "number", "number",
   "Result.Result<number, number>", "boolean", "boolean", "boolean", "boolean",
   "boolean", "boolean", "boolean", "boolean"]

#guard Deferreds.rows.ops.map (·.tsParams.map (·.2)) =
  [[], ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "number"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "number"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "Result.Result<number, number>"],
   ["Deferred.Deferred<number, number>", "number"]]

-- Only the two aborting reads declare an error channel; every other refusal in
-- this lane is data or a frontier.
#guard Deferreds.rows.ops.map (·.error) =
  [none, none, none, none, none, some ("Nat", "number"), some ("Nat", "number"),
   none, none, none, none, none, none, none, none, none]

/-! The service class the profile emits: the handle prints as rc.112's own
`Deferred`, `poll`'s answer is the depth-two Stratum V spelling, and `done`
takes an `Exit`-shaped `Result` where every other completion takes a number. -/
#guard Deferreds.rows.shapeType =
  "{\n" ++
  "  readonly make: Effect.Effect<Deferred.Deferred<number, number>>\n" ++
  "  readonly succeed: (cell: Deferred.Deferred<number, number>, value: number) => Effect.Effect<boolean>\n" ++
  "  readonly fail: (cell: Deferred.Deferred<number, number>, error: number) => Effect.Effect<boolean>\n" ++
  "  readonly isDone: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>\n" ++
  "  readonly poll: (cell: Deferred.Deferred<number, number>) => Effect.Effect<Option.Option<Result.Result<number, number>>>\n" ++
  "  readonly awaitValue: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>\n" ++
  "  readonly awaitError: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>\n" ++
  "  readonly awaitDeferred: (cell: Deferred.Deferred<number, number>) => Effect.Effect<Result.Result<number, number>>\n" ++
  "  readonly failCause: (cell: Deferred.Deferred<number, number>, error: number) => Effect.Effect<boolean>\n" ++
  "  readonly die: (cell: Deferred.Deferred<number, number>, defect: number) => Effect.Effect<boolean>\n" ++
  "  readonly interrupt: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>\n" ++
  "  readonly interruptWith: (cell: Deferred.Deferred<number, number>, fiber: number) => Effect.Effect<boolean>\n" ++
  "  readonly complete: (cell: Deferred.Deferred<number, number>, effect: number) => Effect.Effect<boolean>\n" ++
  "  readonly completeWith: (cell: Deferred.Deferred<number, number>, effect: number) => Effect.Effect<boolean>\n" ++
  "  readonly done: (cell: Deferred.Deferred<number, number>, exit: Result.Result<number, number>) => Effect.Effect<boolean>\n" ++
  "  readonly into: (cell: Deferred.Deferred<number, number>, body: number) => Effect.Effect<boolean>\n" ++
  "}"

/-! `poll`'s answer nests one namespace inside another. Since the answer-profile
packet the namespace test is by occurrence (`Spelling.namespacesOf`), so
`Result` counts as used wherever it appears; the module's imports are computed
from the namespaces a spelling mentions, and `deferred-fixture.ts` is byte-stable
across that change. -/
#guard Deferreds.rows.usesResult

/-! ## The handler is a projection of the Deferred store

Every completion row goes through `DeferredStore.complete`, which is
`doneUnsafe` (`Deferred.ts:1648-1662`); the clauses are in
`Effect4/Stateful/DeferredFamily.lean` and their axiom receipts in
`Effect4Test/Flow/DeferredsAxiomReport.lean`. -/

#check @Effect4.DeferredFamily.deferredStep_make
#check @Effect4.DeferredFamily.deferredStep_succeed
#check @Effect4.DeferredFamily.done_eq_complete_of_exit
#check @Effect4.DeferredFamily.interrupt_is_interruptWith_self
#check @Effect4.DeferredFamily.completeWith_stores_the_name
#check @Effect4.DeferredFamily.complete_twice_is_false
#check @Effect4.DeferredFamily.complete_clears_then_owes
#check @Effect4.DeferredFamily.isDone_of_completion
#check @Effect4.DeferredFamily.awaitDeferred_pending_registers
#check @Effect4.DeferredFamily.cancel_splices_the_waiter
#check @Effect4.DeferredFamily.cancel_after_complete_is_a_noop
#check @Effect4.DeferredFamily.complete_of_done_does_not_run

/-! ### Laws of the projection

The six statements the four-row era carried, restated over the store the
library owns. Each is `rfl`, so the axiom report below can hold them to the
`propext`/`Quot.sound` ceiling. -/

/-- `isDone` is exactly `poll`'s `isSome`: one observation, two operations. -/
theorem isDone_eq_poll_isSome (store : DeferredStore) (cell : DeferredHandle) :
    (deferredStep .isDone cell store).1 = Except.ok (store.poll cell).isSome := by
  cases h : store.cellAt cell <;> simp [deferredStep, DeferredStore.isDone, DeferredStore.poll, h]

/-- Completion is one-shot on the value side: the second `succeed` answers
`false`, and the cell keeps the value the first one stored. -/
theorem succeed_once (value other : Nat) :
    deferredStep .succeed (⟨0⟩, other)
        (deferredStep .succeed (⟨0⟩, value) ({ cells := [{}] } : DeferredStore)).2 =
      (Except.ok false, ({ cells := [⟨Option.some (.success value), []⟩] } : DeferredStore)) :=
  rfl

/-- Completion is one-shot on the failure side, and a `fail` after a `succeed`
does not overwrite it either. -/
theorem fail_after_succeed (value error : Nat) :
    deferredStep .fail (⟨0⟩, error)
        (deferredStep .succeed (⟨0⟩, value) ({ cells := [{}] } : DeferredStore)).2 =
      (Except.ok false, ({ cells := [⟨Option.some (.success value), []⟩] } : DeferredStore)) :=
  rfl

/-- A completed cell answers its await; the store is untouched. -/
theorem awaitValue_of_completed (value : Nat) (rest : List DeferredCell)
    (due : List (Nat × Nat × Completion)) :
    deferredStep .awaitValue ⟨0⟩
        ({ cells := ⟨Option.some (.success value), []⟩ :: rest, due := due } : DeferredStore) =
      (Except.ok value,
        ({ cells := ⟨Option.some (.success value), []⟩ :: rest, due := due } : DeferredStore)) :=
  rfl

/-- A pending cell has no await answer at all. This is the whole content of
the sequential projection's limit: not a failure, not an answer, a stall. -/
theorem awaitValue_pending (rest : List DeferredCell) (due : List (Nat × Nat × Completion)) :
    (deferredStep .awaitValue ⟨0⟩
      ({ cells := ({} : DeferredCell) :: rest, due := due } : DeferredStore)).1 =
      Except.error (.pending ⟨0⟩) :=
  rfl

/-- And the stall renders as a `frontier`, never as an outcome row. -/
theorem pendingAwait_is_a_frontier :
    (deferredGoldenLog
      (Deferreds.make >>= fun d => Deferreds.awaitValue d)).getLast? = some .frontier :=
  rfl

/-! ### The waiter list the four-row store did not have

`_await` on a pending cell registers `(fiber, token)` in registration order and
a completion clears the array *before* it owes the resumes
(`Deferred.ts:173-177`, `:1648-1662`). No row observes either, so both are
theorems about the store; that is the whole forgetful direction of this
family's join. -/

-- A pending await leaves one waiter behind, in registration order.
#guard decide ((deferredStep .awaitValue ⟨0⟩ ({ cells := [{}] } : DeferredStore)).2
  = ({ cells := [⟨Option.none, [(selfFiber, 0)]⟩] } : DeferredStore))

-- And the completion after it clears the array and owes exactly that resume.
#guard decide (
  ((({ cells := [⟨Option.none, [(selfFiber, 0)]⟩] } : DeferredStore).complete ⟨0⟩ (.success 7)).1)
    = ({ cells := [⟨Option.some (.success 7), []⟩], due := [(selfFiber, 0, .success 7)] }
        : DeferredStore))

/-! ## The programs, and the rows the goldens carry

The corpus and its pure atoms are the library's; the lowered programs call the
atoms by name and `harness/trace/atoms.ts` carries the same bodies. -/

#guard deferredEntries.length == 11

#guard deferredEntries.map (·.name) ==
  [ "deferredSucceedAwait", "deferredFailAwait", "deferredDoubleComplete", "deferredPollPending"
  , "deferredTwoHandles", "deferredPendingAwait", "deferredDoneAwait", "deferredInterruptIsDone"
  , "deferredCompleteRunsOnce", "deferredIntoFailingBody", "deferredCompleteWithStoresEffect" ]

-- The six that have a golden come first, and their rows are unchanged.
#guard (deferredEntries.take 6).map (·.name) ==
  [ "deferredSucceedAwait", "deferredFailAwait", "deferredDoubleComplete", "deferredPollPending"
  , "deferredTwoHandles", "deferredPendingAwait" ]

#guard deferredGoldenLog (deferredSucceedAwait 7) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "succeed" (.pair (.nat 0) (.nat 7)), .answer "succeed" (.bool true)
  , .op "awaitValue" (.nat 0), .answer "awaitValue" (.nat 7)
  , .done (.success (.nat 7)) ]

#guard deferredGoldenLog (deferredFailAwait 5) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "fail" (.pair (.nat 0) (.nat 5)), .answer "fail" (.bool true)
  , .op "awaitError" (.nat 0), .answer "awaitError" (.nat 5)
  , .done (.success (.nat 5)) ]

#guard deferredGoldenLog (deferredDoubleComplete 4) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "succeed" (.pair (.nat 0) (.nat 4)), .answer "succeed" (.bool true)
  , .op "succeed" (.pair (.nat 0) (.nat 9)), .answer "succeed" (.bool false)
  , .done (.success (.nat 0)) ]

#guard deferredGoldenLog (deferredPollPending 6) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "poll" (.nat 0), .answer "poll" .none
  , .op "succeed" (.pair (.nat 0) (.nat 6)), .answer "succeed" (.bool true)
  , .op "poll" (.nat 0), .answer "poll" (.some (.pair (.bool true) (.nat 6)))
  , .done (.success (.nat 6)) ]

#guard deferredGoldenLog (deferredTwoHandles 8) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "make" .unit, .answer "make" (.nat 1)
  , .op "succeed" (.pair (.nat 0) (.nat 8)), .answer "succeed" (.bool true)
  , .op "fail" (.pair (.nat 1) (.nat 3)), .answer "fail" (.bool true)
  , .op "awaitValue" (.nat 0), .answer "awaitValue" (.nat 8)
  , .op "awaitError" (.nat 1), .answer "awaitError" (.nat 3)
  , .done (.success (.nat 11)) ]

/-! The frontier program: the `op` row is written, and then nothing. No
`answer`, no `failed`, no `done`. -/
#guard deferredGoldenLog (deferredPendingAwait 1) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "isDone" (.nat 0), .answer "isDone" (.bool false)
  , .op "awaitValue" (.nat 0)
  , .frontier ]

/-! ### The five programs the added rows own -/

-- `done` of an exit read back through `awaitDeferred`: one answer carrying the
-- whole result (`Deferred.ts:571`).
#guard deferredGoldenLog (deferredDoneAwait 3) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "done" (.pair (.nat 0) (.pair (.bool true) (.nat 3))), .answer "done" (.bool true)
  , .op "awaitDeferred" (.nat 0), .answer "awaitDeferred" (.pair (.bool true) (.nat 3))
  , .done (.success (.nat 3)) ]

-- An interrupt is an ordinary stored completion: `isDone` sees it and a later
-- `succeed` answers `false`. Its payload is not a value this profile spells,
-- which is why the program never polls it. counterexample: E4-SEM-CE-012
#guard deferredGoldenLog (deferredInterruptIsDone 2) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "interrupt" (.nat 0), .answer "interrupt" (.bool true)
  , .op "isDone" (.nat 0), .answer "isDone" (.bool true)
  , .op "succeed" (.pair (.nat 0) (.nat 2)), .answer "succeed" (.bool false)
  , .done (.success (.nat 1)) ]

-- `complete` on a done cell answers `false` *without running* the effect
-- (`Deferred.ts:333-334`), which is what separates it from `completeWith`.
#guard deferredGoldenLog (deferredCompleteRunsOnce 1) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "complete" (.pair (.nat 0) (.nat 0)), .answer "complete" (.bool true)
  , .op "complete" (.pair (.nat 0) (.nat 1)), .answer "complete" (.bool false)
  , .op "awaitDeferred" (.nat 0), .answer "awaitDeferred" (.pair (.bool true) (.nat 11))
  , .done (.success (.nat 1)) ]

-- `into` on a failing body still completes the cell (`Deferred.ts:1776-1783`).
#guard deferredGoldenLog (deferredIntoFailingBody 1) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "into" (.pair (.nat 0) (.nat 1)), .answer "into" (.bool true)
  , .op "isDone" (.nat 0), .answer "isDone" (.bool true)
  , .done (.success (.nat 2)) ]

-- `completeWith` stores the argument effect and never runs it
-- (`Deferred.ts:458-460`), so the cell is done, a second completion answers
-- `false`, and the `poll` after that is a frontier: the answer profile has no
-- spelling for a stored effect. counterexample: E4-SEM-CE-012
#guard deferredGoldenLog (deferredCompleteWithStoresEffect 1) =
  [ .op "make" .unit, .answer "make" (.nat 0)
  , .op "completeWith" (.pair (.nat 0) (.nat 7)), .answer "completeWith" (.bool true)
  , .op "isDone" (.nat 0), .answer "isDone" (.bool true)
  , .op "poll" (.nat 0)
  , .frontier ]

/-! A frontier is not an outcome: the pending log has no `done` row, and the
completed log has one. Separation 5 of `docs/TRACE-DAG.md`. -/
#guard (deferredGoldenLog (deferredPendingAwait 1)).all (fun event =>
    match event with | .done _ => false | _ => true)
#guard (deferredGoldenLog (deferredSucceedAwait 7)).any (fun event =>
    match event with | .done _ => true | _ => false)

-- Exactly two programs of the corpus end in a frontier, and each is a frontier
-- for its own reason: a pending await, and a completion the profile cannot
-- spell.
#guard (deferredEntries.filter (fun entry => entry.log.getLast? == some .frontier)).map (·.name)
  == ["deferredPendingAwait", "deferredCompleteWithStoresEffect"]

/-! ### The declaration lines the pinned compiler must emit -/

#guard Script.declarationLine Deferreds.rows deferredSucceedAwait.script =
  "export declare const deferredSucceedAwait: (n: number) => Effect.Effect<number, number, Deferreds>;"
#guard Script.declarationLine Deferreds.rows deferredPollPending.script =
  "export declare const deferredPollPending: (n: number) => Effect.Effect<number, never, Deferreds>;"

end Effect4Test.Flow.DeferredsContract
