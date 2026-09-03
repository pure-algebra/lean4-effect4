/-
Contract packet: the trace lane (`docs/TRACE-DAG.md`), the `Deferreds` family.
Light ceremony by operator ruling D2: contract, battery and code land together.

Frozen: the operation rows of the one-shot cell family, the sequential
projection it runs under in Lean, and the traced log of every program the
harness carries a golden for (`generated/traces/deferred/*.tsv`).

The family is re-declared here rather than imported: `harness/trace/Generate.lean`
is a script, not a library, and `Effect4Test/Semantics/ObservationContract.lean`
sets the precedent (it re-declares `Cell`). The two declarations must stay
byte-equal in content; a drift shows up as a failing `#guard` below, because
these logs are exactly the rows the goldens carry.

What this battery does *not* say: anything about rc.112. The host facts the
Lean face cannot express are register rows `E4-SEM-CE-012` and `E4-SEM-CE-013`,
witnessed in `Effect4Test/Counterexamples/Flow/Deferreds.lean`.
-/

import Effect4.Semantics.Observation
import Effect4.Meta.Derive

set_option linter.unusedVariables false

namespace Effect4Test.Flow.DeferredsContract

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

/-! ## The family -/

/-- The handle a `Deferreds` operation takes and returns: `Effect4.Meta.Handle`
carrying an index, spelled on the target as rc.112's own `Deferred`. -/
abbrev DeferredHandle := Handle "Deferred.Deferred<number, number>"

effect_signature Deferreds where
  | make : Handle "Deferred.Deferred<number, number>"
      ⟪ "make a one-shot cell", "the cell's handle" ⟫
  | succeed (cell : Handle "Deferred.Deferred<number, number>") (value : Nat) : Bool
      ⟪ "complete it with a value", "false if it was already completed" ⟫
  | fail (cell : Handle "Deferred.Deferred<number, number>") (error : Nat) : Bool
      ⟪ "complete it with a failure", "false if it was already completed" ⟫
  | isDone (cell : Handle "Deferred.Deferred<number, number>") : Bool
      ⟪ "has it completed" ⟫
  | poll (cell : Handle "Deferred.Deferred<number, number>") : Option (Except Nat Nat)
      ⟪ "read it without waiting", "none while pending" ⟫
  | awaitValue (cell : Handle "Deferred.Deferred<number, number>") : Nat !! Nat
      ⟪ "wait for its value", "its failure, resumed here" ⟫
  | awaitError (cell : Handle "Deferred.Deferred<number, number>") : Nat !! Nat
      ⟪ "wait for its failure", "its value, resumed here" ⟫

/-! ### The frozen rows

The names and their order, the arities, and the TypeScript spellings the
profile emits. `poll` is the Stratum V spelling that carries the whole state of
a cell in one answer; `awaitValue`/`awaitError` are the aborting reading. -/

#guard Deferreds.rows.name = "Deferreds"
#guard Deferreds.rows.ops.map (·.name) =
  ["make", "succeed", "fail", "isDone", "poll", "awaitValue", "awaitError"]
#guard Deferreds.rows.ops.map (·.params.length) = [0, 2, 2, 1, 1, 1, 1]
#guard Deferreds.rows.ops.map (·.tsAnswer) =
  ["Deferred.Deferred<number, number>", "boolean", "boolean", "boolean",
   "Option.Option<Result.Result<number, number>>", "number", "number"]
#guard Deferreds.rows.ops.map (·.tsParams.map (·.2)) =
  [[], ["Deferred.Deferred<number, number>", "number"],
   ["Deferred.Deferred<number, number>", "number"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>"], ["Deferred.Deferred<number, number>"],
   ["Deferred.Deferred<number, number>"]]
#guard Deferreds.rows.ops.map (·.error) =
  [none, none, none, none, none, some ("Nat", "number"), some ("Nat", "number")]

/-! The service class the profile emits: the handle prints as rc.112's own
`Deferred`, and `poll`'s answer is the depth-two Stratum V spelling. -/
#guard Deferreds.rows.shapeType =
  "{\n" ++
  "  readonly make: Effect.Effect<Deferred.Deferred<number, number>>\n" ++
  "  readonly succeed: (cell: Deferred.Deferred<number, number>, value: number) => Effect.Effect<boolean>\n" ++
  "  readonly fail: (cell: Deferred.Deferred<number, number>, error: number) => Effect.Effect<boolean>\n" ++
  "  readonly isDone: (cell: Deferred.Deferred<number, number>) => Effect.Effect<boolean>\n" ++
  "  readonly poll: (cell: Deferred.Deferred<number, number>) => Effect.Effect<Option.Option<Result.Result<number, number>>>\n" ++
  "  readonly awaitValue: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>\n" ++
  "  readonly awaitError: (cell: Deferred.Deferred<number, number>) => Effect.Effect<number, number>\n" ++
  "}"

/-! `poll`'s answer nests one namespace inside another. Since the answer-profile
packet the namespace test is by occurrence (`Spelling.namespacesOf`), so
`Result` counts as used wherever it appears; the module's imports are computed
from the namespaces a spelling mentions, and `deferred-fixture.ts` is byte-stable
across that change. -/
#guard Deferreds.rows.usesResult

/-! ## The sequential projection -/

/-- One cell per handle: `none` pending, `some (.ok v)` completed with a value,
`some (.error e)` completed with a failure. It is the answer type of `poll`. -/
abbrev DeferredTable := List (Option (Except Nat Nat))

/-- Why a run stopped before its `return`. `failed` is the declared error
channel; `pending` is a frontier, not a failure. -/
inductive Stall where
  | failed (payload : Nat)
  | pending (cell : DeferredHandle)
deriving DecidableEq, Repr

def deferredCell (table : DeferredTable) (cell : DeferredHandle) : Option (Except Nat Nat) :=
  (table[cell.index]?).getD none

def deferredStep : (name : Deferreds.Name) → Deferreds.Param name → DeferredTable →
    Except Stall (Deferreds.Answer name) × DeferredTable
  | .make, _, table => (.ok ⟨table.length⟩, table ++ [none])
  | .succeed, (cell, value), table =>
      match table[cell.index]? with
      | some none => (.ok true, table.set cell.index (some (.ok value)))
      | _ => (.ok false, table)
  | .fail, (cell, error), table =>
      match table[cell.index]? with
      | some none => (.ok true, table.set cell.index (some (.error error)))
      | _ => (.ok false, table)
  | .isDone, cell, table => (.ok (deferredCell table cell).isSome, table)
  | .poll, cell, table => (.ok (deferredCell table cell), table)
  | .awaitValue, cell, table =>
      match deferredCell table cell with
      | some (.ok value) => (.ok value, table)
      | some (.error error) => (.error (.failed error), table)
      | none => (.error (.pending cell), table)
  | .awaitError, cell, table =>
      match deferredCell table cell with
      | some (.error error) => (.ok error, table)
      | some (.ok value) => (.error (.failed value), table)
      | none => (.error (.pending cell), table)

abbrev DeferredM := ExceptT Stall (StateT (DeferredTable × Effect4.Trace.Log) Id)

/-- An answered operation writes `op` then `answer`; an aborting one writes
`op` then `failed`; a pending await writes `op` and nothing else, because on
the host the method never returns. -/
def deferredsTraced : Deferreds.Service DeferredM := fun name param => ExceptT.mk do
  let (table, log) ← get
  let (result, table') := deferredStep name param table
  set (table',
    log ++ [Effects.Trace.Event.op (Deferreds.Name.spelling name) (Deferreds.encodeParam name param)] ++
      (match result with
       | .ok answer =>
           [Effects.Trace.Event.answer (Deferreds.Name.spelling name) (Deferreds.encodeAnswer name answer)]
       | .error (.failed payload) =>
           [Effects.Trace.Event.failed (Deferreds.Name.spelling name) (.nat payload)]
       | .error (.pending _) => []))
  pure result

def deferredGoldenLog (program : Program Deferreds.Sig Nat) : Effect4.Trace.Log :=
  let result : Except Stall Nat × (DeferredTable × Effect4.Trace.Log) :=
    (interpret deferredsTraced.toHandler program).run.run ([], [])
  result.2.2 ++
    (match result.1 with
     | .ok value => [.done (.success (.nat value))]
     | .error (.failed payload) => [.done (.failure (.nat payload))]
     | .error (.pending _) => [.frontier])

/-! ### Laws of the projection

Four statements about the table alone, each `rfl` or `decide`, so the axiom
report below can hold them to the `propext`/`Quot.sound` ceiling. -/

/-- `isDone` is exactly `poll`'s `isSome`: one observation, two operations. -/
theorem isDone_eq_poll_isSome (table : DeferredTable) (cell : DeferredHandle) :
    (deferredStep .isDone cell table).1 = Except.ok (deferredCell table cell).isSome :=
  rfl

/-- Completion is one-shot on the value side: the second `succeed` answers
`false`, and the cell keeps the value the first one stored. -/
theorem succeed_once (value other : Nat) :
    deferredStep .succeed (⟨0⟩, other) (deferredStep .succeed (⟨0⟩, value) [none]).2 =
      (Except.ok false, [some (Except.ok value)]) :=
  rfl

/-- Completion is one-shot on the failure side, and a `fail` after a `succeed`
does not overwrite it either. -/
theorem fail_after_succeed (value error : Nat) :
    deferredStep .fail (⟨0⟩, error) (deferredStep .succeed (⟨0⟩, value) [none]).2 =
      (Except.ok false, [some (Except.ok value)]) :=
  rfl

/-- A completed cell answers its await; the table is untouched. -/
theorem awaitValue_of_completed (value : Nat) (table : DeferredTable) :
    deferredStep .awaitValue ⟨0⟩ (some (Except.ok value) :: table) =
      (Except.ok value, some (Except.ok value) :: table) :=
  rfl

/-- A pending cell has no await answer at all. This is the whole content of
the sequential projection's limit: not a failure, not an answer, a stall. -/
theorem awaitValue_pending (table : DeferredTable) :
    (deferredStep .awaitValue ⟨0⟩ (none :: table)).1 = Except.error (.pending ⟨0⟩) :=
  rfl

/-- And the stall renders as a `frontier`, never as an outcome row. -/
theorem pendingAwait_is_a_frontier :
    (deferredGoldenLog
      (Deferreds.make >>= fun d => Deferreds.awaitValue d)).getLast? = some .frontier :=
  rfl

/-! ## The programs, and the rows the goldens carry

The pure atoms are the Lean models of the bodies `harness/trace/atoms.ts`
carries; the lowered programs call them by name. -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def flagToNat (flag : Bool) : Nat := if flag then 1 else 0

/-- The value a completed `poll` found; `0` while pending or failed. -/
def pollValue (cell : Option (Except Nat Nat)) : Nat :=
  match cell with
  | some (.ok value) => value
  | _ => 0

/-- Addition as a named atom. -/
def addNat (left right : Nat) : Nat := left + right

effect_program deferredSucceedAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.succeed(d, n)
  let v ← Deferreds.awaitValue(d)
  return v

effect_program deferredFailAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.fail(d, n)
  let e ← Deferreds.awaitError(d)
  return e

effect_program deferredDoubleComplete (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.succeed(d, n)
  let again ← Deferreds.succeed(d, 9)
  return flagToNat again

effect_program deferredPollPending (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.poll(d)
  let _ ← Deferreds.succeed(d, n)
  let after ← Deferreds.poll(d)
  return pollValue after

effect_program deferredTwoHandles (n : Nat) over Deferreds : Nat :=
  let a ← Deferreds.make()
  let b ← Deferreds.make()
  let _ ← Deferreds.succeed(a, n)
  let _ ← Deferreds.fail(b, 3)
  let x ← Deferreds.awaitValue(a)
  let y ← Deferreds.awaitError(b)
  return addNat x y

effect_program deferredPendingAwait (n : Nat) over Deferreds : Nat :=
  let d ← Deferreds.make()
  let _ ← Deferreds.isDone(d)
  let v ← Deferreds.awaitValue(d)
  return v

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

/-! A frontier is not an outcome: the pending log has no `done` row, and the
completed log has one. Separation 5 of `docs/TRACE-DAG.md`. -/
#guard (deferredGoldenLog (deferredPendingAwait 1)).all (fun event =>
    match event with | .done _ => false | _ => true)
#guard (deferredGoldenLog (deferredSucceedAwait 7)).any (fun event =>
    match event with | .done _ => true | _ => false)

/-! ### The declaration lines the pinned compiler must emit -/

#guard Script.declarationLine Deferreds.rows deferredSucceedAwait.script =
  "export declare const deferredSucceedAwait: (n: number) => Effect.Effect<number, number, Deferreds>;"
#guard Script.declarationLine Deferreds.rows deferredPollPending.script =
  "export declare const deferredPollPending: (n: number) => Effect.Effect<number, never, Deferreds>;"

end Effect4Test.Flow.DeferredsContract
