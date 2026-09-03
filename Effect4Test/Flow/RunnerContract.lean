/-
Contract packet: `test/contracts/flow-runner.contract.md` (P-T2, light ceremony D2).

Frozen: the decision tape, the frontier, the runner, and the straight-line
embedding. Executable receipts: tape reads; the `incr` script embedded, admitted,
and run agrees with the traced service under `m2`; fuel and tape exhaustion are
frontiers; a foreign tape entry is a refusal; a chosen loop consumes its tape.
Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Semantics.Runs
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Meta.Derive

namespace Effect4Test.Flow.RunnerContract

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## The frozen surface -/

#check (@Effect4.Flow.Decision : Type)
#check (@Effect4.Flow.Tape : Type)
#check (@Effect4.Flow.TapeRead : Type)
#check (@Effect4.Flow.Tape.read : Tape → DecisionId → TapeRead)
#check (@Effect4.Flow.Tape.wire : Tape → List (Nat × Bool))
#check (@Effect4.Frontier : Type)
#check (@Effect4.Flow.RunResult : Type)
#check (@Effect4.Flow.RunResult.exhausted : RunResult → Bool)
#check (@Effect4.Flow.RunResult.stuck : RunResult → Bool)
#check @Effect4.Flow.FlowService
#check @Effect4.Flow.plan
#check @Effect4.Flow.step
#check @Effect4.Flow.loop
#check @Effect4.Flow.run
#check @Effect4.Flow.runTape
#check @Effect4.Flow.runDefault
#check @Effect4.Flow.fuelFor
#check @Effect4.Flow.Tape.read_answered_length
#check @Effect4.Flow.step_choose_consumes_one
#check @Effect4.Flow.plan_checked
#check @Effect4.Flow.run_checked_not_stuck
#check @Effect4.Flow.run_fuel_mono
#check @Effect4.Target.EffectV4.tableAlphabet
#check @Effect4.Target.EffectV4.tableService
#check @Effect4.Target.EffectV4.tableNameOf
#check @Effect4.Target.EffectV4.Script.toFlow

/-! ## The tape -/

example : Tape.read [] ⟨1⟩ = .exhausted := rfl
#guard Tape.read [⟨⟨1⟩, true⟩] ⟨1⟩ = .answered true []
#guard Tape.read [⟨⟨2⟩, true⟩] ⟨1⟩ = .mismatch ⟨1⟩ ⟨2⟩
#guard Tape.read [⟨⟨1⟩, false⟩, ⟨⟨3⟩, true⟩] ⟨1⟩ = .answered false [⟨⟨3⟩, true⟩]
#guard Tape.wire [⟨⟨1⟩, false⟩, ⟨⟨3⟩, true⟩] = [(1, false), (3, true)]

/-! ## The internal oracle on `incr` -/

effect_signature Cell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

def succ (n : Nat) : Nat := n + 1

effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  let y ← Cell.get()
  return y

def cellLive : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | .get => fun _ => get
  | .put => fun n => set n

/-- The traced service's log, with the outcome appended (the harness golden). -/
def tracedLog : Effect4.Trace.Log :=
  let result : (Nat × Effect4.Trace.Log) × Nat :=
    ((interpret (Cell.traced cellLive).toHandler (incr 0)).run []).run 41
  result.1.2 ++ [.done (.success (.nat result.1.1))]

def cellAtoms : AtomTable := [("succ", "number", "number")]

def cellFamily : String → Val → StateT Nat Id Val
  | "get", _ => do let n ← get; pure (.nat n)
  | "put", .nat n => do set n; pure .unit
  | _, _ => pure .unit

def cellAtom : String → Val → Val
  | "succ", .nat n => .nat (n + 1)
  | _, _ => .unit

/-- The embedded and admitted `incr` flow with its table. -/
def embedded : Option (Σ table : List OpSpec, CheckedFlow (tableAlphabet ⟨0⟩ table)) := do
  let (table, raw) ← Script.toFlow Cell.rows cellAtoms incr.script
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some ⟨table, flow⟩
  | .error _ => none

#guard embedded.isSome

/-- Run the embedded flow with the given fuel from cell 41 and input 0. -/
def flowRun (fuel : Nat) : Option ((RunResult × Effect4.Trace.Log) × Nat) :=
  embedded.map fun ⟨table, flow⟩ =>
    ((Flow.run fuel flow (tableService ⟨0⟩ table cellFamily cellAtom) (tableNameOf ⟨0⟩ table)
      [] (.nat 0)).run []).run 41

def flowDefault : Option ((RunResult × Effect4.Trace.Log) × Nat) :=
  embedded.map fun ⟨table, flow⟩ =>
    ((Flow.runDefault flow (tableService ⟨0⟩ table cellFamily cellAtom) (tableNameOf ⟨0⟩ table)
      [] (.nat 0)).run []).run 41

-- The runner finishes with the traced service's outcome and state.
#guard (flowDefault.map fun r => (r.1.1, r.2)) = some (RunResult.done (.nat 42), 42)

-- The internal oracle: the runner's log agrees with the traced service under `m2`.
#guard (flowDefault.map fun r => Effect4.Trace.agree Effects.Trace.Mask.m2 r.1.2 tracedLog) = some true

-- The runner's log is exactly the golden: pure operations leave no rows.
#guard (flowDefault.map fun r => r.1.2) = some tracedLog

-- Fuel exhaustion is a frontier with a trailing `frontier` row, never an outcome.
#guard (flowRun 0).map (fun r => r.1) =
  some (RunResult.frontier (.fuel ⟨0⟩), [Effects.Trace.Event.frontier])

-- Enough fuel changes nothing (`run_fuel_mono`, executable instance).
#guard flowRun 40 = flowDefault

/-! ## Decisions on a hand-built flow -/

/-- `choose` at site 7 between two returns of the input. -/
def chooser : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨7⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

/-- `choose` at site 1 back to itself or on to a return: a chosen loop. -/
def chosenLoop : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨1⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def noOps : FlowService (tableAlphabet ⟨0⟩ []) Id :=
  tableService ⟨0⟩ [] (fun _ v => pure v) (fun _ v => v)

def runRaw (raw : RawFlow String) (tape : Tape) :
    Option ((RunResult × Tape) × Effect4.Trace.Log) :=
  match admit (tableAlphabet ⟨0⟩ []) raw with
  | .ok flow =>
      some ((Flow.runTape (Flow.fuelFor raw tape) flow noOps (tableNameOf ⟨0⟩ []) tape (.nat 5)).run [])
  | .error _ => none

-- Tape exhaustion is the unanswered frontier.
#guard runRaw chooser [] =
  some ((RunResult.frontier (.unansweredDecision ⟨7⟩), []), [Effects.Trace.Event.frontier])

-- A tape entry for another site is a refusal; nothing is consumed or logged.
#guard runRaw chooser [⟨⟨8⟩, true⟩] = some ((RunResult.refused ⟨7⟩ ⟨8⟩, [⟨⟨8⟩, true⟩]), [])

-- An answered decision is consumed and logged; the branch is taken.
#guard runRaw chooser [⟨⟨7⟩, true⟩] =
  some ((RunResult.done (.nat 5), []), [.decide 7 true, .done (.success (.nat 5))])
#guard runRaw chooser [⟨⟨7⟩, false⟩, ⟨⟨9⟩, true⟩] =
  some ((RunResult.done (.nat 5), [⟨⟨9⟩, true⟩]), [.decide 7 false, .done (.success (.nat 5))])

-- A chosen loop consumes one entry per visit and finishes within `fuelFor`.
#guard runRaw chosenLoop [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] =
  some ((RunResult.done (.nat 5), []),
    [.decide 1 true, .decide 1 true, .decide 1 false, .done (.success (.nat 5))])

/-- The fuel allotted to that loop, by definition. -/
example : Flow.fuelFor chosenLoop [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] = 9 := rfl

end Effect4Test.Flow.RunnerContract
