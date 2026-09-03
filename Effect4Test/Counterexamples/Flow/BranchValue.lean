/-
Counterexample for the Flow v3 `branch` value contract
(`test/counterexamples/REGISTER.md`, `E4-FLOW-CE-029`).

Admission types a `branch`'s test operand with the alphabet's `boolTy`
(`Effects.BranchTestWF`), but `Effects.Trace.Val` is an untyped eight-arm
carrier with no relation to `Ty`, and a `FlowService` answers an unconstrained
`Val`. So an *admitted* flow can reach its `branch` with a `.nat` in the
`boolTy`-typed slot. This file is the witness for that flow.
-/

import Effect4.Semantics.Runs
import Effect4.Target.TypeScript.ScriptFlow

namespace Effect4Test.Counterexamples.Flow.BranchValue

open Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)

/-- One family operation whose declared answer type is the alphabet's boolean
spelling. Nothing constrains the `Val` its service actually answers. -/
def table : List OpSpec :=
  [ { name := "probe", kind := .family, requestTy := "number", answerTy := "boolean" } ]

/-- `probe` the input, then branch at site 1 on the answer. Both edges return
the input, so the two runs are separated by their `decide` row alone. -/
def probeBranch : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "boolean"], term := .branch ⟨1⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

-- The flow is admitted: the test slot is spelled `boolean`, the alphabet's `boolTy`.
#guard (admit (tableAlphabet ⟨0⟩ table) probeBranch).isOk

/-- A service that answers `answer` to every `probe`. -/
def answering (answer : Val) : FlowService (tableAlphabet ⟨0⟩ table) Id :=
  tableService ⟨0⟩ table (fun _ _ => pure answer) (fun _ v => v)

/-- Run `probeBranch` under a service that answers `answer` to every `probe`. -/
def runWith (answer : Val) (tape : Tape) : Option (RunResult × Effect4.Trace.Log) :=
  match admit (tableAlphabet ⟨0⟩ table) probeBranch with
  | .ok flow =>
      some ((Flow.run 8 flow (answering answer) (tableNameOf ⟨0⟩ table) tape (.nat 5)).run [])
  | .error _ => none

/-- Just the decision rows of a run. -/
def decides (answer : Val) (tape : Tape) : Option Effect4.Trace.Log :=
  (runWith answer tape).map fun r =>
    r.2.filter fun event => match event with | .decide _ _ => true | _ => false

/-! ## The attack

`probe` answers `.nat 0`, which is not a `Val.bool`, so the run has no boolean
reading of its test operand. The readings below are the *attacked* ones: the
tape alone steers the admitted flow, both tapes are accepted, and the two runs
differ only in the row the tape dictated. The `branch` contract — "the tape and
the value must agree, else refusal" — does not hold here.

The host does not read it this way. `Skeleton.branchIf` renders as
`decisions.report(site, test); if (test) …`, and `decisions.report`
(`harness/trace/tracer.ts:327-335`) compares the reported test to the tape
entry with `!==`, so a test that is not a boolean never equals a boolean entry
and the run dies with `TapeValueMismatch`. These two runs have no host
counterpart at all. -/

-- ATTACK: the tape decides, and it is believed.
#guard runWith (.nat 0) [⟨⟨1⟩, true⟩] = some (RunResult.done (.nat 5),
  [ .op "probe" (.nat 5), .answer "probe" (.nat 0), .decide 1 true
  , .done (.success (.nat 5)) ])

-- ATTACK: the other tape is taken just as happily, on the same service.
#guard decides (.nat 0) [⟨⟨1⟩, false⟩] = some [.decide 1 false]

-- ATTACK: the two runs of one service differ only in the tape's own row.
#guard decides (.nat 0) [⟨⟨1⟩, true⟩] ≠ decides (.nat 0) [⟨⟨1⟩, false⟩]

/-! ## The positive controls

With a real `Val.bool` in the slot the advertised contract does hold, and it is
the only reading the lowering can render: `Skeleton.branchIf` emits
`decisions.report(site, test); if (test) …`, a JavaScript truthiness test that
has no tape-only mode. -/

-- The agreeing tape runs.
#guard decides (.bool true) [⟨⟨1⟩, true⟩] = some [.decide 1 true]

-- The disagreeing tape refuses, at the branch's own site twice.
#guard (runWith (.bool true) [⟨⟨1⟩, false⟩]).map (·.1)
  = some (RunResult.refused ⟨1⟩ ⟨1⟩)

-- A tape naming another site is the other refusal, and is unrelated to the value.
#guard (runWith (.bool true) [⟨⟨2⟩, true⟩]).map (·.1)
  = some (RunResult.refused ⟨1⟩ ⟨2⟩)

end Effect4Test.Counterexamples.Flow.BranchValue
