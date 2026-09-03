/-
Counterexamples the job-runner packet found (`test/counterexamples/REGISTER.md`,
`E4-FLOW-CE-026` and `E4-FLOW-CE-027`). Each attack names a reading of the flow
language that writing a real program showed to be false; the witness is a
`#guard` over the region runner itself (`Effect4/Flow/Region.lean`), on graphs
small enough to read.

The program that provoked them is `docs/research/2026-09-03-job-runner.md`, and
its own receipts are `Effect4Test/Flow/JobRunnerContract.lean`.
-/

import Effect4.Flow.Interrupt
import Effect4.Meta.Derive

namespace Effect4Test.Counterexamples.Flow.JobRunner

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

effect_signature Ping where
  | ping (n : Nat) : Nat ⟪ "answer something", "the answer a flow cannot look at" ⟫
  | bang (n : Nat) : Nat !! String ⟪ "abort with a string" ⟫

/-- Two services over the same alphabet, differing only in what `ping` answers.
`E4-FLOW-CE-027` is that no flow can tell them apart. -/
def pingZero : String → Val → StateT Nat Id (Except Val Val)
  | "ping", _ => pure (.ok (.nat 0))
  | "bang", _ => pure (.error (.str "boom"))
  | _, _ => pure (.ok .unit)

def pingNine : String → Val → StateT Nat Id (Except Val Val)
  | "ping", _ => pure (.ok (.nat 9))
  | "bang", _ => pure (.error (.str "boom"))
  | _, _ => pure (.ok .unit)

/-- The family's two operations, then the one pure atom the repaired witness
branches on (Flow v3): `isZero` answers a boolean the flow can test. -/
def table : List OpSpec := familyTable Ping.rows ++
  [ { name := "isZero", kind := .atom, requestTy := "number", answerTy := "boolean" } ]

def opPing : OperationId := ⟨0⟩
def opBang : OperationId := ⟨1⟩
def opIsZero : OperationId := ⟨2⟩

/-- The atom dispatcher of these runs: `isZero` on a natural, identity otherwise. -/
def atom : String → Val → Val
  | "isZero", .nat n => .bool (n == 0)
  | _, v => v

def block (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) :
    RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def region (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

def flowOf (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) :
    RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def runWith (family : String → Val → StateT Nat Id (Except Val Val)) (raw : RegionFlow String)
    (tape : Tape) : Option (RunResult × Effect4.Trace.Log) :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      let r := ((Flow.runRegionsDefault flow
        (Flow.tableRegionService ⟨0⟩ table family atom)
        (tableNameOf ⟨0⟩ table) tape (.nat 5)).run []).run 41
      some (r.1.1.1, r.1.2)
  | .error _ => none

/-! ## `E4-FLOW-CE-026` — an abort is not recoverable inside a flow

*Attacked statement.* "A region flow can act on an operation's failure: the
retry-or-give-up decision after a failing job is expressible over an aborting
operation."

The job runner's whole retry path depends on this and it is false. An operation
declared `A !! E` that fails takes `Effect4.Flow.regionLoop`'s `fail` arm: every
open region closes, the run ends `failed`, and the successor block named by the
`perform` is never entered. There is no terminator, and no arm of `RegionTerm`
or `RawTerm`, that continues from an abort.

*Forced repair.* State a recoverable failure in the *data* reading of the error
(`Except ε α` as the answer, rc.112's `Result`), which the run survives and a
`choose` can then branch after; or add a handler former to the flow language and
a `catch` arm to both runners. The job runner took the first: `Jobs.attempt` is
`Jobs.run` with its error in the answer.
-/

/-- Region 1 holds a resource; block 1 aborts; block 2 would have performed
`ping` had the run survived. Before Flow v3 this was the whole story
(`E4-FLOW-CE-026`): an abort took `regionLoop`'s `fail` arm and no successor
was ever entered. -/
def abortFlow : RegionFlow String :=
  flowOf [region 1 none 4]
    [ block 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
    , block 1 (some 1) ["number"] (.plain (.perform opBang ⟨0⟩ ⟨2⟩ (vars 1)))
    , block 2 (some 1) ["number", "number"] (.plain (.perform opPing ⟨0⟩ ⟨3⟩ (vars 1)))
    , block 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , block 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

-- The graph is admitted, and an uncaught abort still ends the run `failed`
-- with the region closed on the way out: the plain `perform` keeps its meaning.
#guard (admitRegions (tableAlphabet ⟨0⟩ table) abortFlow).isOk
#guard runWith pingZero abortFlow [] =
  some (.failed (.str "boom"),
    [ .enter 1
    , .op "bang" (.nat 5)
    , .failed "bang" (.str "boom")
    , .leave 1 (.failure (.str "boom"))
    , .done (.failure (.str "boom")) ])

/-- **Repaired by Flow v3.** The same abort, caught: `performCatch` names a
failure successor (block 5) that receives the environment and the error, so
the run continues, `ping` is performed on the recovery path, and the region
closes with success. The trace writes the `failed` row and then the
successor's rows — never `done failure` — and no region unwinds. -/
def caughtFlow : RegionFlow String :=
  flowOf [region 1 none 4]
    [ block 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
    , block 1 (some 1) ["number"] (.plain (.performCatch opBang ⟨0⟩ ⟨2⟩ (vars 1) ⟨5⟩ (vars 1)))
    , block 2 (some 1) ["number", "number"] (.plain (.perform opPing ⟨0⟩ ⟨3⟩ (vars 1)))
    , block 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , block 4 none ["number"] (.plain (.ret ⟨0⟩))
    , block 5 (some 1) ["number", "string"] (.plain (.perform opPing ⟨0⟩ ⟨3⟩ (vars 1))) ]

#guard (admitRegions (tableAlphabet ⟨0⟩ table) caughtFlow).isOk
#guard runWith pingZero caughtFlow [] =
  some (.done (.nat 0),
    [ .enter 1
    , .op "bang" (.nat 5)
    , .failed "bang" (.str "boom")
    , .op "ping" (.nat 5)
    , .answer "ping" (.nat 0)
    , .leave 1 (.success (.nat 0))
    , .done (.success (.nat 0)) ])

/-! ## `E4-FLOW-CE-027` — a flow never branches on a value (repaired by Flow v3)

*Attacked statement, before v3.* "A flow can test the answer it just received."
It could not: `choose` was the only branching terminator and `plan` answered
it from the tape, so two runs of one graph under one tape followed the same
path whatever the service answered (`branchFlow` below still shows that for
`choose`).

*Repair.* Flow v3 adds `branch (test) (site) (onTrue) (onFalse) (args)`, taken
by the *value* of `test`. It is still a decision site: the tape entry at
`site` is read, the `decide` row is written, and a run whose tape disagrees
with the value is refused — which is what keeps every cycle tape-bounded.
`valueFlow` below branches on whether `ping` answered zero. -/

/-- `ping`, then a `choose` at site 1, then a second `ping` on the left branch
and none on the right. -/
def branchFlow : RegionFlow String :=
  flowOf []
    [ block 0 none ["number"] (.plain (.perform opPing ⟨0⟩ ⟨1⟩ (vars 1)))
    , block 1 none ["number", "number"] (.plain (.choose ⟨1⟩ ⟨2⟩ ⟨3⟩ (vars 2)))
    , block 2 none ["number", "number"] (.plain (.perform opPing ⟨1⟩ ⟨3⟩ [⟨0⟩]))
    , block 3 none ["number", "number"] (.plain (.ret ⟨1⟩)) ]

/-- The branch each run took, and the answer it saw. -/
def branchTaken (family : String → Val → StateT Nat Id (Except Val Val)) (tape : Tape) :
    Option Effect4.Trace.Log :=
  (runWith family branchFlow tape).map fun r =>
    r.2.filter fun event => match event with | .decide _ _ => true | _ => false

-- A `choose` is the tape's: both services take the same branch.
#guard branchTaken pingZero [⟨⟨1⟩, true⟩] = branchTaken pingNine [⟨⟨1⟩, true⟩]
#guard branchTaken pingZero [⟨⟨1⟩, false⟩] = branchTaken pingNine [⟨⟨1⟩, false⟩]

/-- `ping`, then `isZero` of the answer, then a `branch` on that flag at site 1:
a second `ping` when the answer was zero, none otherwise. -/
def valueFlow : RegionFlow String :=
  flowOf []
    [ block 0 none ["number"] (.plain (.perform opPing ⟨0⟩ ⟨1⟩ (vars 1)))
    , block 1 none ["number", "number"] (.plain (.perform opIsZero ⟨1⟩ ⟨2⟩ (vars 2)))
    , block 2 none ["number", "number", "boolean"] (.plain (.branch ⟨2⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ (vars 2)))
    , block 3 none ["number", "number"] (.plain (.perform opPing ⟨1⟩ ⟨4⟩ [⟨0⟩]))
    , block 4 none ["number", "number"] (.plain (.ret ⟨1⟩)) ]

#guard (admitRegions (tableAlphabet ⟨0⟩ table) valueFlow).isOk

-- The value steers the graph: `pingZero` answers 0, so the branch is taken and
-- a second `ping` runs; `pingNine` answers 9, so it is not.
#guard (runWith pingZero valueFlow [⟨⟨1⟩, true⟩]).map
    (fun r => r.2.count (.op "ping" (.nat 0))) = some 1
#guard (runWith pingNine valueFlow [⟨⟨1⟩, false⟩]).map
    (fun r => r.2.count (.op "ping" (.nat 9))) = some 0

-- Still a decision site: the `decide` row is written with the value's answer ...
#guard (runWith pingZero valueFlow [⟨⟨1⟩, true⟩]).map
    (fun r => r.2.filter fun event => match event with | .decide _ _ => true | _ => false)
  = some [.decide 1 true]

-- ... and a tape that disagrees with the value is refused, not followed.
#guard (runWith pingZero valueFlow [⟨⟨1⟩, false⟩]).map (·.1) = some (.refusedValue ⟨1⟩)

/-! ## Axiom report

Expected union: `propext` and `Quot.sound`. -/

#print axioms Effect4.Flow.closeFrame_log
#print axioms Effect4.Flow.closeFrame_failure

end Effect4Test.Counterexamples.Flow.JobRunner
