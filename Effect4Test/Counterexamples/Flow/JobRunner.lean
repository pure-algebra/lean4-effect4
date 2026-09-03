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

def table : List OpSpec := familyTable Ping.rows

def opPing : OperationId := ⟨0⟩
def opBang : OperationId := ⟨1⟩

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
        (Flow.tableRegionService ⟨0⟩ table family fun _ v => v)
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
`ping` had the run survived. -/
def abortFlow : RegionFlow String :=
  flowOf [region 1 none 4]
    [ block 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
    , block 1 (some 1) ["number"] (.plain (.perform opBang ⟨0⟩ ⟨2⟩ (vars 1)))
    , block 2 (some 1) ["number", "number"] (.plain (.perform opPing ⟨0⟩ ⟨3⟩ (vars 1)))
    , block 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , block 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

-- The graph is admitted: nothing about it is ill formed. The refusal is not an
-- admission clause, it is the absence of a continuation.
#guard (admitRegions (tableAlphabet ⟨0⟩ table) abortFlow).isOk

-- The run ends `failed` at the abort. Block 2 is never entered: there is no
-- `op ping` row, and the region closed on the way out.
#guard runWith pingZero abortFlow [] =
  some (.failed (.str "boom"),
    [ .enter 1
    , .op "bang" (.nat 5)
    , .failed "bang" (.str "boom")
    , .leave 1 (.failure (.str "boom"))
    , .done (.failure (.str "boom")) ])

-- The same graph with `ping` in place of `bang` reaches block 2, so the missing
-- row above is the abort and nothing else.
#guard (runWith pingZero
  (flowOf [region 1 none 4]
    [ block 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
    , block 1 (some 1) ["number"] (.plain (.perform opPing ⟨0⟩ ⟨2⟩ (vars 1)))
    , block 2 (some 1) ["number", "number"] (.plain (.perform opPing ⟨0⟩ ⟨3⟩ (vars 1)))
    , block 3 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , block 4 none ["number"] (.plain (.ret ⟨0⟩)) ]) []).map
      (fun r => r.2.any fun event => event == .op "ping" (.nat 5)) = some true

/-! ## `E4-FLOW-CE-027` — a flow never branches on a value

*Attacked statement.* "A flow can test the answer it just received: the job
runner's queue-empty test is `next` answering 0, and its retry bound is the
carried attempt counter reaching zero."

Both are false. `RawTerm` has exactly one branching terminator, `choose`, and
`Effect4.Flow.plan` answers it from the decision tape (`Flow.read`), never from
the environment. So two runs of one graph under one tape follow the same path
whatever the service answered, and a block parameter — the job runner's attempt
budget — can be carried and computed on by atoms but never compared.

*Forced repair.* Either add a data-dependent terminator (a `branch` on a
variable, with a decidable predicate the alphabet declares) and give both
runners and all three lowerings an arm for it; or state plainly, wherever a
flow's control is described, that every branch of an admitted flow is a tape
question and that a graph's control is therefore independent of its service.
-/

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

-- The two services answer differently — the logs are not equal ...
#guard (runWith pingZero branchFlow [⟨⟨1⟩, true⟩]).map (·.2) ≠
  (runWith pingNine branchFlow [⟨⟨1⟩, true⟩]).map (·.2)

-- ... and yet both take the same branch, because the branch is the tape's.
#guard branchTaken pingZero [⟨⟨1⟩, true⟩] = branchTaken pingNine [⟨⟨1⟩, true⟩]
#guard branchTaken pingZero [⟨⟨1⟩, false⟩] = branchTaken pingNine [⟨⟨1⟩, false⟩]

-- The right branch under the same service and a different tape: the service is
-- unchanged, the path is not. The tape is the only thing steering the graph.
#guard (runWith pingZero branchFlow [⟨⟨1⟩, false⟩]).map
    (fun r => r.2.count (.op "ping" (.nat 0))) = some 0
#guard (runWith pingZero branchFlow [⟨⟨1⟩, true⟩]).map
    (fun r => r.2.count (.op "ping" (.nat 0))) = some 1

/-! ## Axiom report

Expected union: `propext` and `Quot.sound`. -/

#print axioms Effect4.Flow.closeFrame_log
#print axioms Effect4.Flow.closeFrame_failure

end Effect4Test.Counterexamples.Flow.JobRunner
