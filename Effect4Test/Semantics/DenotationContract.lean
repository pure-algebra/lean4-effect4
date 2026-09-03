/-
Contract packet: `test/contracts/flow-denotation.contract.md` (D1, light
ceremony D2).

Frozen: the flow signature sum, the fuelled and the fuel-free denotation, the
trace handler and the outcome rows. Executable receipts: for the `incr`,
`chooser` and `chosenLoop` flows of `Effect4Test/Flow/RunnerContract.lean`, the
runner's own result and log equal `interpret (traceHandler …) (denoteFuel …)`
closed by the outcome rows, run from the empty log — the `m2` oracle as an
instance of T1. Doc comments cannot precede `#guard`, so the receipts carry line
comments.
-/

import Effect4.Semantics.Denotation
import Effect4Test.Flow.RunnerContract

namespace Effect4Test.Semantics.DenotationContract

open Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)
open Effect4Test.Flow.RunnerContract
  (embedded tracedLog cellFamily cellAtom chooser chosenLoop noOps runRaw)

/-! ## The frozen surface -/

#check @Effects.FlowAlphabet.toAlphabet
#check @Effect4.Flow.Fam
#check @Effect4.Flow.Sig
#check (@Effect4.Flow.DecSig : Signature)
#check @Effect4.Flow.FullSig
#check @Effect4.Flow.FlowService.toService
#check @Effect4.Flow.denoteFuel
#check @Effect4.Flow.denoteGo
#check @Effect4.Flow.denote
#check @Effect4.Flow.tracedFlowService
#check @Effect4.Flow.decisionHandler
#check @Effect4.Flow.traceHandler
#check @Effect4.Flow.outcomeRows
#check @Effect4.Flow.close
#check @Effect4.Flow.interpretRun
#check @Effect4.Flow.WritesLog

/-! ## The laws -/

#check @Effects.reachableNoChoose_trans
#check @Effects.RawFlow.reachSet_length_lt_of_edge
#check @Effect4.Flow.edgeNoChoose_of_plan_jump
#check @Effect4.Flow.edgeNoChoose_of_plan_perform
#check @Effect4.Flow.tape_length_of_plan_choose
#check @Effect4.Flow.interpret_log_append
#check @Effect4.Flow.interpret_log_of_nil
#check @Effect4.Flow.loop_eq_interpretRun
#check @Effect4.Flow.runTape_eq_interpretRun
#check @Effect4.Flow.denoteGo_eq
#check @Effect4.Flow.denoteFuel_eq_denoteGo
#check @Effect4.Flow.denoteFuel_eq_denote
#check @Effect4.Flow.runTape_eq_interpretRun_denote
#check @Effect4.Flow.runDefault_eq_interpretRun_denote
#check @Effect4.Flow.runDefault_no_fuel_frontier

/-! ## The signature sum, spelled out -/

-- The decision summand answers `Unit`: the tape fixed the branch already.
example (site : DecisionId) (branch : Bool) : DecSig.Answer (site, branch) = Unit := rfl

-- The flow summand answers a wire value.
example (alphabet : FlowAlphabet String) (op : alphabet.Op) (request : Val) :
    (FullSig alphabet).Answer (Sum.inl ⟨op, request⟩) = Val := rfl

-- The sum is `Sig ⊕ₛ DecSig`, definitionally.
example (alphabet : FlowAlphabet String) : FullSig alphabet = Sig alphabet ⊕ₛ DecSig := rfl

/-! ## T2 as a statement about any admitted flow

The fuel-free `denote` is well-founded, so it does not reduce in the kernel and
carries no `#guard`. T2 is what moves a receipt taken at `fuelFor`'s allotment
onto it. -/

example {alphabet : FlowAlphabet String} (flow : CheckedFlow alphabet) (tape : Tape)
    (input : Val) :
    denoteFuel (fuelFor flow.erase tape) flow.erase flow.erase.entry [input] tape
      = denote flow tape input :=
  denoteFuel_eq_denote flow tape input (Nat.le_refl _)

/-! ## The `m2` oracle on `incr`, as an instance of T1 -/

/-- The runner's own `runTape` on the embedded `incr` flow. -/
def runnerIncr : Option (((RunResult × Tape) × Effect4.Trace.Log) × Nat) :=
  embedded.map fun ⟨table, flow⟩ =>
    ((Flow.runTape (fuelFor flow.erase []) flow (tableService ⟨0⟩ table cellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) [] (.nat 0)).run []).run 41

/-- The same run read through the algebra: `interpret` of the denotation under
the trace handler, closed by the outcome rows. -/
def denotedIncr : Option (((RunResult × Tape) × Effect4.Trace.Log) × Nat) :=
  embedded.map fun ⟨table, flow⟩ =>
    ((interpretRun (tableService ⟨0⟩ table cellFamily cellAtom) (tableNameOf ⟨0⟩ table)
      (denoteFuel (fuelFor flow.erase []) flow.erase flow.erase.entry [Val.nat 0]
        [])).run []).run 41

-- T1 on `incr`: result, unconsumed tape, log and state all agree.
#guard denotedIncr = runnerIncr

-- And the log is the traced service's golden: the `m2` oracle, denotationally.
#guard (denotedIncr.map fun r => r.1.2) = some tracedLog

-- Pure atoms leave no rows: the guarded service, not `Family.Service.traced`.
#guard (denotedIncr.map fun r => r.1.1.1) = some (RunResult.done (.nat 42))

/-! ## Decisions: the right summand carries them -/

/-- The denotation of a hand-built raw flow, interpreted from the empty log. -/
def denotedRaw (raw : RawFlow String) (tape : Tape) :
    Option ((RunResult × Tape) × Effect4.Trace.Log) :=
  match admit (tableAlphabet ⟨0⟩ []) raw with
  | .ok flow =>
      some ((interpretRun noOps (tableNameOf ⟨0⟩ [])
        (denoteFuel (fuelFor flow.erase tape) flow.erase flow.erase.entry [Val.nat 5]
          tape)).run [])
  | .error _ => none

-- An answered decision: `decide` comes from `decisionHandler`, `done` from `close`.
#guard denotedRaw chooser [⟨⟨7⟩, true⟩] = runRaw chooser [⟨⟨7⟩, true⟩]
#guard denotedRaw chooser [⟨⟨7⟩, true⟩] =
  some ((RunResult.done (.nat 5), []), [.decide 7 true, .done (.success (.nat 5))])

-- Tape exhaustion: the unanswered frontier, with the `frontier` outcome row.
#guard denotedRaw chooser [] = runRaw chooser []

-- A foreign tape entry: a refusal, and no row at all.
#guard denotedRaw chooser [⟨⟨8⟩, true⟩] = runRaw chooser [⟨⟨8⟩, true⟩]

-- The unconsumed tail is returned, not dropped.
#guard denotedRaw chooser [⟨⟨7⟩, false⟩, ⟨⟨9⟩, true⟩] =
  runRaw chooser [⟨⟨7⟩, false⟩, ⟨⟨9⟩, true⟩]

-- A chosen loop: three decisions, three `decide` rows, one outcome row.
#guard denotedRaw chosenLoop [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] =
  runRaw chosenLoop [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩]
#guard denotedRaw chosenLoop [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] =
  some ((RunResult.done (.nat 5), []),
    [.decide 1 true, .decide 1 true, .decide 1 false, .done (.success (.nat 5))])

/-! ## The outcome rows are the runner's, not the algebra's -/

#guard outcomeRows (.done (.nat 1)) = [Effects.Trace.Event.done (.success (.nat 1))]
#guard outcomeRows (.frontier (.fuel ⟨0⟩)) = [Effects.Trace.Event.frontier]
#guard outcomeRows (.frontier (.unansweredDecision ⟨0⟩)) = [Effects.Trace.Event.frontier]
#guard outcomeRows (.frontier (.stuck ⟨0⟩)) = []
#guard outcomeRows (.refusedSite ⟨0⟩ ⟨1⟩) = []
#guard outcomeRows (.refusedValue ⟨1⟩) = []

end Effect4Test.Semantics.DenotationContract
