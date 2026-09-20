import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Auto.Obligations
/-! Statements captured before Phase A origin/site proof maintenance. -/
namespace Effect4.Machine.PhaseA.ApproximationWanted
open Effect4 Effect4.Machine Effect4.Machine.RunMachine
set_option linter.unusedSectionVars false
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

def spawn_grows {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {parent : RunFiber ν σ β ε δ ι α χ}
    {program : Prim ν σ β ε δ ι α} {options : Supervision.ForkOptions} {site : List Nat} :
    ProofGraph.Obligation (Grows m (spawn interp m parent program options site)) := ⟨⟩
#proof_wanted spawn_grows

def launchEntrant_grows {interp : RunInterp ν σ β ε δ ι α χ St}
    {raceId : Nat} {m : RunMachine ν σ β ε δ ι α χ St} {host : RunFiber ν σ β ε δ ι α χ}
    {program : Prim ν σ β ε δ ι α} {site : List Nat} :
    ProofGraph.Obligation (Grows m (launchEntrant interp raceId m host program site)) := ⟨⟩
#proof_wanted launchEntrant_grows
end Effect4.Machine.PhaseA.ApproximationWanted
