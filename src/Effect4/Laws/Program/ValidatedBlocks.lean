import Effect4.Laws.Api.SessionMeaningBlocks
import Effect4.Laws.Program.Validated
import Effect4.Laws.Auto.Semantics

set_option autoImplicit false
namespace Effect4.Run
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- Step of `rows-block-host`, R6. Consumer: the checked service-consumer claim in stage 5.
Reach: completed, conforming `BlockRows` runs under the existing receipt premises.
The postcondition covers every finished budgeted leaf. A cut satisfies it vacuously.
This establishes neither host conformance nor progress. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal conforms_sat_blocks (protocols : RowProtocols) (s : Run) (hreach : Run.Reached s)
    (hfund : funded s = true) (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : BlockRows s.built.table s.built.program = true)
    (hconf : conforms protocols s = true) {Q : ExitV → Prop}
    (hsat : ∀ k, Effects.Program.Sat (rowsProtocol s.built.table protocols)
      (fun result => match result with | none => True | some ex => Q ex)
      (denoteBlockB s.built.table (bodiesOf s.built.program) k []
        s.built.program emptyCtx []))
    (ex : ExitV) (hex : s.exit = some ex) : Q ex

/-- Step of `rows-block-host`, R6. Consumer: the reference-model service claim in stage 5.
Reach: completed `BlockRows` runs whose applied answers match the model.
The final observation retains stores and model state. It establishes no progress. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal agrees_hostRun_blocks {σ : Type} (model : Reactor σ) (s : Run)
    (hreach : Run.Reached s) (hfund : funded s = true) (hrest : atRest s = true)
    (hhost : hostDriven s = true) (hfrag : BlockRows s.built.table s.built.program = true)
    (start finish : σ) (hagree : agrees model s start = some finish)
    (ex : ExitV) (hex : s.exit = some ex) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunBlockB (reactorHost s.built.table model) (bodiesOf s.built.program) k []
        s.built.program emptyCtx [] Stores.empty start = some (some ex, (s.machine.state, finish))
end Effect4.Run
