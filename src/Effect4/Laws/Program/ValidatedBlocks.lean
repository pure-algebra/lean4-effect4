import Effect4.Laws.Api.SessionMeaningBlocks
import Effect4.Laws.Program.Validated
import Effect4.Laws.Auto.Semantics

/-!
# Validated observations of completed block runs

Concept: translation-simulation. Claim: rows-block-host, R6, serving the service consumer.
Reach: completed BlockRows runs with checked protocol or model premises, at empty context.
The postcondition holds on finished leaves. Neither conformance nor progress is established.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- Step of `rows-block-host`, R6. Consumer: the checked service-consumer claim in stage 5.
Reach: completed, conforming `BlockRows` runs under the existing receipt premises.
The postcondition covers every finished budgeted leaf. A cut satisfies it vacuously.
This establishes neither host conformance nor progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem conforms_sat_blocks (protocols : RowProtocols) (s : Run) (hreach : Run.Reached s)
    (hfund : funded s = true) (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hfrag : BlockRows s.built.table s.built.program = true)
    (hconf : conforms protocols s = true) {Q : ExitV → Prop}
    (hsat : ∀ k, Effects.Program.Sat (rowsProtocol s.built.table protocols)
      (fun result => match result with | none => True | some ex => Q ex)
      (denoteBlockB s.built.table (bodiesOf s.built.program) k []
        s.built.program emptyCtx []))
    (ex : ExitV) (hex : s.exit = some ex) : Q ex := by
  obtain ⟨-, hcheck⟩ := Bool.and_eq_true_iff.mp hconf
  obtain ⟨st', hst'⟩ := Option.isSome_iff_exists.mp hcheck
  have hA := hostAnsweredCheck_sound s.built.table (keptTapeHost s.built.table protocols)
    s.built.program s.budget.fuel (tapeOf s) _ (appliedExits s) st' hst'
  obtain ⟨lower, hlow⟩ := h9_blocks s hreach hfund hrest hhost hfrag
    (keptTapeHost s.built.table protocols) (appliedExits s) st' hA ex hex
  have hresult := Effects.Program.Sat.sound (rowsHost (keptTapeHost s.built.table protocols))
    (rowsHost_meets (keptTapeHost_meets s.built.table protocols)) _ (hsat lower)
    (Stores.empty, appliedExits s) (some ex) (s.machine.state, st') (hlow lower (Nat.le_refl _))
  exact hresult

/-- Step of `rows-block-host`, R6. Consumer: the reference-model service claim in stage 5.
Reach: completed `BlockRows` runs whose applied answers match the model.
The final observation retains stores and model state. It establishes no progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem agrees_hostRun_blocks {σ : Type} (model : Reactor σ) (s : Run)
    (hreach : Run.Reached s) (hfund : funded s = true) (hrest : atRest s = true)
    (hhost : hostDriven s = true) (hfrag : BlockRows s.built.table s.built.program = true)
    (start finish : σ) (hagree : agrees model s start = some finish)
    (ex : ExitV) (hex : s.exit = some ex) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunBlockB (reactorHost s.built.table model) (bodiesOf s.built.program) k []
        s.built.program emptyCtx [] Stores.empty start = some (some ex, (s.machine.state, finish)) := by
  exact h9_blocks s hreach hfund hrest hhost hfrag _ start finish
    (hostAnsweredCheck_sound _ _ _ _ _ _ _ _ hagree) ex hex
end Effect4.Run
