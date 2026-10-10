import Meaning
import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Auto.Semantics
import ProofGraph.Goal

/-! Proposed statements only. README.md places these under translation-simulation, R6,
and the existing rows-denotation-session/rows-denotation-host questions. No production
registry entry changes. The finite controls import Meaning, not these open goals. -/
set_option autoImplicit false
namespace Test.HostMeaningWidening
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- H8 widened to the row-safe part of LoopedRows, after a sufficient semantic budget.
The premises retain the existing journal funding and host control restrictions. -/
def H8LoopedRows : Prop :=
  ∀ (s : Run), Run.Reached s → Run.funded s = true → Run.atRest s = true →
    Run.hostDriven s = true → LoopedRows s.built.program = true →
    LoopedDataRows s.built.table s.built.program = true →
    ∃ lower, ∀ k, lower ≤ k →
      coarseRowsB s.built.table k s.built.program [] Stores.empty (Run.appliedExits s) =
        s.exit.map fun ex => ((ex, s.machine.state), [])

/-- Proposed loop extension of rows-denotation-session, role simulation; R6.
Consumer: the paged data-row client and the later driver theorem. Reach: H8LoopedRows.
It establishes no scope, external handle allocation, interruption, fork, progress, or target claim. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal h8_loopedRows : H8LoopedRows

/-- H9 keeps completion as a premise. Past host answers do not fix an unanswered next call. -/
def H9LoopedRows : Prop :=
  ∀ (s : Run), Run.Reached s → Run.funded s = true → Run.atRest s = true →
    Run.hostDriven s = true → LoopedRows s.built.program = true →
    LoopedDataRows s.built.table s.built.program = true →
    ∀ {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ),
      Run.HostAnswered s.built.table host s.built.program s.budget.fuel (Run.tapeOf s)
        (Api.load s.built.program s.budget.compileFuel) st st' →
      ∀ ex, s.exit = some ex → ∃ lower, ∀ k, lower ≤ k →
        meaningUnderB host k s.built.program [] Stores.empty st =
          some ((some ex, s.machine.state), st')
end Test.HostMeaningWidening
