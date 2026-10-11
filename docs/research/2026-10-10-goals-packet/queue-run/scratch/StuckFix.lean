import Test.Dogfood.Scenario.QueueWorkers

/-! Scratch probe: N1's repair. `whnf` folds a `Nat` operation only on an argument with no free
variable (`withNatValue`, `Lean/Meta/WHNF.lean`). The scope that `elaborateModule` builds reads
`(crew total).rowDefs`, so a minted name's digits carry `total` and do not fold. Rewriting the
module's three closed fields to their values at `0` first should let `rfl` through. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

namespace StuckFix

theorem layers_closed (total : Nat) : (crew total).layers = (crew 0).layers := rfl
theorem rowDefs_closed (total : Nat) : (crew total).rowDefs = (crew 0).rowDefs := rfl
theorem defs_closed (total : Nat) : (crew total).defs = (crew 0).defs := rfl

set_option profiler true in
/-- The crew elaborates at every job count, once its closed fields are closed terms. -/
theorem crew_elaborates (total : Nat) : (elaborateModule (crew total)).toOption.isSome = true := by
  unfold elaborateModule
  rw [layers_closed, rowDefs_closed, defs_closed]
  rfl

/-- What `build` keeps of the elaboration: the program and the module's table. General in the
module. -/
theorem build_ok {m : Module NativeOp} {b : Api.Built} (h : Api.Author.build m = .ok b) :
    elaborateModule m = .ok b.program ∧ b.table = m.table := by
  unfold Api.Author.build at h
  split at h
  · cases h
  · rename_i program hp
    split at h
    · cases h
    · unfold Api.Author.Internal.finishBuild at h
      split at h
      · cases h
        exact ⟨hp, rfl⟩
      · split at h <;> cases h
      · cases h

end StuckFix
