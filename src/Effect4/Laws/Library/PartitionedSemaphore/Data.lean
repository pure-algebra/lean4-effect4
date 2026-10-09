import Effect4.Library.PartitionedSemaphore.Data
import Effect4.Laws.Auto.Semantics

/-! Value equations consumed by the four source reading laws in Steps.
Placement: helpers of `partitioned-semaphore-bookkeeping`, translation-simulation, R10.
The reservation equation retains the source branch premises. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Effect4.PartitionedSemaphore
open Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Model (Counts)

/-- Use the deriving command's connector, rather than author a carrier tuple. -/
abbrev encoded (s : Model.Counts) := Model.Counts.modeledToC s
abbrev requests (s : Model.Counts) (n : Nat) : Inputs Leaves.refused Data.RequestInputs.types :=
  (n, (encoded s, ()))

namespace Model

/-- Helper of partitioned-semaphore-bookkeeping; initial_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_eval (capacity : Nat) :
    Data.initial.eval (Γ := Data.InitialInputs.types) Leaves.refused (capacity, ()) = encoded (Model.initial capacity) := rfl

/-- Helper of partitioned-semaphore-bookkeeping; available_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem available_eval (s : Counts) :
    Data.available.eval (Γ := Data.CellInputs.types) Leaves.refused (encoded s, ()) = Model.available s := rfl

/-- Helper of partitioned-semaphore-bookkeeping; tryTake_reads consumes this equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryTake_eval (s : Counts) (n : Nat) :
    Data.tryTake.eval Leaves.refused (requests s n) =
      ((Model.tryTake s n).1, encoded (Model.tryTake s n).2) := by
  cases s with
  | mk capacity available waiting =>
    cases n with
    | zero => rfl
    | succ n =>
      change (if decide (capacity < n + 1) || decide (available < n + 1) then
        (false, encoded ⟨capacity, available, waiting⟩)
        else (true, encoded ⟨capacity, available - (n + 1), waiting⟩)) = _
      unfold Model.tryTake
      split <;> rfl

/-- Helper of partitioned-semaphore-bookkeeping; reserve_reads consumes this conditional equation.
The branch premise remains explicit, although the scalar arithmetic equation needs no premise. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem reserve_eval (s : Counts) (n : Nat) (_insufficient : s.available < n)
    (_capacity : n ≤ s.capacity) :
    Data.reserve.eval Leaves.refused (requests s n) =
      ((Model.reserve s n).1, encoded (Model.reserve s n).2) := rfl

end Model
end Effect4.PartitionedSemaphore
