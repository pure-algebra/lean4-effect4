import Effect4.Modules.Semaphore.Data
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Semaphore.Relation

/-!
# Laws.Modules.Semaphore.Data — Semaphore's model on the step language's carriers

The connector between Semaphore's model and its steps written as data
(`src/Effect4/Modules/Semaphore/Data.lean`; decisions row 330, slice L3). Each step's agreement
then factors into three parts:

1. the step language's reading law (`Step.sound`), proved once;
2. **the encoding**, once for the module: a model state's carrier at the opaque identity context
   (`cellC`) has the cell's value as its image (`cellVal_image`);
3. **the value**, once for each step: the step's value on that carrier is the model's transition
   (`takeIfAvailable_eval`, `release_eval`). These are equations of Lean values.

The typing statements need no connector: the typing check closes by `rfl`.

Placement: concept `translation-simulation`, requirement R10, helpers of the claim
`semaphore-steps-agree`. Their consumers are `takeIfAvailableStep_agrees` and
`releaseStep_agrees` (`src/Effect4/Laws/Modules/Semaphore/Steps.lean`). They establish nothing
for the three steps that fold.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Semaphore (cellRecord)

/-- A waiter on the carrier of the opaque context: its hint and its identity through the table,
its count and its stamp. -/
def waiterC (tb : Table) (w : Waiter) : CarrierAt Leaves.opaque waiterTy :=
  (Val.promise (tb.hint w.id), (Val.promise (tb.handle w.id), (w.need, (w.stamp, ()))))

/-- **A model state on the carrier of the opaque context**, through the table. -/
def cellC (tb : Table) (s : State) : CarrierAt Leaves.opaque (.record cellRecord) :=
  (s.next, (s.permits, (s.taken, (s.waiters.map (waiterC tb), ()))))

theorem waiterVal_image (tb : Table) (w : Waiter) :
    (imageAt Leaves.opaque waiterTy).toVal (waiterC tb w) = waiterVal tb w := rfl

/-- **The encoding**: a model state's carrier has the cell's value as its image. -/
theorem cellVal_image (tb : Table) (s : State) :
    (imageAt Leaves.opaque (.record cellRecord)).toVal (cellC tb s) = cellVal tb s := by
  show Val.ctor 0 [.list [.str "next", .str "permits", .str "taken", .str "waiters"],
      .list [.nat s.next, .nat s.permits, .nat s.taken,
        .list ((s.waiters.map (waiterC tb)).map (imageAt Leaves.opaque waiterTy).toVal)]] = _
  rw [List.map_map]
  rfl

/-- The inputs of a step at a count and a model state. -/
abbrev inputsAt (tb : Table) (s : State) (n : Nat) : Inputs Leaves.opaque Data.Γ :=
  (n, (cellC tb s, ()))

/-- The test of the take: the count fits the free count. -/
theorem fits_eval (tb : Table) (s : State) (n : Nat) :
    (Step.not (.lt Data.free (.var Data.count))).eval Leaves.opaque (inputsAt tb s n) =
      decide (n ≤ free s) := by
  show (!decide (s.permits - s.taken < n)) = decide (n ≤ s.permits - s.taken)
  by_cases fitsNow : n ≤ s.permits - s.taken
  · rw [decide_eq_false (Nat.not_lt.mpr fitsNow), decide_eq_true fitsNow]
    rfl
  · rw [decide_eq_true (Nat.lt_of_not_le fitsNow), decide_eq_false fitsNow]
    rfl

/-- **The take-if-available step's value is the model's transition.** -/
theorem takeIfAvailable_eval (tb : Table) (s : State) (n : Nat) :
    Data.takeIfAvailable.eval Leaves.opaque (inputsAt tb s n) =
      ((takeIfAvailable s n).2, cellC tb (takeIfAvailable s n).1) := by
  unfold Data.takeIfAvailable
  rw [Step.eval_ite, fits_eval]
  unfold takeIfAvailable
  by_cases fitsNow : n ≤ free s
  · rw [decide_eq_true fitsNow, if_pos fitsNow]
    rfl
  · rw [decide_eq_false fitsNow, if_neg fitsNow]
    rfl

/-- **The release step's value is the model's transition.** -/
theorem release_eval (tb : Table) (s : State) (n : Nat) :
    Data.release.eval Leaves.opaque (inputsAt tb s n) =
      ((release s n).2, cellC tb (release s n).1) := by
  show ((s.permits - (s.taken - n), !decide ((s.waiters.map (waiterC tb)).length = 0)),
      cellC tb { s with taken := s.taken - n }) = _
  rw [List.length_map, Effect4.Constructive.List.decide_length_zero]
  rfl

end Effect4.Semaphore.Model
