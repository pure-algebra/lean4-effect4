import Effect4.Library.Semaphore.Data
import Effect4.Laws.Step
import Effect4.Laws.Step.Lists
import Effect4.Laws.Schema.Identity
import Effect4.Laws.Library.Semaphore.Relation

/-!
# Laws.Modules.Semaphore.Data — Semaphore's model on the step language's carriers

The connector between Semaphore's model and its steps written as data
(`src/Effect4/Library/Semaphore/Data.lean`; decisions row 330, slice L3). Each step's agreement
then factors into three parts:

1. the step language's reading law (`Step.sound`), proved once;
2. **the encoding**, once for the module: a model state's carrier at the deferred-key identity context
   (`cellC`) has the cell's value as its image (`cellVal_image`);
3. **the value**, once for each step: the step's value on that carrier is the model's transition
   (`take_eval`, `takeIfAvailable_eval`, `release_eval`, `visit_eval`, `withdraw_eval`).
   These are equations of Lean values.

The typing statements need no connector: the typing check closes by `rfl`.

Placement: concept `translation-simulation`, requirement R10, helpers of the claim
`semaphore-steps-agree`. Their consumers are the five `*_agrees` statements
(`src/Effect4/Laws/Library/Semaphore/Steps.lean`).
Identity comparisons require the table injectivity premise.
These equations establish no wrapper scheduling, allocation, progress, or native host result.
-/

set_option autoImplicit false
-- Carrier folds expose their concrete types at default transparency.
set_option backward.isDefEq.respectTransparency false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Semaphore (cellRecord)
open Effect4.Constructive.List (fromFirst_find?)

abbrev WaiterCarrier := DeferredKey × (DeferredKey × (Nat × (Nat × Unit)))

/-- A waiter on the carrier of the opaque context: its hint and its identity through the table,
its count and its stamp. -/
def waiterC (tb : Table) (w : Waiter) : WaiterCarrier :=
  (tb.hint w.id, (tb.handle w.id, (w.need, (w.stamp, ()))))

/-- **A model state on the carrier of the opaque context**, through the table. -/
def cellC (tb : Table) (s : State) : CarrierAt Leaves.deferredKeys (.record cellRecord) :=
  (s.next, (s.permits, (s.taken, (s.waiters.map (waiterC tb), ()))))

theorem waiterVal_image (tb : Table) (w : Waiter) :
    (imageAt Leaves.deferredKeys waiterTy).toVal (waiterC tb w) = waiterVal tb w := rfl

/-- **The encoding**: a model state's carrier has the cell's value as its image. -/
theorem cellVal_image (tb : Table) (s : State) :
    (imageAt Leaves.deferredKeys (.record cellRecord)).toVal (cellC tb s) = cellVal tb s := by
  show Val.ctor 0 [.list [.str "next", .str "permits", .str "taken", .str "waiters"],
      .list [.nat s.next, .nat s.permits, .nat s.taken,
        .list ((s.waiters.map (waiterC tb)).map (imageAt Leaves.deferredKeys waiterTy).toVal)]] = _
  rw [List.map_map]
  rfl

/-- The inputs of a step at a count and a model state. -/
abbrev inputsAt (tb : Table) (s : State) (n : Nat) : Inputs Leaves.deferredKeys Data.Γ :=
  (n, (cellC tb s, ()))

/-- The test of the take: the count fits the free count. -/
theorem fits_eval (tb : Table) (s : State) (n : Nat) :
    (Step.not (.lt Data.free (.var Data.count))).eval Leaves.deferredKeys (inputsAt tb s n) =
      decide (n ≤ free s) := by
  show (!decide (s.permits - s.taken < n)) = decide (n ≤ s.permits - s.taken)
  by_cases fitsNow : n ≤ s.permits - s.taken
  · rw [decide_eq_false (Nat.not_lt.mpr fitsNow), decide_eq_true fitsNow]
    rfl
  · rw [decide_eq_true (Nat.lt_of_not_le fitsNow), decide_eq_false fitsNow]
    rfl

/-- **The take-if-available step's value is the model's transition.** -/
theorem takeIfAvailable_eval (tb : Table) (s : State) (n : Nat) :
    Data.takeIfAvailable.eval Leaves.deferredKeys (inputsAt tb s n) =
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
    Data.release.eval Leaves.deferredKeys (inputsAt tb s n) =
      ((release s n).2, cellC tb (release s n).1) := by
  show ((s.permits - (s.taken - n), !decide ((s.waiters.map (waiterC tb)).length = 0)),
      cellC tb { s with taken := s.taken - n }) = _
  rw [List.length_map, Effect4.Constructive.List.decide_length_zero]
  rfl

/-- The deferred comparison is model request equality only on an injective table. -/
theorem request_equal (tb : Table) (injective : tb.Injective) (a b : Nat) :
    Effect4.Schema.Model.deferredEqual Leaves.deferredKeys (tb.handle a) (tb.handle b) = decide (a = b) := by
  change decide (tb.handle a = tb.handle b) = decide (a = b)
  exact injective.decides a b

def requestValue {Γ : List Ty} (request : Input Γ idTy) (vs : Inputs Leaves.deferredKeys Γ) : DeferredKey :=
  request.get vs

def waitersValue {Γ : List Ty} (xs : Step Γ (.list waiterTy)) (vs : Inputs Leaves.deferredKeys Γ) : List WaiterCarrier :=
  xs.eval Leaves.deferredKeys vs

/-- The removal fold filters deferred keys, before the table connects them to model numbers. -/
theorem remove_eval {Γ : List Ty} (xs : Step Γ (.list waiterTy)) (request : Input Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) :
    (Data.remove xs request).eval Leaves.deferredKeys vs =
      (waitersValue xs vs).filter (fun w => !decide ((w.2.1 : DeferredKey) = (requestValue request vs))) := by
  unfold Data.remove Data.removeWith
  rw [Step.Lists.eval_removeBy]
  rfl

/-- The carrier's removal agrees with the independent model under table injectivity. -/
theorem without_image (tb : Table) (injective : tb.Injective) (ws : List Waiter) (id : Nat) :
    (ws.map (waiterC tb)).filter (fun w => !decide (w.2.1 = tb.handle id)) =
      (without ws id).map (waiterC tb) := by
  rw [List.filter_map]
  have predicate : (fun w => !decide ((waiterC tb w).2.1 = tb.handle id)) =
      (fun w => w.id != id) := by
    funext w
    change (!decide (tb.handle w.id = tb.handle id)) = (w.id != id)
    rw [injective.decides]
    rfl
  change (ws.filter (fun w => !decide ((waiterC tb w).2.1 = tb.handle id))).map (waiterC tb) = _
  rw [predicate]
  rfl

/-- Renewing this request's hint frames every waiter that survives its removal. -/
theorem withoutC_renew (tb : Table) (ws : List Waiter) (id : Nat) (hint : DeferredKey) :
    (without ws id).map (waiterC (tb.renew id hint)) = (without ws id).map (waiterC tb) := by
  apply List.map_congr_left
  intro w member
  have other : w.id ≠ id := (mem_without.mp member).2
  change (if w.id = id then hint else tb.hint w.id, (tb.handle w.id, (w.need, (w.stamp, ())))) = _
  rw [if_neg other]
  rfl

abbrev takeInputs (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey) :
    Inputs Leaves.deferredKeys Data.TakeΓ :=
  (n, (tb.handle id, (hint, (cellC tb s, ()))))

abbrev withdrawInputs (tb : Table) (s : State) (id : Nat) :
    Inputs Leaves.deferredKeys Data.WithdrawΓ :=
  (tb.handle id, (cellC tb s, ()))

/-- The withdrawal step's value is the independent transition. -/
theorem withdraw_eval (tb : Table) (s : State) (id : Nat) (injective : tb.Injective) :
    Data.withdraw.eval Leaves.deferredKeys (withdrawInputs tb s id) =
      ((), cellC tb (withdraw s id)) := by
  have removed := remove_eval (.get (.var Data.withdrawCell) Data.waitersF) Data.withdrawId
    (withdrawInputs tb s id)
  change (Data.remove (.get (.var Data.withdrawCell) Data.waitersF) Data.withdrawId).eval
    Leaves.deferredKeys (withdrawInputs tb s id) =
      (s.waiters.map (waiterC tb)).filter (fun w => !decide (w.2.1 = tb.handle id)) at removed
  rw [without_image tb injective] at removed
  change ((), (s.next, (s.permits, (s.taken,
    ((Data.remove (.get (.var Data.withdrawCell) Data.waitersF) Data.withdrawId).eval
      Leaves.deferredKeys (withdrawInputs tb s id), ()))))) = _
  rw [removed]
  rfl

/-- Taking agrees with the independent transition and renews only the request's hint. -/
theorem take_eval (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey)
    (injective : tb.Injective) :
    Data.take.eval Leaves.deferredKeys (takeInputs tb s id n hint) =
      ((take s id n).2, cellC (tb.renew id hint) (take s id n).1) := by
  have removed := remove_eval (.get (.var Data.takeCell) Data.waitersF) Data.takeId
    (takeInputs tb s id n hint)
  change (Data.remove (.get (.var Data.takeCell) Data.waitersF) Data.takeId).eval
    Leaves.deferredKeys (takeInputs tb s id n hint) =
      (s.waiters.map (waiterC tb)).filter (fun w => !decide (w.2.1 = tb.handle id)) at removed
  rw [without_image tb injective] at removed
  unfold Data.take
  rw [Step.eval_ite]
  have condition : (Step.not (.lt (Data.freeAt Data.takeCell) (.var Data.takeNeed))).eval
      Leaves.deferredKeys (takeInputs tb s id n hint) = decide (n ≤ free s) := by
    change (!decide (s.permits - s.taken < n)) = decide (n ≤ s.permits - s.taken)
    exact Effect4.Constructive.Decidable.not_decide_lt _ _
  rw [condition]
  unfold take
  by_cases fitsNow : n ≤ free s
  · rw [decide_eq_true fitsNow, if_pos fitsNow]
    change (true, (s.next, (s.permits, (s.taken + n,
      ((Data.remove (.get (.var Data.takeCell) Data.waitersF) Data.takeId).eval
        Leaves.deferredKeys (takeInputs tb s id n hint), ()))))) = _
    rw [removed]
    change (true, (s.next, (s.permits, (s.taken + n, ((without s.waiters id).map (waiterC tb), ()))))) =
      (true, (s.next, (s.permits, (s.taken + n, ((without s.waiters id).map (waiterC (tb.renew id hint)), ())))))
    rw [withoutC_renew]
  · rw [decide_eq_false fitsNow, if_neg fitsNow]
    change (false, (s.next + 1, (s.permits, (s.taken,
      ((waitersValue (Data.remove (.get (.var Data.takeCell) Data.waitersF) Data.takeId)
        (takeInputs tb s id n hint)) ++
          [(hint, (tb.handle id, (n, (s.next, ()))))], ()))))) = _
    simp only [waitersValue]
    rw [removed]
    change (false, (s.next + 1, (s.permits, (s.taken,
      ((without s.waiters id).map (waiterC tb) ++ [(hint, (tb.handle id, (n, (s.next, ()))))], ()))))) =
      (false, (s.next + 1, (s.permits, (s.taken,
        ((without s.waiters id ++ [(⟨id, n, s.next⟩ : Waiter)]).map (waiterC (tb.renew id hint)), ())))))
    rw [List.map_append, withoutC_renew]
    change _ = (false, (s.next + 1, (s.permits, (s.taken,
      ((without s.waiters id).map (waiterC tb) ++
        [(if id = id then hint else tb.hint id, (tb.handle id, (n, (s.next, ()))))], ())))))
    rw [if_pos rfl]

/-- The live-scan fold computes the independent model's fitting suffix. -/
theorem fromFirst_eval (tb : Table) (s : State) (cursor : Nat) :
    Data.fromFirst.eval Leaves.deferredKeys (inputsAt tb s cursor) =
      (s.waiters.dropWhile (fun w => !fits cursor (free s) w)).map (waiterC tb) := by
  change (s.waiters.map (waiterC tb)).foldl
    (fun kept w => if (!decide (kept.length = 0) ||
      ((!decide (w.2.2.2.1 < cursor)) && (!decide (free s < w.2.2.1)))) = true
      then kept ++ [w] else kept) [] = _
  rw [Effect4.Constructive.List.foldl_fromFirst]
  simp only [List.length_nil]
  rw [List.dropWhile_map]
  have predicate : (fun w => !((!decide ((waiterC tb w).2.2.2.1 < cursor)) &&
      (!decide (free s < (waiterC tb w).2.2.1)))) =
      (fun w => !fits cursor (free s) w) := by
    funext w
    change (!((!decide (w.stamp < cursor)) && (!decide (free s < w.need))) : Bool) = _
    rw [Effect4.Constructive.Decidable.not_decide_lt, Effect4.Constructive.Decidable.not_decide_lt]
    rfl
  change (s.waiters.dropWhile (fun w => !((!decide ((waiterC tb w).2.2.2.1 < cursor)) &&
    (!decide (free s < (waiterC tb w).2.2.1))))).map (waiterC tb) = _
  rw [predicate]

/-- **The model's visit where a permit is free, from the waiters that start at the first
fitting one.** The reply is the first of those waiters, if any. The next state holds the
waiters before them, then the rest of them. The list is the list without the selected waiter:
an earlier entry equal to the selected one would fit too, at or after the cursor, so it would
have been selected first (`fromFirst_find?`). So the removal by position is the model's
removal, with no premise on the identities. -/
theorem visit_fromFirst (s : State) (cursor : Nat) (someFree : free s ≠ 0) :
    visit s cursor =
      ({ s with
          waiters :=
            s.waiters.take (s.waiters.length -
                (s.waiters.dropWhile (fun w => !fits cursor (free s) w)).length) ++
              (s.waiters.dropWhile (fun w => !fits cursor (free s) w)).drop 1 },
        (s.waiters.dropWhile (fun w => !fits cursor (free s) w))[0]?) := by
  obtain ⟨head, around⟩ := fromFirst_find? (fits cursor (free s)) s.waiters
  cases found : s.waiters.find? (fits cursor (free s)) with
  | none =>
    rw [found] at head around
    rw [visit_none_fits someFree found, head, around]
  | some w =>
    rw [found] at head around
    rw [visit_some someFree found, head, around]

/-- Visiting agrees with the independent transition without any identity premise. -/
theorem visit_eval (tb : Table) (s : State) (cursor : Nat) :
    Data.visit.eval Leaves.deferredKeys (inputsAt tb s cursor) =
      ((visit s cursor).2.map (waiterC tb), cellC tb (visit s cursor).1) := by
  unfold Data.visit
  rw [Step.eval_ite]
  by_cases noneFree : free s = 0
  · change cond (decide (free s = 0)) _ _ = _
    rw [decide_eq_true noneFree, visit_none_free cursor noneFree]
    rfl
  · change cond (decide (free s = 0)) _ _ = _
    rw [decide_eq_false noneFree]
    change ((Data.fromFirst.eval Leaves.deferredKeys (inputsAt tb s cursor)).head?,
      (s.next, (s.permits, (s.taken,
        ((s.waiters.map (waiterC tb)).take
          ((s.waiters.map (waiterC tb)).length -
            (Data.fromFirst.eval Leaves.deferredKeys (inputsAt tb s cursor)).length) ++
          (waitersValue Data.fromFirst (inputsAt tb s cursor)).drop 1, ()))))) = _
    simp only [waitersValue]
    rw [fromFirst_eval, List.length_map, List.length_map, ← List.map_take, ← List.map_drop,
      ← List.map_append, List.head?_map, List.head?_eq_getElem?, visit_fromFirst s cursor noneFree]
    rfl

/-- The optional selected waiter keeps the existing reply encoding. -/
theorem visitReply_image (tb : Table) (selected : Option Waiter) :
    (imageAt Leaves.deferredKeys (.option waiterTy)).toVal (selected.map (waiterC tb)) =
      visitReplyVal tb selected := by
  cases selected <;> rfl

end Effect4.Semaphore.Model
