import Effect4.Modules.Pool.Data
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Pool.Relation

/-!
# Laws.Modules.Pool.Data — Pool's model on the step language's carriers

The connector between Pool's model and its steps written as data
(`src/Effect4/Modules/Pool/Data.lean`; decisions row 330, slice L3). It has the three parts of
Semaphore's (`src/Effect4/Laws/Modules/Semaphore/Data.lean`): the reading law, once; the
encoding, once for the module (`cellVal_image`); and each step's value as the model's
transition (`select_eval`, `close_eval`).

**The resource type is a parameter.** A step's term never mentions it, so the reading is taken
with the type variable `P` in place of the resource type, whose carrier at the opaque context is the value itself.
A resource's value is then the model's `res` of its name, as in `cellVal`.

Placement: concept `translation-simulation`, requirement R10, helpers of the claim
`pool-steps-agree`'s parts `selectStep_agrees` and `closeStep_agrees`
(`src/Effect4/Laws/Modules/Pool/Steps.lean`). Nothing here covers a step that folds.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Pool (cellRecord)

/-- The type variable that stands for the resource type. -/
abbrev P : Ty := .var 0

/-- An item on the carrier of the opaque context, its resource through the resources' values. -/
def itemC (res : Nat → Val) (it : Item) : CarrierAt Leaves.opaque (itemTy P) :=
  (it.borrowed, (it.lease, (res it.resource, (it.stamp, ()))))

/-- A waiter on the carrier of the opaque context: its hint and its identity through the table. -/
def waiterC (tb : Table) (id : Nat) : CarrierAt Leaves.opaque waiterTy :=
  (Val.promise (tb.hint id), (Val.promise (tb.handle id), ()))

/-- **A model state on the carrier of the opaque context.** -/
def cellC (tb : Table) (res : Nat → Val) (s : State) :
    CarrierAt Leaves.opaque (.record (cellRecord P)) :=
  (s.available, (s.closing, (s.items.map (itemC res), (s.next, (s.waiters.map (waiterC tb), ())))))

/-- **The encoding**: a model state's carrier has the cell's value as its image. -/
theorem cellVal_image (tb : Table) (res : Nat → Val) (s : State) :
    (imageAt Leaves.opaque (.record (cellRecord P))).toVal (cellC tb res s) = cellVal tb res s := by
  show Val.ctor 0 [.list [.str "available", .str "closing", .str "items", .str "next", .str "waiters"],
      .list [.list (s.available.map (imageAt Leaves.opaque .nat).toVal), .bool s.closing,
        .list ((s.items.map (itemC res)).map (imageAt Leaves.opaque (itemTy P)).toVal), .nat s.next,
        .list ((s.waiters.map (waiterC tb)).map (imageAt Leaves.opaque waiterTy).toVal)]] = _
  rw [List.map_map, List.map_map]
  rfl

/-- The waiters of a selection's reply, encoded. -/
theorem selectReply_image (tb : Table) (selected : List Nat) :
    (imageAt Leaves.opaque (.list waiterTy)).toVal (selected.map (waiterC tb)) =
      selectReplyVal tb selected := by
  show Val.list ((selected.map (waiterC tb)).map (imageAt Leaves.opaque waiterTy).toVal) = _
  rw [List.map_map]
  rfl

/-- The select step's inputs at a count and a model state. -/
abbrev selectInputs (tb : Table) (res : Nat → Val) (s : State) (count : Nat) :
    Inputs Leaves.opaque (Data.Γ P) :=
  (count, (cellC tb res s, ()))

/-- The close's input at a model state. -/
abbrev cellInputs (tb : Table) (res : Nat → Val) (s : State) :
    Inputs Leaves.opaque [.record (cellRecord P)] :=
  (cellC tb res s, ())

/-- **The select step's value is the model's transition.** -/
theorem select_eval (tb : Table) (res : Nat → Val) (s : State) (count : Nat) :
    (Data.select P).eval Leaves.opaque (selectInputs tb res s count) =
      ((select s count).2.map (waiterC tb), cellC tb res (select s count).1) := by
  show ((s.waiters.map (waiterC tb)).take count,
      (s.available, (s.closing, (s.items.map (itemC res),
        (s.next, ((s.waiters.map (waiterC tb)).drop count, ())))))) = _
  rw [← List.map_take, ← List.map_drop]
  rfl

/-- **The close's value is the model's transition.** -/
theorem close_eval (tb : Table) (res : Nat → Val) (s : State) :
    (Data.close P).eval Leaves.opaque (cellInputs tb res s) =
      ((close s).2, cellC tb res (close s).1) := by
  show ((!s.closing, (s.waiters.map (waiterC tb)).length), cellC tb res { s with closing := true }) = _
  rw [List.length_map]
  rfl

end Effect4.Pool.Model
