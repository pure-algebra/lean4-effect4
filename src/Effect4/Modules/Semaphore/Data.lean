module

public import Effect4.Modules.Semaphore.Cell
public import Effect4.Modules.Step.Lists
public import Effect4.Modules.Step.Inputs
meta import Effect4.Modules.Step.Elab.Inputs
meta import Effect4.Modules.Step.Elab
meta import Effect4.Schema.FieldRef.Elab

/-!
# Modules.Semaphore.Data — Semaphore's pure steps, written as data

All five steps are first-order data over the canonical cell schema.
`src/Effect4/Modules/Semaphore/Steps.lean` translates them to the public terms.
The laws connect their carrier evaluation to the independent model.
The comparison steps require a deferred identity interpretation and table injectivity.
No step performs an effect or establishes wrapper scheduling.
-/

@[expose] public section

namespace Effect4.Semaphore.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq : cellTy = .record cellRecord := rfl

def permitsF : FieldRef cellRecord .nat := field_ref% "permits"
def takenF : FieldRef cellRecord .nat := field_ref% "taken"
def waitersF : FieldRef cellRecord (.list waiterTy) := field_ref% "waiters"

/- A step's two inputs: the request's count, then the cell. -/
step_context% CountInputs (count : .nat, cell : cellTy)
step_context% VisitInputs (cursor : .nat, cell : cellTy)
abbrev Γ : List Ty := CountInputs.types

abbrev count : Input Γ .nat := input_ref% (CountInputs) count
abbrev cell : Input Γ (.record cellRecord) := input_ref% (CountInputs) cell

/-- The free count: the total less what is taken. -/
def free : Step Γ .nat := step_inputs% CountInputs =>
  .sub (.get cell permitsF) (.get cell takenF)

/-- **The model's `takeIfAvailable`.** Reply: whether the request took. -/
def takeIfAvailable := step_inputs% CountInputs =>
  .ite (.not (.lt free count))
    (.pair (.bool true) (.set cell takenF (.add (.get cell takenF) count)))
    (.pair (.bool false) cell)

/-- What a release leaves taken: `taken` less the count, truncated. -/
def left : Step Γ .nat := step_inputs% CountInputs => .sub (.get cell takenF) count

/-- **The model's `release`.** Reply: `[the free count, whether a waiter is enrolled]`. -/
def release := step_inputs% CountInputs =>
  .pair (.tuple2 (.sub (.get cell permitsF) left) (.not (.isZero (.len (.get cell waitersF)))))
    (.set cell takenF left)

/-- The cell's next enrolment stamp. -/
def nextF : FieldRef cellRecord .nat := field_ref% "next"
def waiterIdF : FieldRef waiterRecord idTy := field_ref% "id"
def waiterNeedF : FieldRef waiterRecord .nat := field_ref% "need"
def waiterStampF : FieldRef waiterRecord .nat := field_ref% "stamp"

/-- The free count of a cell step in any context. -/
def freeValue {Γ : List Ty} (s : Step Γ cellTy) : Step Γ .nat :=
  .sub (.get s permitsF) (.get s takenF)

/-- The compatibility input witness for the existing value equations. -/
abbrev freeAt {Γ : List Ty} (s : Input Γ cellTy) : Step Γ .nat := freeValue (.var s)

/-- Remove a request using the shared item-only removal builder. -/
def removeWith {Γ : List Ty} (xs : Step Γ (.list waiterTy)) (request : Step Γ idTy) :
    Step Γ (.list waiterTy) :=
  Step.Lists.removeBy xs (item_step% xs with entry => .sameDeferred (.get entry waiterIdF) request)

/-- The compatibility input witness for existing removal equations. -/
def remove {Γ : List Ty} (xs : Step Γ (.list waiterTy)) (request : Input Γ idTy) :
    Step Γ (.list waiterTy) := removeWith xs (.var request)

/-- Construct a waiter in the schema's canonical order. -/
def waiter {Γ : List Ty} (id : Step Γ idTy) (need : Step Γ .nat)
    (hint : Step Γ idTy) (stamp : Step Γ .nat) : Step Γ waiterTy :=
  record_step% { id := id, need := need, hint := hint, stamp := stamp }

step_context% TakeInputs (need : .nat, id : idTy, hint : idTy, cell : cellTy)
abbrev TakeΓ : List Ty := TakeInputs.types
abbrev takeNeed : Input TakeΓ .nat := input_ref% (TakeInputs) need
abbrev takeId : Input TakeΓ idTy := input_ref% (TakeInputs) id
abbrev takeHint : Input TakeΓ idTy := input_ref% (TakeInputs) hint
abbrev takeCell : Input TakeΓ cellTy := input_ref% (TakeInputs) cell

/-- Take or enrol, after removing the request's prior entry. -/
def take := step_inputs% TakeInputs =>
  let rest := removeWith (.get cell waitersF) id
  .ite (.not (.lt (freeValue cell) need))
    (.pair (.bool true)
      (.set (.set cell takenF (.add (.get cell takenF) need)) waitersF rest))
    (.pair (.bool false)
      (.set (.set cell waitersF
        (.snoc rest (waiter id need hint (.get cell nextF))))
        nextF (.add (.get cell nextF) (.nat 1))))

/-- The suffix beginning at the first fitting waiter. -/
def fromFirst := step_inputs% VisitInputs =>
  let xs : Step _ (.list waiterTy) := .get cell waitersF
  let available : Step _ .nat := freeValue cell
  fold_step% xs from suffix := .emptyLike xs with entry =>
    .ite (.or (.not (.isZero (.len suffix)))
        (.and (.not (.lt (.get entry waiterStampF) cursor))
          (.not (.lt available (.get entry waiterNeedF)))))
      (.snoc suffix entry) suffix

/-- Visit reserves nothing and removes the selected waiter by position. -/
def visit := step_inputs% VisitInputs =>
  let xs : Step _ (.list waiterTy) := .get cell waitersF
  .ite (.isZero (freeValue cell))
    (.pair (.head (.emptyLike xs)) cell)
    (.pair (.head fromFirst)
      (.set cell waitersF
        (.append (.take xs (.sub (.len xs) (.len fromFirst))) (.drop fromFirst (.nat 1)))))

step_context% WithdrawInputs (id : idTy, cell : cellTy)
abbrev WithdrawΓ : List Ty := WithdrawInputs.types
abbrev withdrawId : Input WithdrawΓ idTy := input_ref% (WithdrawInputs) id
abbrev withdrawCell : Input WithdrawΓ cellTy := input_ref% (WithdrawInputs) cell

/-- Withdrawal removes the request and changes no other field. -/
def withdraw := step_inputs% WithdrawInputs =>
  .pair .unit (.set cell waitersF (removeWith (.get cell waitersF) id))

end Effect4.Semaphore.Data
