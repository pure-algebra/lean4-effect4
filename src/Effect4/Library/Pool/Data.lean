module

public import Effect4.Library.Pool.Passes
public import Effect4.Step
meta import Effect4.Schema.FieldRef.Elab
meta import Effect4.Step.Elab.Inputs

/-!
# Modules.Pool.Data — Pool's six operations as Step data

The operations reuse the passes in `Modules.Pool.Passes`.
Their public terms live in `Modules.Pool.Steps`, which imports this module.
The independent model and its reading and typing laws remain in the Laws graph.
-/

@[expose] public section

namespace Effect4.Pool.Data

open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

theorem cellTy_eq (A : Ty) : cellTy A = .record (cellRecord A) := rfl

def closingF (A : Ty) : FieldRef (cellRecord A) .bool := field_ref% "closing"
def waitersF (A : Ty) : FieldRef (cellRecord A) (.list waiterTy) := field_ref% "waiters"

/-- The select step's inputs: the count, then the cell. -/
abbrev Γ (A : Ty) : List Ty := (selectInputs A).types


/-- **The model's `select`.** Reply: the first `count` waiters. -/
def select (A : Ty) : Step (Γ A) (.prod (.list waiterTy) (.record (cellRecord A))) :=
  step_inputs% (selectInputs A) =>
    .pair (.take (.get cell (waitersF A)) count)
      (.set cell (waitersF A) (.drop (.get cell (waitersF A)) count))


/-- **The model's `close`.** Reply: `[this step began the close, the count of the waiters]`. -/
def close (A : Ty) : Step (closeInputs A).types (.prod (.prod .bool .nat) (.record (cellRecord A))) :=
  step_inputs% (closeInputs A) =>
    .pair (.tuple2 (.not (.get cell (closingF A))) (.len (.get cell (waitersF A))))
      (.set cell (closingF A) (.bool true))


/-! ## The passes and the four remaining operations -/

variable {Γ : List Ty}

def noItem (A : Ty) (c : Step Γ (cellTy A)) : Step Γ (.option (itemTy A)) :=
  .head (.emptyLike (.get c (itemsF A)))

def mkWaiter (id hint : Step Γ idTy) : Step Γ waiterTy :=
  .record (.cons "hint" hint (.cons "id" id .nil))

abbrev leaseΓ (A : Ty) : List Ty := (leaseInputs A).types

def enrolled (A : Ty) : Step (leaseΓ A) (cellTy A) :=
  step_inputs% (leaseInputs A) =>
    .set cell (waitersF A)
      (.snoc (removed A id cell) (mkWaiter id hint))

def lease (A : Ty) : Step (leaseΓ A) (.prod (.prod .bool (.option (itemTy A))) (cellTy A)) :=
  step_inputs% (leaseInputs A) =>
    .ite (.get cell (closingF A))
      (.pair (.tuple2 (.bool true) (noItem A cell))
        (withdrawn A id cell))
      (.ite (.isZero (.len (.get cell (availableF A))))
        (.pair (.tuple2 (.bool false) (noItem A cell)) (enrolled A))
        (.pair (.tuple2 (.bool false) (.head (leasedOf A cell)))
          (.set
            (.set (.set (withdrawn A id cell) (itemsF A) (marked A cell))
              (availableF A) (.drop (.get cell (availableF A)) (.nat 1)))
            (nextF A) (.add (.get cell (nextF A)) (.nat 1)))))

abbrev returnΓ (A : Ty) : List Ty := (returnInputs A).types

def giveBack (A : Ty) : Step (returnΓ A) (.prod (.prod .bool .bool) (cellTy A)) :=
  step_inputs% (returnInputs A) =>
    .ite (heldBy A stamp lease cell)
      (.pair (.tuple2 (.bool true) (.not (.isZero (.len (.get cell (waitersF A))))))
        (.set (.set cell (itemsF A)
            (freed A stamp lease cell))
          (availableF A) (.cons stamp (.get cell (availableF A)))))
      (.pair (.tuple2 (.bool false) (.bool false)) cell)

abbrev withdrawΓ (A : Ty) : List Ty := (withdrawInputs A).types

def withdraw (A : Ty) : Step (withdrawΓ A) (.prod .unit (cellTy A)) :=
  step_inputs% (withdrawInputs A) =>
    .pair .unit (withdrawn A id cell)

def drain (A : Ty) : Step (leaseΓ A) (.prod .bool (cellTy A)) :=
  step_inputs% (leaseInputs A) =>
    .ite (outstanding A cell)
      (.pair (.bool false) (enrolled A))
      (.pair (.bool true) (withdrawn A id cell))

def waiterPass : Step waiterInputs.types waiterTy :=
  step_inputs% waiterInputs => mkWaiter id hint
def withdrawnPass (A : Ty) : Step (withdrawInputs A).types (cellTy A) :=
  step_inputs% (withdrawInputs A) => withdrawn A id cell
def noItemPass (A : Ty) : Step (closeInputs A).types (.option (itemTy A)) :=
  step_inputs% (closeInputs A) => noItem A cell
def headStampPass (A : Ty) : Step (closeInputs A).types .nat :=
  step_inputs% (closeInputs A) => headStamp A cell
def leasedAsPass (A : Ty) : Step (leaseItemInputs A).types (itemTy A) :=
  step_inputs% (leaseItemInputs A) => leasedAs A lease item
def markedPass (A : Ty) : Step (closeInputs A).types (.list (itemTy A)) :=
  step_inputs% (closeInputs A) => marked A cell
def leasedOfPass (A : Ty) : Step (closeInputs A).types (.list (itemTy A)) :=
  step_inputs% (closeInputs A) => leasedOf A cell
def holdsPass (A : Ty) : Step (holdsInputs A).types .bool :=
  step_inputs% (holdsInputs A) => holds A stamp lease item
def heldByPass (A : Ty) : Step (returnInputs A).types .bool :=
  step_inputs% (returnInputs A) => heldBy A stamp lease cell
def freedPass (A : Ty) : Step (returnInputs A).types (.list (itemTy A)) :=
  step_inputs% (returnInputs A) => freed A stamp lease cell
def outstandingPass (A : Ty) : Step (closeInputs A).types .bool :=
  step_inputs% (closeInputs A) => outstanding A cell

end Effect4.Pool.Data
