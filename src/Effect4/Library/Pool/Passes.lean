module

public import Effect4.Library.Pool.Cell
public import Effect4.Step.Lists
public import Effect4.Step.Inputs
meta import Effect4.Schema.FieldRef.Elab
meta import Effect4.Step.Elab.Inputs

/-! Pool's pure passes as Step data. Inputs captured by a fold retain their positions after
its accumulator and element. The independent model remains in the Laws graph. -/

@[expose] public section
set_option autoImplicit false

namespace Effect4.Pool.Data
open Effect4.Program Effect4.Schema Effect4.Modules

step_context% selectInputs (A : Ty) where (count : .nat, cell : cellTy A)
step_context% closeInputs (A : Ty) where (cell : cellTy A)
step_context% waiterInputs (id : idTy, hint : idTy)
step_context% leaseInputs (A : Ty) where (id : idTy, hint : idTy, cell : cellTy A)
step_context% returnInputs (A : Ty) where (stamp : .nat, lease : .nat, cell : cellTy A)
step_context% withdrawInputs (A : Ty) where (id : idTy, cell : cellTy A)
step_context% leaseItemInputs (A : Ty) where (lease : .nat, item : itemTy A)
step_context% holdsInputs (A : Ty) where (stamp : .nat, lease : .nat, item : itemTy A)

variable {Γ : List Ty}

def availableF (A : Ty) : FieldRef (cellRecord A) (.list .nat) := field_ref% "available"
def itemsF (A : Ty) : FieldRef (cellRecord A) (.list (itemTy A)) := field_ref% "items"
def nextF (A : Ty) : FieldRef (cellRecord A) .nat := field_ref% "next"
def passWaitersF (A : Ty) : FieldRef (cellRecord A) (.list waiterTy) := field_ref% "waiters"
def itemBorrowedF (A : Ty) : FieldRef (itemRecord A) .bool := field_ref% "borrowed"
def itemLeaseF (A : Ty) : FieldRef (itemRecord A) .nat := field_ref% "lease"
def itemStampF (A : Ty) : FieldRef (itemRecord A) .nat := field_ref% "stamp"
def waiterIdF : FieldRef waiterRecord idTy := field_ref% "id"

def headStamp (A : Ty) (cell : Step Γ (cellTy A)) : Step Γ .nat :=
  Step.Lists.headOr (.get cell (availableF A)) (.nat 0)

def removed (A : Ty) (id : Step Γ idTy) (cell : Step Γ (cellTy A)) :
    Step Γ (.list waiterTy) :=
  let waiters : Step Γ (.list waiterTy) := .get cell (passWaitersF A)
  Step.Lists.removeBy waiters (item_step% waiters with waiter =>
    .sameDeferred (.get waiter waiterIdF) id)

def withdrawn (A : Ty) (id : Step Γ idTy) (cell : Step Γ (cellTy A)) : Step Γ (cellTy A) :=
  .set cell (passWaitersF A) (removed A id cell)

def leasedAs (A : Ty) (lease : Step Γ .nat) (item : Step Γ (itemTy A)) : Step Γ (itemTy A) :=
  .set (.set item (itemBorrowedF A) (.bool true)) (itemLeaseF A) lease

def marked (A : Ty) (cell : Step Γ (cellTy A)) : Step Γ (.list (itemTy A)) :=
  let items : Step Γ (.list (itemTy A)) := .get cell (itemsF A)
  Step.Lists.map items (item_step% items with item =>
    .ite (.eq (.get item (itemStampF A)) (headStamp A cell))
      (leasedAs A (.get cell (nextF A)) item) item)

def leasedOf (A : Ty) (cell : Step Γ (cellTy A)) : Step Γ (.list (itemTy A)) :=
  let items : Step Γ (.list (itemTy A)) := .get cell (itemsF A)
  Step.Lists.filterMap items (item_step% items with item =>
    .eq (.get item (itemStampF A)) (headStamp A cell))
    (item_step% items with item => leasedAs A (.get cell (nextF A)) item)

def holds (A : Ty) (stamp lease : Step Γ .nat) (item : Step Γ (itemTy A)) : Step Γ .bool :=
  .and (.eq (.get item (itemStampF A)) stamp)
    (.and (.get item (itemBorrowedF A)) (.eq (.get item (itemLeaseF A)) lease))

def heldBy (A : Ty) (stamp lease : Step Γ .nat) (cell : Step Γ (cellTy A)) : Step Γ .bool :=
  let items : Step Γ (.list (itemTy A)) := .get cell (itemsF A)
  Step.Lists.any items (item_step% items with item => holds A stamp lease item)

def freed (A : Ty) (stamp lease : Step Γ .nat) (cell : Step Γ (cellTy A)) :
    Step Γ (.list (itemTy A)) :=
  let items : Step Γ (.list (itemTy A)) := .get cell (itemsF A)
  Step.Lists.map items (item_step% items with item =>
    .ite (holds A stamp lease item) (.set item (itemBorrowedF A) (.bool false)) item)

def outstanding (A : Ty) (cell : Step Γ (cellTy A)) : Step Γ .bool :=
  let items : Step Γ (.list (itemTy A)) := .get cell (itemsF A)
  Step.Lists.any items (item_step% items with item => .get item (itemBorrowedF A))

end Effect4.Pool.Data
