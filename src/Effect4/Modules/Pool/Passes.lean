module

public import Effect4.Modules.Pool.Cell
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

/-! Pool's pure passes as Step data. Inputs captured by a fold retain their positions after
its accumulator and element. The independent model remains in the Laws graph. -/

@[expose] public section
set_option autoImplicit false

namespace Effect4.Pool.Data
open Effect4.Program Effect4.Schema Effect4.Modules

variable {Γ : List Ty}

def availableF (A : Ty) : FieldRef (cellRecord A) (.list .nat) := field_ref% "available"
def itemsF (A : Ty) : FieldRef (cellRecord A) (.list (itemTy A)) := field_ref% "items"
def nextF (A : Ty) : FieldRef (cellRecord A) .nat := field_ref% "next"
def passWaitersF (A : Ty) : FieldRef (cellRecord A) (.list waiterTy) := field_ref% "waiters"
def itemBorrowedF (A : Ty) : FieldRef (itemRecord A) .bool := field_ref% "borrowed"
def itemLeaseF (A : Ty) : FieldRef (itemRecord A) .nat := field_ref% "lease"
def itemStampF (A : Ty) : FieldRef (itemRecord A) .nat := field_ref% "stamp"
def waiterIdF : FieldRef waiterRecord idTy := field_ref% "id"

/-- An outer input under the fold's accumulator and element. -/
def under {t : Ty} (acc item : Ty) (x : Input Γ t) : Input (acc :: item :: Γ) t :=
  .there _ (.there _ x)

def headStamp (A : Ty) (cell : Input Γ (cellTy A)) : Step Γ .nat :=
  .fold (.take (.get (.var cell) (availableF A)) (.nat 1)) (.nat 0)
    (.var (.there _ (.here _ _)))

def removed (A : Ty) (id : Input Γ idTy) (cell : Input Γ (cellTy A)) :
    Step Γ (.list waiterTy) :=
  .fold (.get (.var cell) (passWaitersF A)) (.emptyLike (.get (.var cell) (passWaitersF A)))
    (.ite (.sameDeferred (.get (.var (.there _ (.here _ _))) waiterIdF)
        (.var (under (.list waiterTy) waiterTy id)))
      (.var (.here _ _))
      (.snoc (.var (.here _ _)) (.var (.there _ (.here _ _)))))

def withdrawn (A : Ty) (id : Input Γ idTy) (cell : Input Γ (cellTy A)) : Step Γ (cellTy A) :=
  .set (.var cell) (passWaitersF A) (removed A id cell)

def leasedAs (A : Ty) (lease : Step Γ .nat) (item : Step Γ (itemTy A)) : Step Γ (itemTy A) :=
  .set (.set item (itemBorrowedF A) (.bool true)) (itemLeaseF A) lease

def marked (A : Ty) (cell : Input Γ (cellTy A)) : Step Γ (.list (itemTy A)) :=
  .fold (.get (.var cell) (itemsF A)) (.emptyLike (.get (.var cell) (itemsF A)))
    (.snoc (.var (.here _ _))
      (.ite (.eq (.get (.var (.there _ (.here _ _))) (itemStampF A))
          (headStamp A (under (.list (itemTy A)) (itemTy A) cell)))
        (leasedAs A (.get (.var (under (.list (itemTy A)) (itemTy A) cell)) (nextF A))
          (.var (.there _ (.here _ _))))
        (.var (.there _ (.here _ _)))))

def leasedOf (A : Ty) (cell : Input Γ (cellTy A)) : Step Γ (.list (itemTy A)) :=
  .fold (.get (.var cell) (itemsF A)) (.emptyLike (.get (.var cell) (itemsF A)))
    (.ite (.eq (.get (.var (.there _ (.here _ _))) (itemStampF A))
        (headStamp A (under (.list (itemTy A)) (itemTy A) cell)))
      (.snoc (.var (.here _ _))
        (leasedAs A (.get (.var (under (.list (itemTy A)) (itemTy A) cell)) (nextF A))
          (.var (.there _ (.here _ _)))))
      (.var (.here _ _)))

def holds (A : Ty) (stamp lease : Input Γ .nat) (item : Input Γ (itemTy A)) : Step Γ .bool :=
  .and (.eq (.get (.var item) (itemStampF A)) (.var stamp))
    (.and (.get (.var item) (itemBorrowedF A))
      (.eq (.get (.var item) (itemLeaseF A)) (.var lease)))

def heldBy (A : Ty) (stamp lease : Input Γ .nat) (cell : Input Γ (cellTy A)) : Step Γ .bool :=
  .fold (.get (.var cell) (itemsF A)) (.bool false)
    (.or (.var (.here _ _))
      (holds A (under .bool (itemTy A) stamp) (under .bool (itemTy A) lease)
        (.there _ (.here _ _))))

def freed (A : Ty) (stamp lease : Input Γ .nat) (cell : Input Γ (cellTy A)) :
    Step Γ (.list (itemTy A)) :=
  .fold (.get (.var cell) (itemsF A)) (.emptyLike (.get (.var cell) (itemsF A)))
    (.snoc (.var (.here _ _))
      (.ite (holds A (under (.list (itemTy A)) (itemTy A) stamp)
          (under (.list (itemTy A)) (itemTy A) lease) (.there _ (.here _ _)))
        (.set (.var (.there _ (.here _ _))) (itemBorrowedF A) (.bool false))
        (.var (.there _ (.here _ _)))))

def outstanding (A : Ty) (cell : Input Γ (cellTy A)) : Step Γ .bool :=
  .fold (.get (.var cell) (itemsF A)) (.bool false)
    (.or (.var (.here _ _)) (.get (.var (.there _ (.here _ _))) (itemBorrowedF A)))

end Effect4.Pool.Data
