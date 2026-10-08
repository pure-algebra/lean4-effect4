module

public import Effect4.Modules.Pool.Passes
public import Effect4.Modules.Step
meta import Effect4.Schema.FieldRef.Elab

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
abbrev Γ (A : Ty) : List Ty := [.nat, .record (cellRecord A)]

def count (A : Ty) : Input (Γ A) .nat := .here _ _
def cell (A : Ty) : Input (Γ A) (.record (cellRecord A)) := .there _ (.here _ _)

/-- **The model's `select`.** Reply: the first `count` waiters. -/
def select (A : Ty) : Step (Γ A) (.prod (.list waiterTy) (.record (cellRecord A))) :=
  .pair (.take (.get (.var (cell A)) (waitersF A)) (.var (count A)))
    (.set (.var (cell A)) (waitersF A) (.drop (.get (.var (cell A)) (waitersF A)) (.var (count A))))

/-- The close's one input: the cell. -/
def only (A : Ty) : Input [.record (cellRecord A)] (.record (cellRecord A)) := .here _ _

/-- **The model's `close`.** Reply: `[this step began the close, the count of the waiters]`. -/
def close (A : Ty) : Step [.record (cellRecord A)] (.prod (.prod .bool .nat) (.record (cellRecord A))) :=
  .pair (.tuple2 (.not (.get (.var (only A)) (closingF A))) (.len (.get (.var (only A)) (waitersF A))))
    (.set (.var (only A)) (closingF A) (.bool true))


/-! ## The passes and the four remaining operations -/

variable {Γ : List Ty}

def noItem (A : Ty) (c : Input Γ (cellTy A)) : Step Γ (.option (itemTy A)) :=
  .head (.emptyLike (.get (.var c) (itemsF A)))

def mkWaiter (id hint : Input Γ idTy) : Step Γ waiterTy :=
  .record (.cons "hint" (.var hint) (.cons "id" (.var id) .nil))

abbrev leaseΓ (A : Ty) : List Ty := [idTy, idTy, cellTy A]
def leaseId (A : Ty) : Input (leaseΓ A) idTy := .here _ _
def leaseHint (A : Ty) : Input (leaseΓ A) idTy := .there _ (.here _ _)
def leaseCell (A : Ty) : Input (leaseΓ A) (cellTy A) := .there _ (.there _ (.here _ _))

def enrolled (A : Ty) : Step (leaseΓ A) (cellTy A) :=
  .set (.var (leaseCell A)) (waitersF A)
    (.snoc (removed A (leaseId A) (leaseCell A)) (mkWaiter (leaseId A) (leaseHint A)))

def lease (A : Ty) : Step (leaseΓ A) (.prod (.prod .bool (.option (itemTy A))) (cellTy A)) :=
  .ite (.get (.var (leaseCell A)) (closingF A))
    (.pair (.tuple2 (.bool true) (noItem A (leaseCell A)))
      (withdrawn A (leaseId A) (leaseCell A)))
    (.ite (.isZero (.len (.get (.var (leaseCell A)) (availableF A))))
      (.pair (.tuple2 (.bool false) (noItem A (leaseCell A))) (enrolled A))
      (.pair (.tuple2 (.bool false) (.head (leasedOf A (leaseCell A))))
        (.set
          (.set (.set (withdrawn A (leaseId A) (leaseCell A)) (itemsF A) (marked A (leaseCell A)))
            (availableF A) (.drop (.get (.var (leaseCell A)) (availableF A)) (.nat 1)))
          (nextF A) (.add (.get (.var (leaseCell A)) (nextF A)) (.nat 1)))))

abbrev returnΓ (A : Ty) : List Ty := [.nat, .nat, cellTy A]
def returnStamp (A : Ty) : Input (returnΓ A) .nat := .here _ _
def returnLease (A : Ty) : Input (returnΓ A) .nat := .there _ (.here _ _)
def returnCell (A : Ty) : Input (returnΓ A) (cellTy A) := .there _ (.there _ (.here _ _))

def giveBack (A : Ty) : Step (returnΓ A) (.prod (.prod .bool .bool) (cellTy A)) :=
  .ite (heldBy A (returnStamp A) (returnLease A) (returnCell A))
    (.pair (.tuple2 (.bool true) (.not (.isZero (.len (.get (.var (returnCell A)) (waitersF A))))))
      (.set (.set (.var (returnCell A)) (itemsF A)
          (freed A (returnStamp A) (returnLease A) (returnCell A)))
        (availableF A) (.cons (.var (returnStamp A)) (.get (.var (returnCell A)) (availableF A)))))
    (.pair (.tuple2 (.bool false) (.bool false)) (.var (returnCell A)))

abbrev withdrawΓ (A : Ty) : List Ty := [idTy, cellTy A]
def withdrawId (A : Ty) : Input (withdrawΓ A) idTy := .here _ _
def withdrawCell (A : Ty) : Input (withdrawΓ A) (cellTy A) := .there _ (.here _ _)

def withdraw (A : Ty) : Step (withdrawΓ A) (.prod .unit (cellTy A)) :=
  .pair .unit (withdrawn A (withdrawId A) (withdrawCell A))

def drain (A : Ty) : Step (leaseΓ A) (.prod .bool (cellTy A)) :=
  .ite (outstanding A (leaseCell A))
    (.pair (.bool false) (enrolled A))
    (.pair (.bool true) (withdrawn A (leaseId A) (leaseCell A)))

end Effect4.Pool.Data
