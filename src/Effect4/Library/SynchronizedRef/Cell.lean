module

public import Effect4.Library.Ref.Model
public import Effect4.Library.Semaphore.Cell

/-! The latest SynchronizedRef handle contains a backing Ref and a one-permit Semaphore.
The independent pure value model is Ref.Model; this handle is identity-bearing program data.
Source: vendor/effect-4.0.1/src/SynchronizedRef.ts, fields 38–42. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.SynchronizedRef
open Effect4.Program

/-- Required handle fields, in canonical byte order. -/
def handleFields (A : Ty) : List (String × Bool × Ty) :=
  [("backing", false, .refOf A), ("semaphore", false, .refOf Semaphore.cellTy)]

/-- The constructor's declared result, with the backing value type retained. -/
def handleTy (A : Ty) : Ty := .record (handleFields A)

/-- The actual library components of the pure wrapper, for decisions row 335. -/
def buildingBlocks : List String := ["Ref", "Semaphore"]

end Effect4.SynchronizedRef
