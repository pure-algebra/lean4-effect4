module

public import Effect4.Program.TyFoldExtras

/-!
# The classifier table of `Ty` (decisions row 182 (a), slice C)

A classifier asks one question of every node of a type and requires the answer everywhere: one
Boolean column per question, answered once per constructor, read by the generated head fold
(`TyAlgebra.headAlg`): a node's answer and all of its children's. A constructor appended to `Ty` is
one row here, and the table does not elaborate until the row is written (`TyTable` is generated from
the declaration, `TyFoldExtras`); no column has a default.

A column lands with its consumer. Today: `handleFree`, the data fragment's classifier, and
`shapeDecides`, where the shape check (`Val.hasTy`) is membership at every world, read by the Schema
answer bridge (both in `Laws/Program/Typed/Membership.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-- One constructor's answers to the classifier questions. -/
structure ClassRow where
  /-- The node holds no handle, nominal reference, fiber, cell or deferred: its members name no
  world entry. -/
  handleFree : Bool
  /-- At this node the shape check decides membership at every world: not a handle, a nominal
  reference, fiber, cell, deferred or `unknown` (members read the world), and not an exit (its
  membership also asks a shape-free cause, decisions row 152). -/
  shapeDecides : Bool

/-- **Every node in a class**: the head fold `(Bool, &&)` of a column, the node's answer and all of
its children's. -/
def TyTable.allHeads (tbl : TyTable ClassRow) (col : ClassRow → Bool) : TyAlgebra (fun _ => Bool) :=
  TyAlgebra.headAlg true (· && ·) fun c _ => col (tbl.get c)

/-- The classifier table of `Ty`. -/
def tyClasses : TyTable ClassRow where
  never := ⟨true, true⟩
  unit := ⟨true, true⟩
  nat := ⟨true, true⟩
  int := ⟨true, true⟩
  string := ⟨true, true⟩
  bool := ⟨true, true⟩
  handle := ⟨false, false⟩
  option := ⟨true, true⟩
  list := ⟨true, true⟩
  prod := ⟨true, true⟩
  except := ⟨true, true⟩
  exitOf := ⟨true, false⟩
  causeOf := ⟨true, true⟩
  fiberOf := ⟨false, false⟩
  union := ⟨true, true⟩
  lit := ⟨true, true⟩
  refOf := ⟨false, false⟩
  deferredOf := ⟨false, false⟩
  var := ⟨true, true⟩
  unknown := ⟨true, false⟩
  record := ⟨true, true⟩
  map := ⟨true, true⟩
  tuple := ⟨true, true⟩
  app := ⟨false, false⟩
  null := ⟨true, true⟩
  undefined := ⟨true, true⟩
  number := ⟨true, true⟩
  bytes := ⟨true, true⟩

end Effect4.Program
