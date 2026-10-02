import Effect4.Program.TyFoldExtras

/-!
# The classifier table of `Ty` (decisions row 182 (a), slice C)

A classifier asks one question of every node of a type and requires the answer everywhere: one
Boolean column per question, answered once per constructor, read by the generated head fold
(`TyAlgebra.headAlg`): a node's answer and all of its children's. A constructor appended to `Ty` is
one row here, and the table does not elaborate until the row is written (`TyTable` is generated from
the declaration, `TyFoldExtras`); no column has a default.

A column lands with its consumer. Today: `handleFree`, the data fragment's classifier
(`Laws/Program/Typed/Membership.lean`).
-/

set_option autoImplicit false

namespace Effect4.Program

/-- One constructor's answers to the classifier questions. -/
structure ClassRow where
  /-- The node holds no handle, fiber, cell or deferred: its members name no world entry. -/
  handleFree : Bool

/-- **Every node in a class**: the head fold `(Bool, &&)` of a column, the node's answer and all of
its children's. -/
def TyTable.allHeads (tbl : TyTable ClassRow) (col : ClassRow → Bool) : TyAlgebra (fun _ => Bool) :=
  TyAlgebra.headAlg (· && ·) fun c _ => col (tbl.get c)

/-- The classifier table of `Ty`. -/
def tyClasses : TyTable ClassRow where
  never := ⟨true⟩
  unit := ⟨true⟩
  nat := ⟨true⟩
  int := ⟨true⟩
  string := ⟨true⟩
  bool := ⟨true⟩
  handle := ⟨false⟩
  option := ⟨true⟩
  list := ⟨true⟩
  prod := ⟨true⟩
  except := ⟨true⟩
  exitOf := ⟨true⟩
  causeOf := ⟨true⟩
  fiberOf := ⟨false⟩
  union := ⟨true⟩
  lit := ⟨true⟩
  refOf := ⟨false⟩
  deferredOf := ⟨false⟩
  var := ⟨true⟩
  unknown := ⟨true⟩

end Effect4.Program
