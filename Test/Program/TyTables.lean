import Effect4.Schema.TyFaces
import Effect4.Program.TyClasses

/-!
# Test.Program.TyTables — the per-constructor tables of `Ty` (decisions row 182 (a), slice C)

`tyFaces` stores one first-order recipe for each type constructor.
Fixed recipes use child references and a payload mark.
Record and tuple selectors retain the complete generated child lists.
`schema_eq_face` connects the interpreted algebra to `Schema.Bridge.schema` at every type.
The bridge's retraction and exactness results therefore apply to this table fold.

**The refusals a table gets from its generated type.** `TyTable` has one field per constructor of
`Ty` (`TyFoldExtras`, generated from the declaration), so a table with a row missing, a row for no
constructor, or a second row for one does not elaborate. The controls below pin the three, over the
classifier table's row type.
-/

set_option autoImplicit false

namespace Test.Program.TyTables

open Effect4 Effect4.Program

/-- **The Schema face table agrees with `Schema.Bridge.schema` at every type.** -/
theorem schema_eq_face (t : Ty) : Schema.Bridge.schema t = cata_ty (TyTable.schemaFace tyFaces) t :=
  rfl

/-- error: Fields missing: `unknown` -/
#guard_msgs (error) in
example : TyTable ClassRow where
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
  record := ⟨true, true⟩
  map := ⟨true, true⟩
  tuple := ⟨true, true⟩
  app := ⟨false, false⟩
  null := ⟨true, true⟩
  undefined := ⟨true, true⟩
  number := ⟨true, true⟩
  bytes := ⟨true, true⟩

/-- error: `bigint` is not a field of structure `TyTable` -/
#guard_msgs (error) in
example : TyTable ClassRow := { tyClasses with bigint := ⟨true, true⟩ }

/-- error: field `never` has already been specified -/
#guard_msgs (error) in
example : TyTable ClassRow := { tyClasses with never := ⟨true, true⟩, never := ⟨false, true⟩ }

end Test.Program.TyTables
