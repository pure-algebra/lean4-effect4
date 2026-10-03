import Effect4.Schema.TyFaces
import Effect4.Program.TyClasses

/-!
# Test.Program.TyTables — the per-constructor tables of `Ty` (decisions row 182 (a), slice C)

**The Schema face table is the hand fold.** `tyFaces` writes each constructor's node of rc.112's
Schema IR as a template (`Schema.Template`: children as references, the payload at a mark), and its
fold agrees with `Schema.Bridge.schema` at every type (`schema_eq_face`): the generated uniqueness in
layer form (`eq_cata_ofLayer`), each constructor's layer checked by computation. Every property
proved of `Bridge.schema` (the bridge's exactness, `ofSchema_exact`) holds of the table's fold.

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
  eq_cata_ofLayer _ Schema.Bridge.schema (fun t => by cases t <;> rfl) t

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
