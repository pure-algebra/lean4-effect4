import OCaml5.Lcnf.Translate

/-!
# The constructor census of the LCNF route

A type that the route spells natively (`OCaml5.Lcnf.typeRows`) has no declared record or variant in
OCaml. So the translator lowers each of its constructors and projections by an owner
(`OCaml5.Lcnf.nativeOwner?`): its row, OCaml's own datatype, or a transparent structure's
field. It refuses one with no owner by name. This battery reads the same function
over every constructor and every projection function of every such type, a proof field excepted,
and pins the table. A new type row, a new row or a Lean upgrade that adds a constructor changes the
table, and the change is a review event.

Before the census, three of these had no owner and no refusal. `ByteArray.mk` became a record of no
declared type, which only `ocamlopt` refused, and the words' `toBitVec` were holes at generation
(`docs/research/2026-10-16-ocaml-constructors/README.md`). The constructor lane runs every one
the route lowers (`Test/Codegen/ConstructorLane.lean`, `ocaml/engine/test/ctors/`).
-/

open Lean Meta OCaml5.Lcnf

namespace Test.Audit.ConstructorOwners

/-- An owner's name, as the table prints it. -/
def label : Option NativeOwner → String
  | some (.row _) => "row"
  | some .datatype => "datatype"
  | some .field => "field"
  | none => "none"

-- Finite evaluation: the owner of every constructor and every projection function of every type
-- the type table spells, in the table's order; a proof field is left out, since Lean's compiler
-- erases it. The walk is the `#eval`'s own, so no declaration of this module reads the
-- environment, whose meta library reaches `Classical.choice`.
-- Control: the last line, the residue. `Float` has no operation that lowers (its type row's
-- note), so its model's constructor and projection have no owner, and the translator refuses
-- each by name.
/--
info: Nat.zero: datatype
Nat.succ: datatype
Int.ofNat: row
Int.negSucc: row
UInt8.ofBitVec: row
UInt8.toBitVec: row
UInt16.ofBitVec: row
UInt16.toBitVec: row
UInt32.ofBitVec: row
UInt32.toBitVec: row
UInt64.ofBitVec: row
UInt64.toBitVec: row
USize.ofBitVec: row
USize.toBitVec: row
Bool.false: datatype
Bool.true: datatype
String.ofByteArray: row
String.toByteArray: row
PUnit.unit: datatype
Fin.mk: field
Fin.val: field
BitVec.ofFin: field
BitVec.toFin: field
Char.mk: field
Char.val: field
Float.ofModel: none
Float.toModel: none
List.nil: datatype
List.cons: datatype
Array.mk: row
Array.toList: row
ByteArray.mk: row
ByteArray.data: row
Option.none: datatype
Option.some: datatype
Prod.mk: datatype
Prod.fst: row
Prod.snd: row
Except.error: datatype
Except.ok: datatype
unowned: Float.ofModel, Float.toModel
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut unowned : List Name := []
  for r in typeRows do
    let some (.inductInfo info) := env.find? r.lean | continue
    let mut names := info.ctors
    if let some s := getStructureInfo? env r.lean then
      for f in s.fieldNames do
        let proj := r.lean ++ f
        let some ci := env.find? proj | continue
        unless ← forallTelescope ci.type fun _ body => isProp body do names := names ++ [proj]
    for n in names do
      let owner := nativeOwner? r.lean n
      IO.println s!"{n}: {label owner}"
      if owner.isNone then unowned := unowned ++ [n]
  IO.println s!"unowned: {", ".intercalate (unowned.map toString)}"

end Test.Audit.ConstructorOwners
