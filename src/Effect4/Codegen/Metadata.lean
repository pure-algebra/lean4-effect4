import Effect4.Store.Carrier.Fold
import Effect4.Store.Domain.Derived.Program
import TypeScript.Syntax

/-!
# Exact structural type metadata

`writeTy` retains raw type declarations for the record printer. The metadata uses the existing
`Canonical Ty` value image and the generated value fold. Arbitrary naturals use base-256 digits,
each printed as an integer from zero through 255. No framed byte length or `Val.WF` premise is
needed. The structural reader refuses expressions outside this canonical image.

The laws live in `Laws/Codegen/Metadata.lean`, under the proposed claim `type-metadata-exact`.
This boundary says nothing about JavaScript execution or rendered-source parsing.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Metadata
open Effect4.Store TypeScript

/-- One byte as a target integer that JavaScript represents exactly. -/
def writeByte (b : UInt8) : Expr := .int (.ofNat b.toNat)

/-- Byte data has no frame-length prefix in structural metadata. -/
def writeBytes (bs : Bytes) : Expr := .arr (bs.map writeByte)

/-- Arbitrary naturals use the existing canonical digit spelling. -/
def writeNat (n : Nat) : Expr := writeBytes (natBytes n)

/-- The generated value fold's algebra. The tag bytes retain their existing owner. -/
def valueAlgebra : ValAlgebra (fun _ => Expr) where
  val_unit := .arr [writeByte Tag.unit]
  val_bool b := .arr [writeByte Tag.bool, .bool b]
  val_nat n := .arr [writeByte Tag.nat, writeNat n]
  val_str s := .arr [writeByte Tag.string, .str s]
  val_bytes bs := .arr [writeByte Tag.bytes, writeBytes bs]
  val_list xs := .arr [writeByte Tag.list, .arr xs]
  val_pair a b := .arr [writeByte Tag.pair, a, b]
  val_none := .arr [writeByte Tag.none]
  val_some a := .arr [writeByte Tag.some, a]
  val_ctor i xs := .arr [writeByte Tag.ctor, writeNat i, .arr xs]
  val_ref k bs := .arr [writeByte Tag.ref, writeByte k, writeBytes bs]
  val_handle k n := .arr [writeByte Tag.handle, writeByte k, writeNat n]
  val_negInt n := .arr [writeByte Tag.int, writeNat n]
  val_float bits := .arr [writeByte Tag.float, writeNat bits.toNat]

/-- A structural target expression for any raw value, through the generated fold. -/
def writeValue (v : Val) : Expr := cata_val valueAlgebra v

/-- Read only a nonnegative byte-sized integer literal. -/
def readByte : Expr → Option UInt8
  | .int (.ofNat n) => if n < 256 then some (UInt8.ofNat n) else none
  | _ => none

/-- Read an array of byte-sized integer literals. -/
def readBytes : Expr → Option Bytes
  | .arr xs => xs.mapM readByte
  | _ => none

/-- Read canonical natural digits. A leading zero is a refusal, not normalization. -/
def readNat (e : Expr) : Option Nat := do
  let bs ← readBytes e
  if bs.head? = some 0 then none else some (natOfDigits bs)

/-- The float constructor stores precisely one 64-bit pattern. -/
def readBits (e : Expr) : Option UInt64 := do
  let n ← readNat e
  if n < 2 ^ 64 then some (UInt64.ofNat n) else none

mutual
  /-- Recognize the structural value image. Other target syntax is refused. -/
  def readValue (e : Expr) : Option Val :=
    match e with
    | .arr [.int 9] => some .unit
    | .arr [.int 1, .bool b] => some (.bool b)
    | .arr [.int 2, n] => (readNat n).map Val.nat
    | .arr [.int 3, .str s] => some (.str s)
    | .arr [.int 8, bs] => (readBytes bs).map Val.bytes
    | .arr [.int 4, .arr xs] => (readValues xs).map Val.list
    | .arr [.int 5, a, b] => do
      let a' ← readValue a
      let b' ← readValue b
      some (.pair a' b')
    | .arr [.int 6] => some .none
    | .arr [.int 7, a] => (readValue a).map Val.some
    | .arr [.int 10, i, .arr xs] => do
      let i' ← readNat i
      let xs' ← readValues xs
      some (.ctor i' xs')
    | .arr [.int 11, k, bs] => do
      let k' ← readByte k
      let bs' ← readBytes bs
      some (.ref k' bs')
    | .arr [.int 12, k, n] => do
      let k' ← readByte k
      let n' ← readNat n
      some (.handle k' n')
    | .arr [.int 13, n] => (readNat n).map Val.negInt
    | .arr [.int 14, n] => (readBits n).map Val.float
    | _ => none
  termination_by structural e

  /-- Read recursive values in their written order. -/
  def readValues (es : List Expr) : Option (List Val) :=
    match es with
    | [] => some []
    | e :: es => do
      let v ← readValue e
      let vs ← readValues es
      some (v :: vs)
  termination_by structural es
end

/-- Retain the complete raw declaration, without type normalization. -/
def writeTy (t : Effect4.Program.Ty) : Expr := writeValue (Canonical.toVal t)

/-- Read only the exact canonical value image of the existing type language. -/
def readTy (e : Expr) : Option Effect4.Program.Ty :=
  (readValue e).bind Canonical.ofVal

end Effect4.Codegen.Metadata
