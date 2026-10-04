module

public import Effect4.Data.Ascii
public import Init.Data.Nat.ToString

/-! Canonical natural text for tuple indices, service keys and variable-name laws.
The byte fold is shared with the existing codegen decoder; it does not assign a nominal type.
Exact reconstruction laws live in `Laws/Data/NatDecimal.lean`. -/

@[expose] public section

namespace Effect4.Data.NatDecimal

/-- The natural digit represented by one byte. Canonical reading checks the full spelling. -/
def digitOfByte (b : UInt8) : Nat := b.toNat - 48

/-- Fold digit bytes into a natural number, without a Unicode string iterator. -/
def decodeBytes (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 10 + digitOfByte b) 0

/-- Read exactly one canonical decimal spelling, with no bound on the natural number. -/
def read (text : String) : Option Nat :=
  let n := decodeBytes text.toByteArray.data.toList
  if text = Nat.repr n then some n else none

end Effect4.Data.NatDecimal
