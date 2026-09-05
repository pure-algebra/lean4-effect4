import Effect4.Data.Json

/-!
# Data.JsonNumber

Owner: a JSON number from a natural — the binary64 datum the host would parse — built from
the number's bits alone, so it reaches no `Float` primitive and no axiom.

`highestBit`, `binary64OfNat` and `Json.ofNat` are `Store/JsonCanonical.lean:61-81` moved
verbatim when that module retired with the JSON tag alphabet (the CAS trait,
`docs/research/2026-09-04-cas-trait-plan.md` §6): the helpers were never part of the address,
only of the printers, and the printers outlive the alphabet. The namespace stays
`Effect4.Arch` because six modules address them as `Arch.Json.ofNat` and `Arch.binary64OfNat`
(`Surface/Entity.lean:532`, `Surface/Api.lean:1855`, `Surface/Deploy.lean:520`,
`Codegen/JsonSchema.lean:428-601`, `Ingest/JsonSchema.lean:280`, `Evidence/Views.lean`,
`Evidence/StdLib/Entry.lean:68`), and the store's own printer (`Store/Shape.lean`) reads them
the same way. The law that is not here: `binary64OfNat` is exact below 2^53 and truncates
toward zero above it, so it is not injective on `Nat` (`Surface/Annotate.lean:58`); its
inverse and that theorem are owed (`Schema/Dimension.lean:21`).
-/

set_option autoImplicit false

namespace Effect4.Arch

/-- The index of the highest set bit, with the number as its own fuel. -/
def highestBit (n : Nat) : Nat :=
  go n n 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | fuel + 1, m, acc => if m < 2 then acc else go fuel (m / 2) (acc + 1)

/-- The binary64 bit pattern of a natural, exact below 2^53 and truncated
toward zero above it: sign 0, biased exponent `1023 + e` where `e` is the
highest bit, and the 52 bits after it as the significand. Built from the
number's bits alone, so it reaches no `Float` primitive and no axiom. -/
def binary64OfNat (n : Nat) : UInt64 :=
  if n = 0 then 0
  else
    let e := highestBit n
    let significand := if e ≤ 52 then (n <<< (52 - e)) - (1 <<< 52) else (n >>> (e - 52)) - (1 <<< 52)
    UInt64.ofNat (((1023 + e) <<< 52) + significand)

/-- A JSON number from a natural: the binary64 the host would parse. -/
def Json.ofNat (n : Nat) : Json := .number ⟨binary64OfNat n⟩

-- The two exact anchors and the first truncation: `2^53` is the last exact integer, `2^53 + 1`
-- rounds down to it.
#guard binary64OfNat 0 = 0
#guard binary64OfNat 1 = 0x3FF0000000000000
#guard binary64OfNat 1947 = 0x409E6C0000000000
#guard binary64OfNat (2 ^ 53 + 1) = binary64OfNat (2 ^ 53)

/-! ## Receipts -/

#print axioms highestBit
#print axioms binary64OfNat
#print axioms Json.ofNat

end Effect4.Arch
