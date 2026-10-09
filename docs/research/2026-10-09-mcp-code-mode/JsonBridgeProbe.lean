import Tools.JsonBridge

/-!
# Probe MCP-2 (finite): the JSON profile at the tool's bridge

Seat MCP, 2026-10-09. Evidence for finding F1 of `docs/research/2026-10-09-mcp-code-mode-design.md`.
Not part of the tree. Run it with:

    scratch/lean-slot.sh lake env lean docs/research/2026-10-09-mcp-code-mode/JsonBridgeProbe.lean

`Tools.JsonBridge.ofLeanJson` (`tools/Tools/JsonBridge.lean`) admits a JSON integer when
`natOfBinary64 (binary64OfNat n) = some n`. Above `2^1024`, `binary64OfNat` leaves the finite
range: `2^1024` gets the bit pattern of `+Infinity`, and `2^2048` the bit pattern of `-1.0`. The
round trip still holds inside Lean, so the bridge admits both and gives each back. A host that
reads the tree's JSON datum as binary64 reads a different number. Every result below is a finite
evaluation.
-/

open Effect4 Effect4.Store

/-- The datum the bridge makes of a natural written as a JSON integer, if it admits it. -/
def datumOf (n : Nat) : Option UInt64 :=
  match Tools.JsonBridge.ofLeanJson 4 (Lean.Json.num (Lean.JsonNumber.fromNat n)) with
  | some (.number x) => some x.bits
  | _ => none

-- 2^53 + 1: refused, as the JSON-01 repair requires (binary64 rounds it)
#eval datumOf (2 ^ 53 + 1)
-- 2^53 + 2: admitted; binary64 holds it exactly
#eval datumOf (2 ^ 53 + 2) == some (Effect4.Arch.binary64OfNat (2 ^ 53 + 2))
-- 2^1024: admitted, and its datum is the bit pattern of +Infinity (0x7FF0000000000000)
#eval datumOf (2 ^ 1024) == some 0x7FF0000000000000
-- 2^2048: admitted, and its datum is the bit pattern of -1.0 (0xBFF0000000000000)
#eval datumOf (2 ^ 2048) == some 0xBFF0000000000000
-- and the bridge gives the natural back, so the round trip inside Lean holds
#eval (Tools.JsonBridge.ofLeanJson 4 (Lean.Json.num (Lean.JsonNumber.fromNat (2 ^ 2048)))).map
  (fun j => Tools.JsonBridge.toLeanJson j == Lean.Json.num (Lean.JsonNumber.fromNat (2 ^ 2048)))
-- the text -1 is refused at the bridge: its mantissa is negative
#eval (Tools.JsonBridge.ofLeanJson 4 (Lean.Json.num (-1 : Lean.JsonNumber))).isSome
