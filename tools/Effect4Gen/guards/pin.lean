/-! ## Acceptance: a pin as `source` content

Appended verbatim by `--append`; not generated. The laws of the class made executable on one
well-formed pin (its span digest recomputed from its own lines, as `Pin.isWellFormed` does),
the reader's refusals, the kind the `--kind` option filed the carrier under, and the frame of
a typed reference to a pin: forty-two bytes, `Tag.ref`, the `source` kind byte, the address. -/

namespace PinAcceptance

def lines : List String := ["const releaseCapacity = (self) => {", "}"]

/-- One pin, well-formed by construction: two lines, offsets `0..1`, the digest of the lines
joined by newlines with a trailing newline. -/
def sample : Pin :=
  { package := "effect", version := "4.0.0-rc.112", file := "src/Queue.ts",
    declaration := "releaseCapacity", role := .internal, anchor := "const releaseCapacity",
    offsetStart := 0, offsetEnd := 1,
    spanDigest := sha256 (lines.foldr (fun line acc => line.toUTF8.data.toList ++ (10 :: acc)) []),
    text := lines }

#guard sample.isWellFormed

-- The laws, run: the image reads back, through the class and through the bytes; a byte
-- appended or dropped is refused; the image fits the shape.
#guard PinGen.PinC.ofVal (PinGen.PinC.toVal sample) = some sample
#guard Canonical.decode (α := Pin) (Canonical.encode sample) = some sample
#guard Canonical.decode (α := Pin) (Canonical.encode sample ++ [0]) = none
#guard Canonical.decode (α := Pin) (Canonical.encode sample).dropLast = none
#guard (Canonical.shape Pin).accepts (Canonical.toVal sample)
#guard [PinRole.public, .internal].all fun r => PinGen.PinRoleC.ofVal (PinGen.PinRoleC.toVal r) = some r

-- The kind, and the spec's root: a struct.
#guard Content.kind Pin = .source
#guard (Canonical.document Pin).representation.tag = .objects

-- The printer follows the shape: keys in declaration order, the role as its constructor's
-- name, the digest as lowercase hex, the lines as an array.
#guard Canonical.print sample =
  .obj [ ("package", .str "effect"), ("version", .str "4.0.0-rc.112"), ("file", .str "src/Queue.ts")
       , ("declaration", .str "releaseCapacity"), ("role", .str "internal")
       , ("anchor", .str "const releaseCapacity"), ("offsetStart", Arch.Json.ofNat 0)
       , ("offsetEnd", Arch.Json.ofNat 1), ("spanDigest", .str sample.spanDigest.hex)
       , ("text", .arr (lines.map .str)) ]

-- A typed reference to a pin: `Tag.ref`, the `source` kind byte, thirty-two address bytes;
-- another kind byte or a short digest is refused before any store is consulted.
#guard (Canonical.encode (⟨sha256 []⟩ : Ref Pin)).length = 42
#guard (Canonical.encode (⟨sha256 []⟩ : Ref Pin)).take 10 = [11, 0, 0, 0, 0, 0, 0, 0, 33, 1]
#guard Canonical.decode (α := Ref Pin) (Canonical.encode (⟨sha256 []⟩ : Ref Pin)) =
  some (⟨sha256 []⟩ : Ref Pin)
#guard Canonical.decode (α := Ref Pin) (Val.encode (.ref 2 (sha256 []).bytes)) = none
#guard Canonical.decode (α := Ref Pin) (Val.encode (.ref 1 (List.replicate 31 0))) = none

end PinAcceptance
