/-! ## Acceptance against the hand oracle

Appended verbatim by `--append`; not generated. The oracle is `Cas/Templates.lean`'s hand
`Float64Canonical` and `JsonCanonical`, which lane S1 proved and guarded. Agreement of the two
`toVal`s is agreement of the bytes, the digest and the address, because `Canonical.encode` is
`Val.encode ∘ toVal` and nothing else reads the carrier. -/

namespace JsonAcceptance

open Effect4 (Json Float64)

/-- The hand template's sample, touching every constructor (`Templates.lean:630-631`), and the
degenerate values around it. -/
def samples : List Json :=
  [ .obj [("a", .arr [.null, .bool true, .number ⟨3⟩, .str "x"]), ("b", .obj [])]
  , .null, .bool true, .bool false, .number ⟨0⟩, .number ⟨4614256656552045848⟩, .str "", .str "é"
  , .arr [], .obj []
  , .arr [.arr [.obj [("k", .null), ("k", .bool false)]]]
  , .obj [("", .arr [.number ⟨1⟩, .str "\"\\"]), ("nested", .obj [("deep", .arr [.null])])] ]

def floats : List Float64 := [⟨0⟩, ⟨3⟩, ⟨1⟩, ⟨18446744073709551615⟩, ⟨4614256656552045848⟩]

-- The generated image is the hand image, tree for tree, hence byte for byte.
#guard floats.all fun f => JsonGen.Float64C.toVal f = Float64Canonical.toVal f
#guard samples.all fun j => JsonGen.JsonC.toValJson j = JsonCanonical.toVal j
#guard samples.all fun j =>
  Val.encode (JsonGen.JsonC.toValJson j) = Val.encode (JsonCanonical.toVal j)
#guard samples.all fun j =>
  (sha256 (Val.encode (JsonGen.JsonC.toValJson j))).hex =
    (sha256 (Val.encode (JsonCanonical.toVal j))).hex

-- The generated reader agrees with the hand reader on the images and on a corrupted frame.
#guard samples.all fun j =>
  guarded JsonGen.JsonC.toValJson JsonGen.JsonC.rawJson (JsonGen.JsonC.toValJson j) =
    JsonCanonical.ofVal (JsonCanonical.toVal j)
#guard samples.all fun j =>
  (Val.decode (Val.encode (JsonGen.JsonC.toValJson j) ++ [0])).isNone
#guard samples.all fun j =>
  (Val.decode (Val.encode (JsonGen.JsonC.toValJson j)).dropLast).isNone

-- The generated shape is the hand shape's twin: it accepts every image and the same documents.
#guard samples.all fun j =>
  (ShapeDoc.mk (.named "Json") JsonGen.JsonC.defs).accepts (JsonGen.JsonC.toValJson j)
#guard samples.all fun j => JsonCanonical.shapeDoc.accepts (JsonGen.JsonC.toValJson j)
#guard floats.all fun f => JsonGen.Float64C.shapeDoc.accepts (JsonGen.Float64C.toVal f)
#guard (ShapeDoc.mk (.named "Json") JsonGen.JsonC.defs).document.references.length =
  JsonCanonical.shapeDoc.document.references.length

-- The primitive frames of `Test/Store/StoreContract.lean:39-47`, restated on the generated
-- image: a `Json` string is a `ctor 3` around the string frame, unchanged.
#guard Val.encode (JsonGen.JsonC.toValJson (.str "A")) =
  [10, 0, 0, 0, 0, 0, 0, 0, 20, 2, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
#guard Val.encode (JsonGen.JsonC.toValJson .null) =
  [10, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0]

end JsonAcceptance
