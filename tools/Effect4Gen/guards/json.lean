/-! ## Acceptance: the laws made executable

Appended verbatim by `--append`; not generated. The spike's hand instances (`workshop/Cas`,
lane S1's `JsonCanonical` and `Float64Canonical`) agreed with these tree for tree on every
sample below and retired at the landing (`REPORT-G.md`, decision 1), so no oracle is called
here: the guards are the three laws run on real values through the generated readers, spelled
without the class so that no other instance in scope can answer for them, the reader's
refusals, and the primitive frames of `Test/Store/StoreContract.lean:39-47` restated on the
generated image. -/

namespace JsonAcceptance

open Effect4 (Json Float64)

/-- A sample touching every constructor, and the degenerate values around it. -/
def samples : List Json :=
  [ .obj [("a", .arr [.null, .bool true, .number ⟨3⟩, .str "x"]), ("b", .obj [])]
  , .null, .bool true, .bool false, .number ⟨0⟩, .number ⟨4614256656552045848⟩, .str "", .str "é"
  , .arr [], .obj []
  , .arr [.arr [.obj [("k", .null), ("k", .bool false)]]]
  , .obj [("", .arr [.number ⟨1⟩, .str "\"\\"]), ("nested", .obj [("deep", .arr [.null])])] ]

def floats : List Float64 := [⟨0⟩, ⟨3⟩, ⟨1⟩, ⟨18446744073709551615⟩, ⟨4614256656552045848⟩]

-- Every image reads back, through the generated readers and through the bytes.
#guard samples.all fun j =>
  guarded JsonGen.JsonC.toValJson JsonGen.JsonC.rawJson (JsonGen.JsonC.toValJson j) = some j
#guard floats.all fun f => JsonGen.Float64C.ofVal (JsonGen.Float64C.toVal f) = some f
#guard samples.all fun j => Canonical.decode (α := Json) (Canonical.encode j) = some j
#guard floats.all fun f => Canonical.decode (α := Float64) (Canonical.encode f) = some f

-- A byte appended or dropped is refused.
#guard samples.all fun j => Canonical.decode (α := Json) (Canonical.encode j ++ [0]) = none
#guard samples.all fun j => Canonical.decode (α := Json) (Canonical.encode j).dropLast = none

-- Every image fits the generated shape.
#guard samples.all fun j => (Canonical.shape Json).accepts (Canonical.toVal j)
#guard floats.all fun f => (Canonical.shape Float64).accepts (Canonical.toVal f)

-- The primitive frames of `Test/Store/StoreContract.lean:39-47`, restated on the generated
-- image: a `Json` string is a `ctor 3` around the string frame, `null` is `ctor 0` with no
-- arguments, a `Float64` is `ctor 0` around its bits as a `nat`.
#guard Val.encode (JsonGen.JsonC.toValJson (.str "A")) =
  [10, 0, 0, 0, 0, 0, 0, 0, 20, 2, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
#guard Val.encode (JsonGen.JsonC.toValJson .null) =
  [10, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard Val.encode (JsonGen.Float64C.toVal ⟨3⟩) =
  [10, 0, 0, 0, 0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 3]

end JsonAcceptance
