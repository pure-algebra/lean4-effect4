/-! ## Acceptance: the meta-schema is a stored carrier

Appended verbatim by `--append`; not generated. There is no hand oracle for this group — that
is why it is the lane's real deliverable — so the guards are the laws made executable on real
values: the `Document` that `Cas/Shape.lean` derives for the census entry, and the `Document`
of `Document` itself, which is the meta-schema. A carrier that round-trips its own spec is the
fixed point the plan's §4 asks for. -/

namespace SchemaAcceptance

open Effect4 (Representation Check Document MultiDocument ReferenceEntry Annotations
  AnnotationEntry LiteralValue EnumValue EnumEntry PropertyKey UnionMode ReferenceKey
  GlobalSymbolKey RepresentationAnnotation Json)

/-- The spec of the census entry, derived by `Cas/Shape.lean` from `entryDoc`: a real
`Document` with a struct root, a named sum reference and `identifier` annotations. -/
def entrySpec : Document := entryDoc.document

/-- The meta-schema: the spec of the carrier `Document`, read off the generated shape. -/
def metaSchema : Document := Canonical.document Document

/-- A representation touching the awkward corners: an empty `$ref`, a bigint literal, a
non-finite number literal, a nested filter group with a `schemas` list, an index signature. -/
def corner : Representation :=
  .objects (some [⟨"title", .str "corner"⟩])
    [ .filterGroup (some ⟨"g", .null, some [.never none [], .any none []]⟩) none
        [.filter ⟨"f", .bool true, none⟩ (some []) false] ]
    [ ⟨.string "a", .literal none [] (.bigint (-7)), true, false, none⟩
    , ⟨.number ⟨18442240474082181120⟩, .reference ⟨""⟩, false, true, some []⟩
    , ⟨.globalSymbol ⟨"s"⟩, .enum none [] [⟨"x", .string "x"⟩, ⟨"y", .number ⟨3⟩⟩], false, false,
        none⟩ ]
    [ ⟨.string none [], .union none [] [.null none [], .undefined none []] .oneOf⟩ ]

def documents : List Document :=
  [ entrySpec
  , metaSchema
  , ⟨.never none [], []⟩
  , ⟨corner, [⟨"corner", corner⟩, ⟨"", .suspend none [] (.reference ⟨"corner"⟩)⟩]⟩
  , ⟨.arrays none [] [⟨true, .string none [], none⟩] [.unknown none []],
     [⟨"dup", .void none []⟩, ⟨"dup", .void none []⟩]⟩ ]

-- Every law of the class, made executable on those documents.
#guard documents.all fun d => Canonical.decode (α := Document) (Canonical.encode d) = some d
#guard documents.all fun d => (Canonical.shape Document).accepts (Canonical.toVal d)
#guard documents.all fun d =>
  Canonical.decode (α := Document) (Canonical.encode d ++ [0]) = none
#guard documents.all fun d =>
  Canonical.decode (α := Document) (Canonical.encode d).dropLast = none

-- The meta-schema is a fixed point: the spec of `Document` is itself a stored `Document`.
#guard Canonical.decode (α := Document) (Canonical.encode metaSchema) = some metaSchema
#guard (Canonical.shape Document).accepts (Canonical.toVal metaSchema)
#guard !metaSchema.references.isEmpty
#guard (Canonical.digest metaSchema).hex.length = 64
#guard (Canonical.digest metaSchema).hex ≠ (Canonical.digest entrySpec).hex

-- The block's other carriers, on the same corner value.
#guard Canonical.decode (α := Representation) (Canonical.encode corner) = some corner
#guard (Canonical.shape Representation).accepts (Canonical.toVal corner)
#guard Canonical.decode (α := Check) (Canonical.encode (Check.filterGroup none none [])) =
  some (Check.filterGroup none none [])
#guard Canonical.decode (α := MultiDocument) (Canonical.encode entrySpec.toMulti) =
  some entrySpec.toMulti

-- The leaf carriers, constructor by constructor.
#guard [LiteralValue.string "s", .number ⟨3⟩, .bigint (-1), .boolean true].all fun l =>
  Canonical.decode (α := LiteralValue) (Canonical.encode l) = some l
#guard [EnumValue.string "s", .number ⟨0⟩].all fun v =>
  Canonical.decode (α := EnumValue) (Canonical.encode v) = some v
#guard [PropertyKey.string "k", .number ⟨1⟩, .globalSymbol ⟨"g"⟩].all fun k =>
  Canonical.decode (α := PropertyKey) (Canonical.encode k) = some k
#guard [UnionMode.anyOf, .oneOf].all fun m =>
  Canonical.decode (α := UnionMode) (Canonical.encode m) = some m
#guard Canonical.decode (α := Annotations) (Canonical.encode (none : Annotations)) = some none
#guard Canonical.decode (α := Annotations)
  (Canonical.encode (some [⟨"k", Json.null⟩] : Annotations)) = some (some [⟨"k", Json.null⟩])
-- Absence and a present empty bag stay distinct in the bytes (`Payload.lean:38`).
#guard Canonical.encode (none : Annotations) ≠ Canonical.encode (some [] : Annotations)

-- A `ReferenceKey` is a struct around a string, so its frame is the string's under one `ctor`.
#guard Canonical.encode (ReferenceKey.mk "A") =
  [10, 0, 0, 0, 0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 65]

end SchemaAcceptance
