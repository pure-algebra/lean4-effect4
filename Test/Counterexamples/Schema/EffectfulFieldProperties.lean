import Effect4.Schema.EffectfulField

/-!
Retained attacks for
`test/contracts/schema-effectful-field-properties.contract.md`.
-/

namespace Test.Counterexamples.Schema.EffectfulFieldProperties

open Effect4

private def specA : EffectfulFieldSpec := ⟨⟨7⟩, ⟨11⟩, ⟨12⟩⟩
private def specB : EffectfulFieldSpec := ⟨⟨7⟩, ⟨21⟩, ⟨22⟩⟩
private def specC : EffectfulFieldSpec := ⟨⟨7⟩, ⟨31⟩, ⟨32⟩⟩

private def bag (spec : EffectfulFieldSpec) : Annotations :=
  EffectfulFieldSpec.annotationKey.singleton spec

private def markedProperty (name : String) (type : Representation)
    (spec : EffectfulFieldSpec) : PropertySignature :=
  { name := .string name
    type
    isOptional := false
    isMutable := true
    annotations := bag spec }

private def plainProperty (name : String) (type : Representation) : PropertySignature :=
  { name := .string name
    type
    isOptional := false
    isMutable := false
    annotations := none }

private def oneProperty (name : String) (spec : EffectfulFieldSpec) : Representation :=
  .objects none [] [markedProperty name (.never none []) spec] []

/-! `E4-SCHEMA-CE-053`: node metadata is not key-local property metadata. -/

private def nodeOnly : Representation :=
  .objects (bag specA) [] [plainProperty "plain" (.string none [])] []

private def propertyOnly : Representation :=
  .objects none [] [markedProperty "marked" (.string none []) specA] []

#guard Representation.effectfulFieldProperties nodeOnly = []
#guard (Representation.effectfulFieldProperties propertyOnly).map
    (fun discovered => discovered.1.name) = [PropertyKey.string "marked"]

/-! `E4-SCHEMA-CE-054`: every hidden recursive route belongs to discovery.
The two duplicate-name properties also retain distinct specs for CE-055. -/

private def outer : PropertySignature :=
  markedProperty "outer" (oneProperty "inner" specB) specA

private def duplicateB : PropertySignature :=
  markedProperty "duplicate" (.never none []) specB

private def duplicateC : PropertySignature :=
  markedProperty "duplicate" (.never none []) specC

private def recursiveWitness : Representation :=
  .declaration ⟨"root", .null⟩ none
    [ .objects none [] [outer, duplicateB, duplicateC]
        [{ parameter := oneProperty "index-parameter" specA
           type := oneProperty "index-type" specB }]
    , .arrays none []
        [{ isOptional := false
           type := oneProperty "element" specA
           annotations := none }]
        [oneProperty "rest" specB]
    , .templateLiteral none [] [oneProperty "template" specC]
    , .union none [] [oneProperty "union" specA] .anyOf
    , .suspend none [] (oneProperty "thunk" specB)
    ]
    [ .filter
        { id := "filter"
          payload := .null
          schemas := some [oneProperty "filter-schema" specC] }
        none false
    , .filterGroup
        (some
          { id := "group"
            payload := .null
            schemas := some [oneProperty "group-schema" specA] })
        none
        [.filter
          { id := "nested-filter"
            payload := .null
            schemas := some [oneProperty "group-check" specB] }
          none false]
    ]

private def summary (representation : Representation) :
    List (PropertyKey × Nat) :=
  (Representation.effectfulFieldProperties representation).map fun discovered =>
    (discovered.1.name, discovered.2.readOperation.value)

#guard summary recursiveWitness =
  [ (PropertyKey.string "outer", 11)
  , (PropertyKey.string "inner", 21)
  , (PropertyKey.string "duplicate", 21)
  , (PropertyKey.string "duplicate", 31)
  , (PropertyKey.string "index-parameter", 11)
  , (PropertyKey.string "index-type", 21)
  , (PropertyKey.string "element", 11)
  , (PropertyKey.string "rest", 21)
  , (PropertyKey.string "template", 31)
  , (PropertyKey.string "union", 11)
  , (PropertyKey.string "thunk", 21)
  , (PropertyKey.string "filter-schema", 31)
  , (PropertyKey.string "group-schema", 11)
  , (PropertyKey.string "group-check", 21)
  ]

private def shallow : Representation -> List (PropertySignature × EffectfulFieldSpec)
  | .objects _ _ properties _ => properties.filterMap fun property =>
      property.effectfulFieldSpec.map fun spec => (property, spec)
  | _ => []

/-- The shallow reading finds nothing: the witness carries no effectful field
directly on `recursiveWitness` itself. -/
theorem shallow_recursiveWitness : shallow recursiveWitness = [] := by rfl

/-- The recursive reading does. This was an `example` closed by `native_decide`
until the axiom gate learned to read the source: an `example` leaves no
constant, so neither the gate's declaration pass nor `#print axioms` ever saw
that it reached `Lean.ofReduceBool`. It is a named theorem closed in the kernel
now, and the `#guard` below pins the two occurrences it finds. -/
theorem recursiveWitness_effectfulFieldProperties_ne_nil :
    Representation.effectfulFieldProperties recursiveWitness != [] := by decide

/-! `E4-SCHEMA-CE-055`: duplicates are occurrences, not map entries. -/

#guard ((Representation.effectfulFieldProperties recursiveWitness).filter
    (fun discovered => discovered.1.name == PropertyKey.string "duplicate")).map
      (fun discovered => discovered.2.readOperation.value) = [21, 31]

end Test.Counterexamples.Schema.EffectfulFieldProperties
