/-
Contract packet: `Test/contracts/schema-payload.contract.md`

Breaker-owned red battery for the Schema representation PAYLOAD carrier — the
recursive first-order tree that hangs off the frozen 22-tag census. The
implementation phase must not edit this file. It is red until the payload
declarations exist, and every pre-implementation failure must be a
`lean.unknownIdentifier` diagnostic naming a frozen declaration.

Targets `SC-REP-01` (declaration half), `SC-REP-04` (clause half), and the
payload half of `SC-REP-03` (structural equality). It makes no denotation,
reference-graph, guardedness, wire, codec, getter, registry, or diagnostic
claim, and discharges none of `E4-SCHEMA-CE-001` .. `-016`.

Every theorem is ascribed at its exact proposition and supplied by name, so a
weaker statement under the same name does not satisfy this battery. Names are
applied with `@` so that binder explicitness is not accidentally frozen.
-/

import Effect4.Schema.Representation
import Effect4.Schema.Document
import Effect4.Schema.Check

set_option autoImplicit false

namespace Test.Schema.PayloadContract

open Effect4

/-! ## D2-D3 import ownership receipt input

The future declaration-surface gate must materialize these lines as a fresh
Lean module. Its only import is `Effect4.Schema.Payload`: D0-D3 must resolve
through that boundary, while D4-D7 must not leak upward into it. Keeping the
probe as packet data freezes the receipt before the boundary exists; this
battery itself does not import the not-yet-admitted module. -/

def payloadBoundaryImportProbe : List String :=
  [ "import Effect4.Schema.Payload"
  , "set_option autoImplicit false"
  , "#check Effect4.Float64"
  , "#check Effect4.Json"
  , "#check Effect4.ReferenceKey"
  , "#check Effect4.GlobalSymbolKey"
  , "#check Effect4.AnnotationEntry"
  , "#check Effect4.Annotations"
  , "#check Effect4.LiteralValue"
  , "#check Effect4.EnumValue"
  , "#check Effect4.EnumEntry"
  , "#check Effect4.PropertyKey"
  , "#check Effect4.RepresentationAnnotation"
  , "#check Effect4.CheckRepresentationAnnotationOf"
  , "#check Effect4.ElementOf"
  , "#check Effect4.PropertySignatureOf"
  , "#check Effect4.IndexSignatureOf"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Representation)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Check)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Document)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.MultiDocument)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Annotations.FieldAdmissible)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Representation.FieldAdmissible)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Check.FieldAdmissible)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.Document.FieldAdmissible)"
  , "/-- error: Unknown -/"
  , "#guard_msgs(error, substring := true) in #check (@Effect4.MultiDocument.FieldAdmissible)" ]

/-- Expected declaration-owner rows for the future environment inspection.
The gate must compare module ownership, not merely observe that imports happen
to make these names reachable. -/
def payloadBoundaryExpectedOwners : List (String × String) :=
  [ ("Effect4.Float64", "Effect4.Data.Json")
  , ("Effect4.Json", "Effect4.Data.Json")
  , ("Effect4.ReferenceKey", "Effect4.Schema.Payload")
  , ("Effect4.GlobalSymbolKey", "Effect4.Schema.Payload")
  , ("Effect4.AnnotationEntry", "Effect4.Schema.Payload")
  , ("Effect4.Annotations", "Effect4.Schema.Payload")
  , ("Effect4.LiteralValue", "Effect4.Schema.Payload")
  , ("Effect4.EnumValue", "Effect4.Schema.Payload")
  , ("Effect4.EnumEntry", "Effect4.Schema.Payload")
  , ("Effect4.PropertyKey", "Effect4.Schema.Payload")
  , ("Effect4.RepresentationAnnotation", "Effect4.Schema.Payload")
  , ("Effect4.CheckRepresentationAnnotationOf", "Effect4.Schema.Payload")
  , ("Effect4.ElementOf", "Effect4.Schema.Payload")
  , ("Effect4.PropertySignatureOf", "Effect4.Schema.Payload")
  , ("Effect4.IndexSignatureOf", "Effect4.Schema.Payload") ]

/-- `Effect4.Schema.Payload` may import Data.Json but none of its upward
consumers. The surface gate must reject each named upward edge. -/
def payloadBoundaryForbiddenImports : List String :=
  [ "Effect4.Schema.Representation"
  , "Effect4.Schema.Document"
  , "Effect4.Schema.Check"
  , "Effect4.Schema.Value" ]

/-! ## D0 — the binary64 payload datum

Lean's `Float` cannot be this carrier: it has no `DecidableEq`, and its `BEq`
is IEEE equality, under which `nan == nan` is `false` and `0.0 == -0.0` is
`true`. `SC-REP-03`'s payload half claims decidable *structural* equality on
the Lean carrier and explicitly not the host's `===`; see the contract's
answer (b). -/

section BinaryFloat

example : Type := Float64

example : DecidableEq Float64 := inferInstance

example : Float64 → UInt64 := Float64.toBits
example : UInt64 → Float64 := Float64.ofBits

/-- `Float64` is the complete binary64 bit-pattern carrier, not an enumeration
of the five distinguished values used elsewhere in this packet. These two
laws make `toBits` and `ofBits` inverse in both directions. -/
example : ∀ bits : UInt64, Float64.toBits (Float64.ofBits bits) = bits :=
  @Float64.toBits_ofBits

example : ∀ value : Float64, Float64.ofBits (Float64.toBits value) = value :=
  @Float64.ofBits_toBits

example : Float64 → Bool := Float64.isFinite

example : Float64 := Float64.nan
example : Float64 := Float64.posInfinity
example : Float64 := Float64.negInfinity
example : Float64 := Float64.zero
example : Float64 := Float64.negZero

/-- The five distinguished constants have exact binary64 spellings. The NaN
constant is the canonical positive quiet NaN chosen by this packet; the
carrier still contains every other NaN payload through `ofBits`. -/
example : Float64.toBits Float64.nan = (0x7ff8000000000000 : UInt64) :=
  @Float64.toBits_nan
example : Float64.toBits Float64.posInfinity = (0x7ff0000000000000 : UInt64) :=
  @Float64.toBits_posInfinity
example : Float64.toBits Float64.negInfinity = (0xfff0000000000000 : UInt64) :=
  @Float64.toBits_negInfinity
example : Float64.toBits Float64.zero = (0x0000000000000000 : UInt64) :=
  @Float64.toBits_zero
example : Float64.toBits Float64.negZero = (0x8000000000000000 : UInt64) :=
  @Float64.toBits_negZero

example : Float64.isFinite Float64.nan = false := @Float64.isFinite_nan
example : Float64.isFinite Float64.posInfinity = false := @Float64.isFinite_posInfinity
example : Float64.isFinite Float64.negInfinity = false := @Float64.isFinite_negInfinity
example : Float64.isFinite Float64.zero = true := @Float64.isFinite_zero
example : Float64.isFinite Float64.negZero = true := @Float64.isFinite_negZero

/-- The named examples do not characterize the other `2^64 - 5` bit
patterns. These two equations freeze the format rule for every datum: the
eleven-bit exponent field is all ones exactly for the non-finite values. -/
example : ∀ bits : UInt64,
    Float64.isFinite (Float64.ofBits bits) = true ↔
      bits.toNat / 0x10000000000000 % 0x800 ≠ 0x7ff :=
  @Float64.isFinite_ofBits_iff

example : ∀ bits : UInt64,
    Float64.isFinite (Float64.ofBits bits) = false ↔
      bits.toNat / 0x10000000000000 % 0x800 = 0x7ff :=
  @Float64.not_isFinite_ofBits_iff

/-- The equality ruling, made observable: a carrier that normalises signed zero
at construction fails here. `E4-SCHEMA-CE-041`. -/
example : Float64.negZero ≠ Float64.zero := @Float64.negZero_ne_zero

end BinaryFloat

/-! ## D1 — JSON

`Schema.Json = null | number | boolean | string | JsonArray | JsonObject`.
Object entries are an ordered `List`, never a map: raw JSON must preserve
ordered duplicate keys until the profile rejects them, which also rules out
reusing `Lean.Json`.

`Json.null` is a third member of the confusion family `E4-SCHEMA-CE-021`
opened: the `Null` representation tag, the absent `LiteralKind.null`, and this
constructor are three different things. -/

section JsonCarrier

example : Type := Json

example : DecidableEq Json := inferInstance

example : Json := Json.null
example : Bool → Json := Json.bool
example : Float64 → Json := Json.number
example : String → Json := Json.str
example : List Json → Json := Json.arr
example : List (String × Json) → Json := Json.obj

/-! `isJsonLeaf` requires `Number.isFinite`, so a non-finite number is not a
JSON value at the pin. This predicate is that requirement. -/

example : Json → Prop := Json.NumbersFinite
example : Json → Bool := Json.numbersFinite

example : ∀ value : Json, Json.numbersFinite value = true ↔ Json.NumbersFinite value :=
  @Json.numbersFinite_iff

/-- `NumbersFinite` is fixed compositionally on every JSON constructor. -/
example : Json.NumbersFinite Json.null := @Json.numbersFinite_null
example : ∀ value : Bool, Json.NumbersFinite (Json.bool value) :=
  @Json.numbersFinite_bool
example : ∀ value : String, Json.NumbersFinite (Json.str value) :=
  @Json.numbersFinite_str
example : ∀ value : Float64,
    Json.NumbersFinite (Json.number value) ↔ Float64.isFinite value = true :=
  @Json.numbersFinite_number_iff
example : ∀ values : List Json,
    Json.NumbersFinite (Json.arr values) ↔
      ∀ value ∈ values, Json.NumbersFinite value :=
  @Json.numbersFinite_arr_iff
example : ∀ entries : List (String × Json),
    Json.NumbersFinite (Json.obj entries) ↔
      ∀ entry ∈ entries, Json.NumbersFinite entry.2 :=
  @Json.numbersFinite_obj_iff

example : ¬ Json.NumbersFinite (Json.number Float64.nan) := @Json.not_numbersFinite_nan
example : Json.NumbersFinite (Json.number Float64.zero) := @Json.numbersFinite_zero

/-- Nested witnesses stop an implementation from checking only the immediate
number or only one of the array/object routes. -/
example : Json.NumbersFinite
    (Json.obj
      [("outer", Json.arr
        [Json.number Float64.zero,
         Json.obj [("leaf", Json.bool true)]])]) :=
  @Json.numbersFinite_nested

example : ¬ Json.NumbersFinite
    (Json.arr [Json.obj [("bad", Json.number Float64.nan)]]) :=
  @Json.not_numbersFinite_nested_nan

/-- The constructor cap for the recursive JSON carrier. -/
example : ∀ value : Json,
    value = Json.null ∨
    (∃ b : Bool, value = Json.bool b) ∨
    (∃ n : Float64, value = Json.number n) ∨
    (∃ s : String, value = Json.str s) ∨
    (∃ values : List Json, value = Json.arr values) ∨
    (∃ entries : List (String × Json), value = Json.obj entries) :=
  @Json.cases_census

end JsonCarrier

/-! ## D2 — scalars, keys, entries -/

section Scalars

example : Type := ReferenceKey
example : DecidableEq ReferenceKey := inferInstance
example : ReferenceKey → String := ReferenceKey.value

example : Type := GlobalSymbolKey
example : DecidableEq GlobalSymbolKey := inferInstance
example : GlobalSymbolKey → String := GlobalSymbolKey.key

example : Type := AnnotationEntry
example : DecidableEq AnnotationEntry := inferInstance
example : AnnotationEntry → String := AnnotationEntry.key
example : AnnotationEntry → Json := AnnotationEntry.payload

/-- Absent and empty are distinct raw states: `pruneAnnotations` maps an
all-pruned record to an omitted key while decode passes `{}` through
unchanged, so a carrier that cannot hold both leaves `SC-WIRE-04` nothing to
normalise. `E4-SCHEMA-CE-036`. -/
example : Annotations = Option (List AnnotationEntry) := rfl

example : Type := LiteralValue
example : DecidableEq LiteralValue := inferInstance
example : String → LiteralValue := LiteralValue.string
example : Float64 → LiteralValue := LiteralValue.number
example : Int → LiteralValue := LiteralValue.bigint
example : Bool → LiteralValue := LiteralValue.boolean

example : Type := EnumValue
example : DecidableEq EnumValue := inferInstance
example : String → EnumValue := EnumValue.string
example : Float64 → EnumValue := EnumValue.number

example : Type := EnumEntry
example : DecidableEq EnumEntry := inferInstance
example : EnumEntry → String := EnumEntry.name
example : EnumEntry → EnumValue := EnumEntry.value

example : Type := PropertyKey
example : DecidableEq PropertyKey := inferInstance
example : String → PropertyKey := PropertyKey.string
example : Float64 → PropertyKey := PropertyKey.number
example : GlobalSymbolKey → PropertyKey := PropertyKey.globalSymbol

/-! The kind projections are the anti-drift law between the payload values and
the already-frozen closed sub-alphabets. Surjectivity is what stops either
layer gaining or losing a row unnoticed. -/

example : LiteralValue → LiteralKind := LiteralValue.kind
example : EnumValue → EnumValueKind := EnumValue.kind
example : PropertyKey → PropertyKeyKind := PropertyKey.kind

example : ∀ kind : LiteralKind, ∃ value : LiteralValue, LiteralValue.kind value = kind :=
  @LiteralValue.kind_surjective
example : ∀ kind : EnumValueKind, ∃ value : EnumValue, EnumValue.kind value = kind :=
  @EnumValue.kind_surjective
example : ∀ kind : PropertyKeyKind, ∃ key : PropertyKey, PropertyKey.kind key = kind :=
  @PropertyKey.kind_surjective

/-! Kind surjectivity does not cap the value carriers: an extra constructor
could reuse an existing kind. These exact eliminations close that hole. -/

example : ∀ value : LiteralValue,
    (∃ s : String, value = LiteralValue.string s) ∨
    (∃ n : Float64, value = LiteralValue.number n) ∨
    (∃ n : Int, value = LiteralValue.bigint n) ∨
    (∃ b : Bool, value = LiteralValue.boolean b) :=
  @LiteralValue.cases_census

example : ∀ value : EnumValue,
    (∃ s : String, value = EnumValue.string s) ∨
    (∃ n : Float64, value = EnumValue.number n) :=
  @EnumValue.cases_census

example : ∀ key : PropertyKey,
    (∃ s : String, key = PropertyKey.string s) ∨
    (∃ n : Float64, key = PropertyKey.number n) ∨
    (∃ s : GlobalSymbolKey, key = PropertyKey.globalSymbol s) :=
  @PropertyKey.cases_census

end Scalars

/-! ## The numeric domains, at the value layer

`E4-SCHEMA-CE-023` fired at the kind layer: `EnumValueKind.toLiteralKind` maps
kinds and says nothing about values. Its value-level companion is a total raw
embedding: non-finite binary64 data remains representable as a
`LiteralValue.number`. Whether that literal is field-admissible is a separate
D7 theorem. `E4-SCHEMA-CE-028`. -/

section NumericDomains

example : EnumValue → LiteralValue := EnumValue.toLiteralValue

example : ∀ value : String,
    EnumValue.toLiteralValue (EnumValue.string value) = LiteralValue.string value :=
  @EnumValue.toLiteralValue_string

example : ∀ value : Float64,
    EnumValue.toLiteralValue (EnumValue.number value) = LiteralValue.number value :=
  @EnumValue.toLiteralValue_number

example : Function.Injective EnumValue.toLiteralValue :=
  @EnumValue.toLiteralValue_injective

example : ∀ value : EnumValue,
    LiteralValue.kind (EnumValue.toLiteralValue value) =
      EnumValueKind.toLiteralKind (EnumValue.kind value) :=
  @EnumValue.toLiteralValue_kind

/-- Totality is observable at the previously problematic point: NaN is copied
as raw data. D7 separately proves that the resulting literal is not admitted. -/
example : EnumValue.toLiteralValue (EnumValue.number Float64.nan) =
    LiteralValue.number Float64.nan :=
  @EnumValue.toLiteralValue_number Float64.nan

end NumericDomains

/-! ## D3 — parameterized record children

Keeping these out of the mutual block is the main lever on recursor usability.
`IndexSignatureOf` has exactly two fields, and `RepresentationAnnotation` has
no `schemas` field; both exclusions are enforced by absence below. -/

section RecordChildren

example : Type := RepresentationAnnotation
example : DecidableEq RepresentationAnnotation := inferInstance
example : RepresentationAnnotation → String := RepresentationAnnotation.id
example : RepresentationAnnotation → Json := RepresentationAnnotation.payload

example : Type → Type := CheckRepresentationAnnotationOf
example : ∀ α : Type, CheckRepresentationAnnotationOf α → String :=
  @CheckRepresentationAnnotationOf.id
example : ∀ α : Type, CheckRepresentationAnnotationOf α → Json :=
  @CheckRepresentationAnnotationOf.payload
example : ∀ α : Type, CheckRepresentationAnnotationOf α → Option (List α) :=
  @CheckRepresentationAnnotationOf.schemas

example : Type → Type := ElementOf
example : ∀ α : Type, ElementOf α → Bool := @ElementOf.isOptional
example : ∀ α : Type, ElementOf α → α := @ElementOf.type
example : ∀ α : Type, ElementOf α → Annotations := @ElementOf.annotations

example : Type → Type := PropertySignatureOf
example : ∀ α : Type, PropertySignatureOf α → PropertyKey := @PropertySignatureOf.name
example : ∀ α : Type, PropertySignatureOf α → α := @PropertySignatureOf.type
example : ∀ α : Type, PropertySignatureOf α → Bool := @PropertySignatureOf.isOptional
example : ∀ α : Type, PropertySignatureOf α → Bool := @PropertySignatureOf.isMutable
example : ∀ α : Type, PropertySignatureOf α → Annotations := @PropertySignatureOf.annotations

example : Type → Type := IndexSignatureOf
example : ∀ α : Type, IndexSignatureOf α → α := @IndexSignatureOf.parameter
example : ∀ α : Type, IndexSignatureOf α → α := @IndexSignatureOf.type

end RecordChildren

/-! ## D4 — the mutual carrier

Twenty-two representation constructors in the frozen census order, and two
check constructors. Twelve constructors share the field list
`(Annotations) (List Check)` and stay twelve; `E4-SCHEMA-CE-026` is the
payload-layer companion of `E4-SCHEMA-CE-017`.

`Suspend.thunk` is a plain nested `Representation` — first-order at the pin, so
no closure, wrapper, `Option`, or reference key. Its `checks` field is present
and constrained to be empty by admission, not removed from the carrier.

`Declaration.representation` and `Filter.representation` are required by the
persisted codec even though the live interfaces mark them optional, so they are
non-`Option` fields; `FilterGroup.representation` is optional in both and is
`Option`. -/

section MutualCarrier

example : Type := Representation
example : Type := Check

/-- `SC-REP-03`, payload half. The instances are demanded; how they are
produced is the builder's choice, because `deriving DecidableEq` does not
cover mutual nested inductives on this toolchain. -/
example : DecidableEq Representation := inferInstance
example : DecidableEq Check := inferInstance

example :
    RepresentationAnnotation → Annotations → List Representation → List Check →
      Representation :=
  Representation.declaration
example : ReferenceKey → Representation := Representation.reference
example : Annotations → List Check → Representation → Representation :=
  Representation.suspend
example : Annotations → List Check → Representation := Representation.null
example : Annotations → List Check → Representation := Representation.undefined
example : Annotations → List Check → Representation := Representation.void
example : Annotations → List Check → Representation := Representation.never
example : Annotations → List Check → Representation := Representation.unknown
example : Annotations → List Check → Representation := Representation.any
example : Annotations → List Check → Representation := Representation.string
example : Annotations → List Check → Representation := Representation.number
example : Annotations → List Check → Representation := Representation.boolean
example : Annotations → List Check → Representation := Representation.bigint
example : Annotations → List Check → Representation := Representation.symbol
example : Annotations → List Check → LiteralValue → Representation :=
  Representation.literal
example : Annotations → List Check → GlobalSymbolKey → Representation :=
  Representation.uniqueSymbol
example : Annotations → List Check → Representation := Representation.objectKeyword
example : Annotations → List Check → List EnumEntry → Representation :=
  Representation.enum
example : Annotations → List Check → List Representation → Representation :=
  Representation.templateLiteral
example :
    Annotations → List Check → List (ElementOf Representation) →
      List Representation → Representation :=
  Representation.arrays
example :
    Annotations → List Check → List (PropertySignatureOf Representation) →
      List (IndexSignatureOf Representation) → Representation :=
  Representation.objects
example :
    Annotations → List Check → List Representation → UnionMode → Representation :=
  Representation.union

/-- `Filter` has no `checks` field, and is nevertheless not a leaf: its
`representation.schemas` is the second `Representation`/`Check` recursion edge,
and rc.112's own lowering walks it first. `E4-SCHEMA-CE-033`. -/
example :
    CheckRepresentationAnnotationOf Representation → Annotations → Bool → Check :=
  Check.filter

/-- `FilterGroup` does carry `annotations`; the census table's silence on that
field was an omission. `E4-SCHEMA-CE-034`. -/
example :
    Option (CheckRepresentationAnnotationOf Representation) → Annotations →
      List Check → Check :=
  Check.filterGroup

/-! The pin's own names for the applied record children. -/

example : Element = ElementOf Representation := rfl
example : PropertySignature = PropertySignatureOf Representation := rfl
example : IndexSignature = IndexSignatureOf Representation := rfl
example : CheckRepresentationAnnotation = CheckRepresentationAnnotationOf Representation :=
  rfl

/-- Absent and empty annotations build distinct carrier values. -/
example : Representation.never none [] ≠ Representation.never (some []) [] :=
  @Representation.absent_ne_empty_annotations

end MutualCarrier

/-! ## D5 — tag projection and the constructor cap

Without `tag` a 21- or 23-constructor payload carrier typechecks and every
census theorem in `RepresentationContract.lean` still passes.
`E4-SCHEMA-CE-027`.

The twenty-two equations are proved here by `rfl`, so `tag` must be a
non-recursive constructor match. `cases_census` is the constructor cap: the
exact-recursor device used by the tag packet is unavailable for a nested mutual
inductive, whose generated recursor carries one extra motive per nested
container instance and is an elaborator detail rather than a contracted API. -/

section TagProjection

example : Representation → RepresentationTag := Representation.tag
example : Check → CheckTag := Check.tag

example : ∀ (a : RepresentationAnnotation) (b : Annotations)
    (c : List Representation) (d : List Check),
    Representation.tag (Representation.declaration a b c d) = RepresentationTag.declaration :=
  fun _ _ _ _ => rfl
example : ∀ k : ReferenceKey,
    Representation.tag (Representation.reference k) = RepresentationTag.reference :=
  fun _ => rfl
example : ∀ (a : Annotations) (c : List Check) (t : Representation),
    Representation.tag (Representation.suspend a c t) = RepresentationTag.suspend :=
  fun _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.null a c) = RepresentationTag.null :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.undefined a c) = RepresentationTag.undefined :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.void a c) = RepresentationTag.void :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.never a c) = RepresentationTag.never :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.unknown a c) = RepresentationTag.unknown :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.any a c) = RepresentationTag.any :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.string a c) = RepresentationTag.string :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.number a c) = RepresentationTag.number :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.boolean a c) = RepresentationTag.boolean :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.bigint a c) = RepresentationTag.bigint :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.symbol a c) = RepresentationTag.symbol :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (l : LiteralValue),
    Representation.tag (Representation.literal a c l) = RepresentationTag.literal :=
  fun _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (s : GlobalSymbolKey),
    Representation.tag (Representation.uniqueSymbol a c s) = RepresentationTag.uniqueSymbol :=
  fun _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check),
    Representation.tag (Representation.objectKeyword a c) = RepresentationTag.objectKeyword :=
  fun _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (e : List EnumEntry),
    Representation.tag (Representation.enum a c e) = RepresentationTag.enum :=
  fun _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (p : List Representation),
    Representation.tag (Representation.templateLiteral a c p) =
      RepresentationTag.templateLiteral :=
  fun _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (e : List (ElementOf Representation))
    (r : List Representation),
    Representation.tag (Representation.arrays a c e r) = RepresentationTag.arrays :=
  fun _ _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check)
    (p : List (PropertySignatureOf Representation))
    (i : List (IndexSignatureOf Representation)),
    Representation.tag (Representation.objects a c p i) = RepresentationTag.objects :=
  fun _ _ _ _ => rfl
example : ∀ (a : Annotations) (c : List Check) (t : List Representation) (m : UnionMode),
    Representation.tag (Representation.union a c t m) = RepresentationTag.union :=
  fun _ _ _ _ => rfl

example : ∀ (r : CheckRepresentationAnnotationOf Representation) (a : Annotations)
    (b : Bool),
    Check.tag (Check.filter r a b) = CheckTag.filter :=
  fun _ _ _ => rfl
example : ∀ (r : Option (CheckRepresentationAnnotationOf Representation))
    (a : Annotations) (c : List Check),
    Check.tag (Check.filterGroup r a c) = CheckTag.filterGroup :=
  fun _ _ _ => rfl

example : ∀ tag : RepresentationTag, ∃ r : Representation, Representation.tag r = tag :=
  @Representation.tag_surjective

example : ∀ tag : CheckTag, ∃ c : Check, Check.tag c = tag :=
  @Check.tag_surjective

/-- The constructor cap. A twenty-third representation constructor makes this
unprovable, which is what the tag packet's exact-recursor snapshot achieves for
the alphabet. -/
example : ∀ r : Representation,
    (∃ (rep : RepresentationAnnotation) (ann : Annotations)
        (tps : List Representation) (cs : List Check),
        r = Representation.declaration rep ann tps cs) ∨
    (∃ k : ReferenceKey, r = Representation.reference k) ∨
    (∃ (ann : Annotations) (cs : List Check) (thunk : Representation),
        r = Representation.suspend ann cs thunk) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.null ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.undefined ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.void ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.never ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.unknown ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.any ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.string ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.number ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.boolean ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.bigint ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.symbol ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check) (lit : LiteralValue),
        r = Representation.literal ann cs lit) ∨
    (∃ (ann : Annotations) (cs : List Check) (sym : GlobalSymbolKey),
        r = Representation.uniqueSymbol ann cs sym) ∨
    (∃ (ann : Annotations) (cs : List Check), r = Representation.objectKeyword ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check) (entries : List EnumEntry),
        r = Representation.enum ann cs entries) ∨
    (∃ (ann : Annotations) (cs : List Check) (parts : List Representation),
        r = Representation.templateLiteral ann cs parts) ∨
    (∃ (ann : Annotations) (cs : List Check)
        (elements : List (ElementOf Representation)) (rest : List Representation),
        r = Representation.arrays ann cs elements rest) ∨
    (∃ (ann : Annotations) (cs : List Check)
        (props : List (PropertySignatureOf Representation))
        (idxs : List (IndexSignatureOf Representation)),
        r = Representation.objects ann cs props idxs) ∨
    (∃ (ann : Annotations) (cs : List Check) (types : List Representation)
        (mode : UnionMode),
        r = Representation.union ann cs types mode) :=
  @Representation.cases_census

example : ∀ c : Check,
    (∃ (rep : CheckRepresentationAnnotationOf Representation) (ann : Annotations)
        (aborted : Bool),
        c = Check.filter rep ann aborted) ∨
    (∃ (rep : Option (CheckRepresentationAnnotationOf Representation))
        (ann : Annotations) (cs : List Check),
        c = Check.filterGroup rep ann cs) :=
  @Check.cases_census

end TagProjection

/-! ## D6 — documents

`Document` and `MultiDocument` are declared as containers only. No reference
edge is interpreted here: resolution, reachability, guardedness, and dead-entry
policy are `SC-DOC-*` and remain open. Tables are ordered `List`s because
duplicate JSON keys must be rejected before the table is constructed, and that
refusal needs the duplicate in hand. -/

section Documents

example : Type := ReferenceEntry
example : DecidableEq ReferenceEntry := inferInstance
example : ReferenceEntry → String := ReferenceEntry.key
example : ReferenceEntry → Representation := ReferenceEntry.representation

example : Type := Document
example : DecidableEq Document := inferInstance
example : Document → Representation := Document.representation
example : Document → List ReferenceEntry := Document.references

example : Type := MultiDocument
example : DecidableEq MultiDocument := inferInstance
example : MultiDocument → List Representation := MultiDocument.representations
example : MultiDocument → List ReferenceEntry := MultiDocument.references

/-- `E4-SCHEMA-CE-038`: the two shapes stay nominally distinct. -/
example : Document → MultiDocument := Document.toMulti

example : ∀ (root : Representation) (references : List ReferenceEntry),
    Document.toMulti (Document.mk root references) =
      MultiDocument.mk [root] references :=
  @Document.toMulti_mk

example : ∀ a b : Document, Document.toMulti a = Document.toMulti b → a = b :=
  @Document.toMulti_injective

/-- The non-image witness has two roots. An empty-root witness would conflate
the nominal one-root/many-root distinction with D7's non-empty-root admission
condition. -/
example : ∀ d : Document,
    Document.toMulti d ≠
      MultiDocument.mk
        [Representation.never none [], Representation.string none []] [] :=
  @Document.toMulti_two_roots_not_image

end Documents

/-! ## D7 — persisted/decode-side field admission, `SC-REP-04`

`FieldAdmissible` is exactly the pinned rc.112 constraints on a persisted
value being decoded into the structural carrier. It is a proposition with a
Boolean decision procedure, not a refusal or issue value. Encode-side pruning
of unsupported live annotation entries is a later wire judgment. -/

section FieldAdmission

example : Annotations → Prop := Annotations.FieldAdmissible
example : Annotations → Bool := Annotations.fieldAdmissible
example : Representation → Prop := Representation.FieldAdmissible
example : Representation → Bool := Representation.fieldAdmissible
example : Check → Prop := Check.FieldAdmissible
example : Check → Bool := Check.fieldAdmissible
example : Document → Prop := Document.FieldAdmissible
example : Document → Bool := Document.fieldAdmissible
example : MultiDocument → Prop := MultiDocument.FieldAdmissible
example : MultiDocument → Bool := MultiDocument.fieldAdmissible

example : ∀ annotations : Annotations,
    Annotations.fieldAdmissible annotations = true ↔
      Annotations.FieldAdmissible annotations :=
  @Annotations.fieldAdmissible_iff
example : Annotations.FieldAdmissible none :=
  @Annotations.fieldAdmissible_none
example : ∀ entries : List AnnotationEntry,
    Annotations.FieldAdmissible (some entries) ↔
      ∀ entry ∈ entries, Json.NumbersFinite entry.payload :=
  @Annotations.fieldAdmissible_some_iff

example : ∀ r : Representation,
    Representation.fieldAdmissible r = true ↔ Representation.FieldAdmissible r :=
  @Representation.fieldAdmissible_iff
example : ∀ c : Check, Check.fieldAdmissible c = true ↔ Check.FieldAdmissible c :=
  @Check.fieldAdmissible_iff
example : ∀ d : Document, Document.fieldAdmissible d = true ↔ Document.FieldAdmissible d :=
  @Document.fieldAdmissible_iff
example : ∀ m : MultiDocument,
    MultiDocument.fieldAdmissible m = true ↔ MultiDocument.FieldAdmissible m :=
  @MultiDocument.fieldAdmissible_iff

/-! ### Complete compositional specification

The Boolean/Prop agreement above is not a specification by itself: both sides
could be constant. These equations fix the proposition on every constructor
and every recursive route. Every ordinary annotation bag that is already
present in persisted input must contain finite JSON, including bags on array
elements, property signatures, and both check constructors. Encode-side
pruning happens before this judgment and remains a wire obligation. -/

example : ∀ (rep : RepresentationAnnotation) (ann : Annotations)
    (types : List Representation) (checks : List Check),
    Representation.FieldAdmissible
        (Representation.declaration rep ann types checks) ↔
      rep.id ≠ "" ∧
      Json.NumbersFinite rep.payload ∧
      Annotations.FieldAdmissible ann ∧
      (∀ child ∈ types, Representation.FieldAdmissible child) ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) :=
  @Representation.fieldAdmissible_declaration_iff

example : ∀ key : ReferenceKey,
    Representation.FieldAdmissible (Representation.reference key) ↔
      key.value ≠ "" :=
  @Representation.fieldAdmissible_reference_iff

example : ∀ (ann : Annotations) (checks : List Check) (thunk : Representation),
    Representation.FieldAdmissible (Representation.suspend ann checks thunk) ↔
      Annotations.FieldAdmissible ann ∧
      checks = [] ∧ Representation.FieldAdmissible thunk :=
  @Representation.fieldAdmissible_suspend_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.null ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_null_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.undefined ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_undefined_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.void ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_void_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.never ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_never_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.unknown ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_unknown_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.any ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_any_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.string ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_string_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.number ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_number_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.boolean ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_boolean_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.bigint ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_bigint_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.symbol ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_symbol_iff

example : ∀ (ann : Annotations) (checks : List Check) (value : String),
    Representation.FieldAdmissible
        (Representation.literal ann checks (LiteralValue.string value)) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_literal_string_iff

example : ∀ (ann : Annotations) (checks : List Check) (value : Float64),
    Representation.FieldAdmissible
        (Representation.literal ann checks (LiteralValue.number value)) ↔
      Annotations.FieldAdmissible ann ∧
      Float64.isFinite value = true ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) :=
  @Representation.fieldAdmissible_literal_number_iff

example : ∀ (ann : Annotations) (checks : List Check) (value : Int),
    Representation.FieldAdmissible
        (Representation.literal ann checks (LiteralValue.bigint value)) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_literal_bigint_iff

example : ∀ (ann : Annotations) (checks : List Check) (value : Bool),
    Representation.FieldAdmissible
        (Representation.literal ann checks (LiteralValue.boolean value)) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_literal_boolean_iff

/-! The raw enum-to-literal embedding is total. Finiteness enters only here,
at persisted field admission. The iff and its forward-use corollary prevent a
builder from hiding admission inside `EnumValue.toLiteralValue`. -/
example : ∀ value : EnumValue,
    Representation.FieldAdmissible
        (Representation.literal none [] (EnumValue.toLiteralValue value)) ↔
      match value with
      | .string _ => True
      | .number number => Float64.isFinite number = true :=
  @Representation.fieldAdmissible_toLiteralValue_iff

example : ∀ value : EnumValue,
    (match value with
      | .string _ => True
      | .number number => Float64.isFinite number = true) →
    Representation.FieldAdmissible
      (Representation.literal none [] (EnumValue.toLiteralValue value)) :=
  @Representation.fieldAdmissible_toLiteralValue_of_finite

example : ∀ (ann : Annotations) (checks : List Check) (key : GlobalSymbolKey),
    Representation.FieldAdmissible (Representation.uniqueSymbol ann checks key) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_uniqueSymbol_iff

example : ∀ (ann : Annotations) (checks : List Check),
    Representation.FieldAdmissible (Representation.objectKeyword ann checks) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_objectKeyword_iff

example : ∀ (ann : Annotations) (checks : List Check) (entries : List EnumEntry),
    Representation.FieldAdmissible (Representation.enum ann checks entries) ↔
      Annotations.FieldAdmissible ann ∧
      ∀ check ∈ checks, Check.FieldAdmissible check :=
  @Representation.fieldAdmissible_enum_iff

example : ∀ (ann : Annotations) (checks : List Check)
    (parts : List Representation),
    Representation.FieldAdmissible
        (Representation.templateLiteral ann checks parts) ↔
      Annotations.FieldAdmissible ann ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ part ∈ parts, Representation.FieldAdmissible part) :=
  @Representation.fieldAdmissible_templateLiteral_iff

example : ∀ (ann : Annotations) (checks : List Check)
    (elements : List (ElementOf Representation)) (rest : List Representation),
    Representation.FieldAdmissible
        (Representation.arrays ann checks elements rest) ↔
      Annotations.FieldAdmissible ann ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ element ∈ elements,
        Annotations.FieldAdmissible element.annotations ∧
        Representation.FieldAdmissible element.type) ∧
      (∀ child ∈ rest, Representation.FieldAdmissible child) :=
  @Representation.fieldAdmissible_arrays_iff

example : ∀ (ann : Annotations) (checks : List Check)
    (properties : List (PropertySignatureOf Representation))
    (indexes : List (IndexSignatureOf Representation)),
    Representation.FieldAdmissible
        (Representation.objects ann checks properties indexes) ↔
      Annotations.FieldAdmissible ann ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ property ∈ properties,
        Annotations.FieldAdmissible property.annotations ∧
        Representation.FieldAdmissible property.type) ∧
      (∀ index ∈ indexes,
        Representation.FieldAdmissible index.parameter ∧
        Representation.FieldAdmissible index.type) :=
  @Representation.fieldAdmissible_objects_iff

example : ∀ (ann : Annotations) (checks : List Check)
    (types : List Representation) (mode : UnionMode),
    Representation.FieldAdmissible (Representation.union ann checks types mode) ↔
      Annotations.FieldAdmissible ann ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ child ∈ types, Representation.FieldAdmissible child) :=
  @Representation.fieldAdmissible_union_iff

example : ∀ (rep : CheckRepresentationAnnotationOf Representation)
    (ann : Annotations) (aborted : Bool),
    Check.FieldAdmissible (Check.filter rep ann aborted) ↔
      rep.id ≠ "" ∧
      Json.NumbersFinite rep.payload ∧
      Annotations.FieldAdmissible ann ∧
      (∀ schemas : List Representation, rep.schemas = some schemas →
        ∀ child ∈ schemas, Representation.FieldAdmissible child) :=
  @Check.fieldAdmissible_filter_iff

example : ∀ (rep : Option (CheckRepresentationAnnotationOf Representation))
    (ann : Annotations) (checks : List Check),
    Check.FieldAdmissible (Check.filterGroup rep ann checks) ↔
      checks ≠ [] ∧
      Annotations.FieldAdmissible ann ∧
      (∀ check ∈ checks, Check.FieldAdmissible check) ∧
      (∀ annotation : CheckRepresentationAnnotationOf Representation,
        rep = some annotation →
          annotation.id ≠ "" ∧
          Json.NumbersFinite annotation.payload ∧
          (∀ schemas : List Representation, annotation.schemas = some schemas →
            ∀ child ∈ schemas, Representation.FieldAdmissible child)) :=
  @Check.fieldAdmissible_filterGroup_iff

example : ∀ (root : Representation) (references : List ReferenceEntry),
    Document.FieldAdmissible (Document.mk root references) ↔
      Representation.FieldAdmissible root ∧
      (∀ entry ∈ references,
        Representation.FieldAdmissible entry.representation) :=
  @Document.fieldAdmissible_mk_iff

example : ∀ (roots : List Representation) (references : List ReferenceEntry),
    MultiDocument.FieldAdmissible (MultiDocument.mk roots references) ↔
      roots ≠ [] ∧
      (∀ root ∈ roots, Representation.FieldAdmissible root) ∧
      (∀ entry ∈ references,
        Representation.FieldAdmissible entry.representation) :=
  @MultiDocument.fieldAdmissible_mk_iff

/-! ### Negative field-admission witnesses

These establish failed propositions only. They do not construct a refusal or
issue value and do not precommit a later diagnostic vocabulary or scan order. -/

/-- A retained ordinary annotation bag is decoded as JSON; non-finite payloads
are rejected here. Pruning unsupported live values on encode is a different,
later wire judgment. -/
example : ¬ Annotations.FieldAdmissible
    (some [⟨"bad", Json.number Float64.nan⟩]) :=
  @Annotations.not_fieldAdmissible_nonFinite

example : ¬ Representation.FieldAdmissible
    (Representation.never
      (some [⟨"bad", Json.number Float64.nan⟩]) []) :=
  @Representation.not_fieldAdmissible_nonFiniteAnnotations

example : ¬ Representation.FieldAdmissible
    (Representation.arrays none []
      [⟨false, Representation.never none [],
        some [⟨"bad", Json.number Float64.nan⟩]⟩] []) :=
  @Representation.not_fieldAdmissible_nonFiniteElementAnnotations

example : ¬ Representation.FieldAdmissible
    (Representation.objects none []
      [⟨PropertyKey.string "x", Representation.never none [], false, false,
        some [⟨"bad", Json.number Float64.nan⟩]⟩] []) :=
  @Representation.not_fieldAdmissible_nonFinitePropertyAnnotations

example : ¬ Check.FieldAdmissible
    (Check.filter ⟨"effect/test", Json.null, none⟩
      (some [⟨"bad", Json.number Float64.nan⟩]) false) :=
  @Check.not_fieldAdmissible_nonFiniteAnnotations

/-- `$ref: Schema.NonEmptyString`. -/
example : ¬ Representation.FieldAdmissible (Representation.reference ⟨""⟩) :=
  @Representation.not_fieldAdmissible_emptyReferenceKey

/-- `id: Schema.NonEmptyString` on the representation annotation. -/
example : ¬ Representation.FieldAdmissible
    (Representation.declaration ⟨"", Json.null⟩ none [] []) :=
  @Representation.not_fieldAdmissible_emptyAnnotationId

/-- `payload: Schema.Json`, and `isJsonLeaf` requires finiteness. This is the
third numeric domain: a non-finite number is a legal enum value and property
key, and is not a legal annotation payload. `E4-SCHEMA-CE-028`. -/
example : ¬ Representation.FieldAdmissible
    (Representation.declaration ⟨"effect/test", Json.number Float64.nan⟩ none [] []) :=
  @Representation.not_fieldAdmissible_nonFiniteAnnotationPayload

/-- The `Literal` number leg is `Schema.Finite`. -/
example : ¬ Representation.FieldAdmissible
    (Representation.literal none [] (LiteralValue.number Float64.nan)) :=
  @Representation.not_fieldAdmissible_nonFiniteLiteral

/-- `checks: Schema.Tuple([])` is present-and-exactly-empty, and it is the only
per-tag field constraint separating `Suspend` from the twelve keyword-shaped
tags. `E4-SCHEMA-CE-031`. -/
example : ¬ Representation.FieldAdmissible
    (Representation.suspend none
      [Check.filter ⟨"effect/test", Json.null, none⟩ none false]
      (Representation.never none [])) :=
  @Representation.not_fieldAdmissible_suspendChecks

/-- `FilterGroup.checks: Schema.NonEmptyArray`. -/
example : ¬ Check.FieldAdmissible (Check.filterGroup none none []) :=
  @Check.not_fieldAdmissible_emptyFilterGroup

/-- `MultiDocument.representations: Schema.NonEmptyArray`. -/
example : ¬ MultiDocument.FieldAdmissible (MultiDocument.mk [] []) :=
  @MultiDocument.not_fieldAdmissible_emptyRoots

/-- `E4-SCHEMA-CE-033`. The defect sits under `Filter.representation.schemas`,
the recursion edge that has no `checks` field. An admission relation that
recurses only through `FilterGroup.checks` never inspects it and passes every
other row of this battery. -/
example : ¬ Representation.FieldAdmissible
    (Representation.objects none
      [Check.filter
        ⟨"effect/test", Json.null, some [Representation.reference ⟨""⟩]⟩
        none false]
      [] []) :=
  @Representation.not_fieldAdmissible_throughFilterSchemas

/-! ### Acceptances, which is where over-strict admission is caught

Every row below is content rc.112 accepts. An admission that rejects any of
them is narrower than the pin without saying so, and the four "retains
witness" reserved rows become unprovable. -/

example : Representation.FieldAdmissible (Representation.reference ⟨"Node"⟩) :=
  @Representation.fieldAdmissible_nonEmptyReferenceKey

example : Representation.FieldAdmissible
    (Representation.literal none [] (LiteralValue.number Float64.zero)) :=
  @Representation.fieldAdmissible_finiteLiteral

example : Representation.FieldAdmissible
    (Representation.suspend none [] (Representation.never none [])) :=
  @Representation.fieldAdmissible_suspendEmptyChecks

/-- `Enum` values are `Schema.Number`, not `Schema.Finite`. -/
example : Representation.FieldAdmissible
    (Representation.enum none [] [⟨"NotANumber", EnumValue.number Float64.nan⟩]) :=
  @Representation.fieldAdmissible_nonFiniteEnumValue

/-- Property-name keys are `Schema.Number` too. -/
example : Representation.FieldAdmissible
    (Representation.objects none []
      [⟨PropertyKey.number Float64.nan, Representation.never none [], false, false, none⟩]
      []) :=
  @Representation.fieldAdmissible_nonFinitePropertyKey

/-- Enum aliases are permitted. A uniqueness clause here makes the reserved
`E4-SCHEMA-CE-003` witness unspellable. `E4-SCHEMA-CE-035`. -/
example : Representation.FieldAdmissible
    (Representation.enum none []
      [⟨"A", EnumValue.string "x"⟩, ⟨"B", EnumValue.string "x"⟩]) :=
  @Representation.fieldAdmissible_aliasedEnum

/-- rc.112's persisted field shape accepts an optional element before a
required one. This is only a field-shape result: the later Schema denotation
may reject the sequence, so the two judgments do not contradict each other.
The reserved `E4-SCHEMA-CE-004` needs the raw value to remain expressible. -/
example : Representation.FieldAdmissible
    (Representation.arrays none []
      [⟨true, Representation.string none [], none⟩,
       ⟨false, Representation.string none [], none⟩] []) :=
  @Representation.fieldAdmissible_optionalBeforeRequiredElement

/-- rc.112 persists `propertySignatures` as a plain array with no uniqueness
check, so duplicate keys are field-admissible. -/
example : Representation.FieldAdmissible
    (Representation.objects none []
      [⟨PropertyKey.string "a", Representation.string none [], false, false, none⟩,
       ⟨PropertyKey.string "a", Representation.number none [], false, false, none⟩]
      []) :=
  @Representation.fieldAdmissible_duplicatePropertyKeys

/-- Field admission resolves no reference. At the pin a dangling `$ref` is
accepted by the document codec `fromJson` and refused by the revival layer
`fromRepresentation`; neither is a field constraint. `E4-SCHEMA-CE-040`. -/
example : Document.FieldAdmissible
    (Document.mk (Representation.reference ⟨"Missing"⟩) []) :=
  @Document.fieldAdmissible_danglingReference

example : Document.FieldAdmissible
    (Document.mk (Representation.never none [])
      [⟨"Dead", Representation.never none []⟩]) :=
  @Document.fieldAdmissible_deadReferenceEntry

/-- `$ref` is `NonEmptyString` while a table key is plain `String`, so an entry
under the empty key is admissible but cannot be named by a field-admissible
reference. The permissive raw carrier can still spell an empty `$ref`, which
is why that scope qualification matters. `E4-SCHEMA-CE-030`. -/
example : Document.FieldAdmissible
    (Document.mk (Representation.never none [])
      [⟨"", Representation.never none []⟩]) :=
  @Document.fieldAdmissible_emptyTableKey

/-- The same plain-string table-key rule applies to the references table in a
multi-document; only `$ref` itself has the non-empty constraint. -/
example : MultiDocument.FieldAdmissible
    (MultiDocument.mk
      [Representation.never none [], Representation.string none []]
      [⟨"", Representation.never none []⟩]) :=
  @MultiDocument.fieldAdmissible_emptyTableKey

/-- The same two-root value used by the D6 non-image theorem is admissible, so
non-surjectivity is not being witnessed only by a D7-rejected empty root list. -/
example : MultiDocument.FieldAdmissible
    (MultiDocument.mk
      [Representation.never none [], Representation.string none []] []) :=
  @MultiDocument.fieldAdmissible_two_roots

end FieldAdmission

/-! ## Enforcement by absence

Each negative asserts exactly that a name does not resolve. The expected
substring is `Unknown` rather than `Unknown constant`, because before
implementation the enclosing type does not resolve either and Lean reports
`Unknown identifier`, while after implementation it reports `Unknown constant`.

These negatives are **vacuously satisfied while the carrier is absent**. They
become load-bearing when the enclosing type exists, which is exactly when the
mistake each guards against becomes available. -/

section AbsentConstructors

/- `E4-SCHEMA-CE-021` at the value layer: a persisted literal never carries
`null`, and the `Null` tag and `Json.null` are different things. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.LiteralValue.null)

/- `E4-SCHEMA-CE-022` at the value layer: a local symbol is never a portable
property key. This remains a necessary condition for the reserved
`E4-SCHEMA-CE-010`, not a discharge of it. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.PropertyKey.localSymbol)

/- `E4-SCHEMA-CE-020` at the value layer: enum values are strings or numbers
only, and widening them to the literal alphabet is invisible without this. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.EnumValue.bigint)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.EnumValue.boolean)

/- `E4-SCHEMA-CE-026`: the twelve shape-identical keyword nodes stay twelve
payload constructors. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Representation.keyword)

/- `E4-SCHEMA-CE-032`: only a check's annotation record carries referenced
schemas. Merging the two records gives `Declaration` a field the pin has
not got. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.RepresentationAnnotation.schemas)

/- An index signature is exactly `parameter` and `type`. Array elements and
property signatures do carry annotations; this one does not. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.IndexSignatureOf.annotations)

/- `E4-SCHEMA-CE-028`: `toLiteralValue` is the one canonical total raw
embedding. `toLiteral` would duplicate that API and could bypass the frozen
embedding/admission split; non-finites remain raw values and are rejected only
by the separate literal field-admission judgment. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.EnumValue.toLiteral)

/- `E4-SCHEMA-CE-039`: persisted field-key spellings are owned by the
wire-profile packet, not by the payload carrier. A spelling function appearing
in this fence breaks the battery, which is the signal to move it to its owner
rather than let it accrete here. -/
/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Representation.persistedFieldName)

/--
error: Unknown
-/
#guard_msgs(error, substring := true) in
#check (@Effect4.Representation.fieldKeyName)

end AbsentConstructors

/-!
The durable executable attacks for this packet live beside their rows in
`Test/Counterexamples/Schema/ATTACKS.md`. Rows whose evidence is the pinned
rc.112 bytes — `E4-SCHEMA-CE-028` .. `-034`, `-036`, `-037`, `-040`, `-042` —
have no Lean witness by construction: they are facts about a TypeScript source
at a fixed digest, and the corresponding executable host vectors are owed under
`SC-HOST-03` and `SC-HOST-04`.
-/

end Test.Schema.PayloadContract
