import Std
import Effect4.Schema.Payload

/-!
# Schema representation tag census

Owner: the rc.112 persisted representation alphabet.

This module owns the *tag* layer of Effect4's Schema representation: the exact
22-member persisted alphabet, its canonical census listing, and the
case-sensitive wire spelling of each member. Its contract packet is
`test/contracts/schema-representation.contract.md` and its ruling input is the
frozen census table in `docs/SCHEMA-CUTOVER.md`.

The payload carrier is deliberately not declared here. `Representation`
itself, its per-tag persisted fields, `Check`, annotations, `Document`, and
`MultiDocument` remain unopened, and no denotation, admission, codec, wire, or
profile claim is made. A tag is a name, not a meaning.

The tags are nominal. Twelve of them share one persisted field shape in
rc.112 — the eleven keyword tags and `objectKeyword` all persist as optional
annotations plus ordered checks — and they remain twelve distinct tags,
because the persisted `_tag` string is itself observable content.
-/

namespace Effect4

/--
The rc.112 persisted representation alphabet, in the source order of the
frozen census table.

Constructor order is the listing order of that table. It is a **membership
census**: it carries no claim about parser precedence, decode order, or union
member preference. No theorem in this module observes a tag's position.
-/
inductive RepresentationTag where
  /-- An opaque declaration with a required representation and type parameters. -/
  | declaration
  /-- A non-empty `$ref` into a document's references table. -/
  | reference
  /-- A lazy boundary. Its persisted `checks` are exactly empty. -/
  | suspend
  /-- The `null` keyword. -/
  | null
  /-- The `undefined` keyword. -/
  | undefined
  /-- The `void` keyword. -/
  | void
  /-- The `never` keyword. -/
  | never
  /-- The `unknown` keyword. -/
  | unknown
  /-- The `any` keyword. -/
  | any
  /-- The `string` keyword. -/
  | string
  /-- The `number` keyword. -/
  | number
  /-- The `boolean` keyword. -/
  | boolean
  /-- The `bigint` keyword. -/
  | bigint
  /-- The `symbol` keyword. -/
  | symbol
  /-- One tagged string, finite-number, bigint, or boolean literal; never `null`. -/
  | literal
  /-- A persistable global symbol. Local symbols are live-only. -/
  | uniqueSymbol
  /-- The `object` keyword, distinct from the structural `objects` tag. -/
  | objectKeyword
  /-- Ordered `[name, value]` entries whose values are strings or numbers. -/
  | enum
  /-- Ordered template-literal parts. -/
  | templateLiteral
  /-- Ordered `elements` together with ordered `rest` representations. -/
  | arrays
  /-- Property-signature and index-signature collections. -/
  | objects
  /-- Ordered member `types` with mode `anyOf` or `oneOf`. -/
  | union
deriving DecidableEq, Repr, Inhabited

namespace RepresentationTag

/--
The canonical census listing of the alphabet.

This is a membership listing in the frozen table's order. Coverage is proved
by case analysis in `mem_census`, so the semantic coverage theorem does not
depend on position. The separate public-surface battery freezes this exact
order through the dependent recursor and census listing; it may not be
permuted without changing the contracted API. No precedence claim follows.
-/
def census : List RepresentationTag :=
  [.declaration, .reference, .suspend,
   .null, .undefined, .void, .never, .unknown, .any,
   .string, .number, .boolean, .bigint, .symbol,
   .literal, .uniqueSymbol, .objectKeyword, .enum,
   .templateLiteral, .arrays, .objects, .union]

/--
The exact case-sensitive rc.112 `_tag` string of a representation tag.

The spelling is pinned per tag rather than produced by a generic constructor
printer. `bigint` becomes `BigInt`, while the camel-case constructors must
retain their internal capitals. A generic capitalization or pretty-printing
rule would therefore be an unnecessary source of wire drift.
-/
def tagName : RepresentationTag → String
  | .declaration => "Declaration"
  | .reference => "Reference"
  | .suspend => "Suspend"
  | .null => "Null"
  | .undefined => "Undefined"
  | .void => "Void"
  | .never => "Never"
  | .unknown => "Unknown"
  | .any => "Any"
  | .string => "String"
  | .number => "Number"
  | .boolean => "Boolean"
  | .bigint => "BigInt"
  | .symbol => "Symbol"
  | .literal => "Literal"
  | .uniqueSymbol => "UniqueSymbol"
  | .objectKeyword => "ObjectKeyword"
  | .enum => "Enum"
  | .templateLiteral => "TemplateLiteral"
  | .arrays => "Arrays"
  | .objects => "Objects"
  | .union => "Union"

/--
Recognise a persisted `_tag` string.

This accepts exactly the 22 census spellings and rejects everything else,
including case variants and `SchemaAST` names that never reach persisted
content. It is a total function into `Option`; it is not a decoder, and it
makes no claim about the payload that accompanies the tag.
-/
def ofTagName : String → Option RepresentationTag
  | "Declaration" => some .declaration
  | "Reference" => some .reference
  | "Suspend" => some .suspend
  | "Null" => some .null
  | "Undefined" => some .undefined
  | "Void" => some .void
  | "Never" => some .never
  | "Unknown" => some .unknown
  | "Any" => some .any
  | "String" => some .string
  | "Number" => some .number
  | "Boolean" => some .boolean
  | "BigInt" => some .bigint
  | "Symbol" => some .symbol
  | "Literal" => some .literal
  | "UniqueSymbol" => some .uniqueSymbol
  | "ObjectKeyword" => some .objectKeyword
  | "Enum" => some .enum
  | "TemplateLiteral" => some .templateLiteral
  | "Arrays" => some .arrays
  | "Objects" => some .objects
  | "Union" => some .union
  | _ => none

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 22 := by decide

/-- The census repeats no tag. -/
theorem census_nodup : census.Nodup := by decide

/--
The census covers the alphabet.

Proved by case analysis rather than by a membership scan, so the statement is
insensitive to the listing order.

Together with `census_length` and `census_nodup` this is the census. The three
are stated separately because deriving any one from the other two needs a
cardinality argument this module deliberately does not import; they are **not**
logically independent. Length plus duplicate freedom implies coverage by
pigeonhole, and duplicate freedom plus coverage forces the length.
`E4-SCHEMA-CE-019` refutes the weaker and more tempting belief that
`census_length = 22` alone establishes the census.
-/
theorem mem_census (tag : RepresentationTag) : tag ∈ census := by
  cases tag <;> decide

/-- Every census spelling is recognised, and recognised as its own tag. -/
theorem ofTagName_tagName (tag : RepresentationTag) :
    ofTagName tag.tagName = some tag := by
  cases tag <;> decide

/--
Wire spellings are injective.

Derived from `ofTagName_tagName` rather than by comparing all 484 pairs: if two
tags spell alike then recognition of that one spelling returns both.
-/
theorem tagName_injective {a b : RepresentationTag}
    (h : a.tagName = b.tagName) : a = b := by
  have ha := ofTagName_tagName a
  rw [h, ofTagName_tagName b] at ha
  exact (Option.some.inj ha).symm

/--
Recognition is a partial inverse of spelling.

With `ofTagName_tagName` this states that `ofTagName` and `tagName` are
mutually inverse on the census. Neither result claims `ofTagName` is total,
and neither licenses any claim about decoding a full representation.
-/
theorem tagName_ofTagName {s : String} {tag : RepresentationTag}
    (h : ofTagName s = some tag) : tag.tagName = s := by
  unfold ofTagName at h
  split at h
  all_goals first
    | (obtain rfl := Option.some.inj h; rfl)
    | simp at h

end RepresentationTag

/-!
## Closed sub-alphabets

The frozen census pins five further closed alphabets inside the persisted
representation. They are declared here so the tag layer keeps one owner.

Wire spellings are supplied only for the two alphabets whose strings the
*ruling* pins: the `anyOf`/`oneOf` union mode and the `Filter`/`FilterGroup`
check tag.

The literal, enum-value, and property-key kinds carry no name function. The
pinned bytes do spell them: literal alternatives at
`SchemaRepresentation.ts:998,1005-1007`, enum codecs at `:998-999` used at
`:1020`, and property-key alternatives at `:1041-1043`. Those spellings sit on
payload envelopes, and the payload carrier is unopened. This module invents
nothing and defers them rather than guessing which layer owns them.

Note that the pin spells the symbol key `"symbol"` at line 1043 while the
constructor here is `globalSymbol`. The payload packet must take that spelling
from the pin and never from the constructor name. This is a later payload
spelling obligation; `E4-SCHEMA-CE-018` covers representation-tag `_tag`
drift, not property-key payload spellings.
-/

/--
Union member-selection mode.

`anyOf` retains member order and operationally chooses the first success;
`oneOf` rejects multiple successes. That operational difference is a
denotation-layer obligation and is not claimed here.
-/
inductive UnionMode where
  /-- First successful member wins; member order is retained. -/
  | anyOf
  /-- Exactly one member may succeed. -/
  | oneOf
deriving DecidableEq, Repr, Inhabited

namespace UnionMode

/-- The closed union-mode alphabet. -/
def census : List UnionMode := [.anyOf, .oneOf]

/-- The exact persisted mode string. -/
def modeName : UnionMode → String
  | .anyOf => "anyOf"
  | .oneOf => "oneOf"

/-- Recognise a persisted mode string; nothing else is a mode. -/
def ofModeName : String → Option UnionMode
  | "anyOf" => some .anyOf
  | "oneOf" => some .oneOf
  | _ => none

theorem census_length : census.length = 2 := by decide

theorem census_nodup : census.Nodup := by decide

theorem mem_census (mode : UnionMode) : mode ∈ census := by
  cases mode <;> decide

theorem ofModeName_modeName (mode : UnionMode) :
    ofModeName mode.modeName = some mode := by
  cases mode <;> decide

theorem modeName_injective {a b : UnionMode}
    (h : a.modeName = b.modeName) : a = b := by
  have ha := ofModeName_modeName a
  rw [h, ofModeName_modeName b] at ha
  exact (Option.some.inj ha).symm

theorem modeName_ofModeName {s : String} {mode : UnionMode}
    (h : ofModeName s = some mode) : mode.modeName = s := by
  unfold ofModeName at h
  split at h
  all_goals first
    | (obtain rfl := Option.some.inj h; rfl)
    | simp at h

end UnionMode

/--
Persisted check node kinds.

rc.112 `Check` is exactly `Filter | FilterGroup`. This alphabet names those
two nodes; their persisted fields belong to the unopened payload carrier.
-/
inductive CheckTag where
  /-- A single filter carrying a required representation annotation. -/
  | filter
  /-- A group whose ordered `checks` are non-empty. -/
  | filterGroup
deriving DecidableEq, Repr, Inhabited

namespace CheckTag

/-- The closed check alphabet. -/
def census : List CheckTag := [.filter, .filterGroup]

/-- The exact persisted `_tag` string. -/
def tagName : CheckTag → String
  | .filter => "Filter"
  | .filterGroup => "FilterGroup"

/-- Recognise a persisted check `_tag`; nothing else is a check node. -/
def ofTagName : String → Option CheckTag
  | "Filter" => some .filter
  | "FilterGroup" => some .filterGroup
  | _ => none

theorem census_length : census.length = 2 := by decide

theorem census_nodup : census.Nodup := by decide

theorem mem_census (tag : CheckTag) : tag ∈ census := by
  cases tag <;> decide

theorem ofTagName_tagName (tag : CheckTag) :
    ofTagName tag.tagName = some tag := by
  cases tag <;> decide

theorem tagName_injective {a b : CheckTag}
    (h : a.tagName = b.tagName) : a = b := by
  have ha := ofTagName_tagName a
  rw [h, ofTagName_tagName b] at ha
  exact (Option.some.inj ha).symm

theorem tagName_ofTagName {s : String} {tag : CheckTag}
    (h : ofTagName s = some tag) : tag.tagName = s := by
  unfold ofTagName at h
  split at h
  all_goals first
    | (obtain rfl := Option.some.inj h; rfl)
    | simp at h

end CheckTag

/--
Literal payload kinds.

rc.112 admits one tagged string, finite-number, bigint, or boolean literal and
**never** `null`. The absence of a `null` constructor is the enforcement: a
null literal has no spelling in this alphabet at all.
-/
inductive LiteralKind where
  /-- A string literal. -/
  | string
  /-- A finite number literal. Non-finite values are not persistable as literals. -/
  | number
  /-- A bigint literal. -/
  | bigint
  /-- A boolean literal. -/
  | boolean
deriving DecidableEq, Repr, Inhabited

namespace LiteralKind

/-- The closed literal-kind alphabet. -/
def census : List LiteralKind := [.string, .number, .bigint, .boolean]

theorem census_length : census.length = 4 := by decide

theorem census_nodup : census.Nodup := by decide

theorem mem_census (kind : LiteralKind) : kind ∈ census := by
  cases kind <;> decide

end LiteralKind

/--
Enum member value kinds.

rc.112 enum entries carry tagged strings or numbers only. This is a strictly
smaller alphabet than `LiteralKind`; the two must not be shared.
-/
inductive EnumValueKind where
  /-- A string enum value. -/
  | string
  /-- A number enum value. -/
  | number
deriving DecidableEq, Repr, Inhabited

namespace EnumValueKind

/-- The closed enum-value alphabet. -/
def census : List EnumValueKind := [.string, .number]

theorem census_length : census.length = 2 := by decide

theorem census_nodup : census.Nodup := by decide

theorem mem_census (kind : EnumValueKind) : kind ∈ census := by
  cases kind <;> decide

/--
The kind-level embedding of enum value kinds into literal payload kinds.

This maps **kinds, not values**, and carries no claim that an enum value is
admissible as a literal payload. At the pin the two have different numeric
domains: the `Literal` number leg is `Schema.Finite`
(`SchemaRepresentation.ts:1005`) while the `Enum` number leg is
`Schema.Number` (`:999`, used at `:1020`). A non-finite enum number therefore
has no literal spelling, even though both kinds are spelled `number`.

Relating the value domains is a payload-layer obligation. See
`E4-SCHEMA-CE-023`.
-/
def toLiteralKind : EnumValueKind → LiteralKind
  | .string => .string
  | .number => .number

theorem toLiteralKind_injective {a b : EnumValueKind}
    (h : a.toLiteralKind = b.toLiteralKind) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

/-- The embedding is not surjective: a bigint literal is not an enum value.
This is a statement about kinds; it is not the numeric-domain separation. -/
theorem toLiteralKind_ne_bigint (kind : EnumValueKind) :
    kind.toLiteralKind ≠ .bigint := by
  cases kind <;> decide

/-- Nor is a boolean literal. -/
theorem toLiteralKind_ne_boolean (kind : EnumValueKind) :
    kind.toLiteralKind ≠ .boolean := by
  cases kind <;> decide

end EnumValueKind

/--
Object property key kinds.

rc.112 persists string, number, and global-symbol keys. Local symbols are
live-only and have no constructor here, so an unportable key cannot be spelled
in *this* alphabet.

The scope of that is narrow. The absence is necessary only relative to the
chosen enforce-by-absence design — an admission rule over a wider alphabet
would exclude local symbols too. And it closes only one of two routes at the
pin: `UniqueSymbol.symbol` (`SchemaRepresentation.ts:1013`) is a second place a
symbol enters a representation, and this alphabet says nothing about it.

So the absence does **not** discharge the reserved `E4-SCHEMA-CE-010`, which
attacks the payload and lowering layers.
-/
inductive PropertyKeyKind where
  /-- A string property key. -/
  | string
  /-- A number property key. -/
  | number
  /-- A registered global symbol key. -/
  | globalSymbol
deriving DecidableEq, Repr, Inhabited

namespace PropertyKeyKind

/-- The closed property-key alphabet. -/
def census : List PropertyKeyKind := [.string, .number, .globalSymbol]

theorem census_length : census.length = 3 := by decide

theorem census_nodup : census.Nodup := by decide

theorem mem_census (kind : PropertyKeyKind) : kind ∈ census := by
  cases kind <;> decide

end PropertyKeyKind

end Effect4

/-!
# Schema representation payload carrier

Owner: the rc.112 persisted representation *payload* — the recursive
first-order tree that hangs off the 22-tag census above, the non-recursive
scalar and record types it is built from, and the tag projection that ties the
two layers together. Its contract packet is
`test/contracts/schema-payload.contract.md` and its battery is
`Effect4Test/Schema/PayloadContract.lean`.

The alphabet section above closes its own `namespace Effect4` block. That
section is frozen and guarded by `scripts/test-schema-alphabet-mutations.sh`;
nothing below changes a declaration in it.

## Scope

A carrier value is syntax. Nothing here says what it accepts, represents,
resolves to, or encodes as. Field admission is `Effect4/Schema/Check.lean`,
documents are `Effect4/Schema/Document.lean`, and reference resolution,
guardedness, denotation, codecs, and wire form are all unopened. This module
also claims **no** persisted field-key spelling: binder names below are
internal, `$ref` is carried as `ReferenceKey.value`, and the spellings belong
to the wire-profile packet (`SC-WIRE-01`, `SC-WIRE-02`).

## Which equality

`SC-REP-03`'s payload half is decidable **structural** equality on the Lean
carrier. It is not the host's `===`, not wire equality, and not a denotational
equality. `deriving DecidableEq` does not apply to a mutual nested inductive on
this toolchain, so the instances are built from `Representation.beq` and its
agreement theorem.

Only `DecidableEq` is derived below. `Repr` and `Inhabited` are deliberately
not: almost every payload type contains `Float64` or `Json`, and this module
claims no instance of theirs beyond the decidable structural equality the
contract requires.

## The carrier is permissive

Raw, admitted, and canonical forms are one carrier plus checked evidence. The
carrier holds content rc.112 refuses — an empty `$ref`, a non-finite literal, a
`Suspend` carrying a check — because a decoder must hold the offending value
long enough to reject it. Only kinds that are *unspellable* are enforced by
absence: there is no `LiteralValue.null`, no `PropertyKey.localSymbol`, and no
`EnumValue.bigint` or `EnumValue.boolean`.
-/

namespace Effect4

/-! D2 scalar carriers and D3 parameterized child records are imported from
`Effect4.Schema.Payload`. The kind projections below remain here because they
depend on this module's frozen alphabets. -/

/-- The closed literal kind a literal payload value belongs to. -/
def LiteralValue.kind : LiteralValue → LiteralKind
  | .string _ => .string
  | .number _ => .number
  | .bigint _ => .bigint
  | .boolean _ => .boolean

/-- The closed enum-value kind an enum member value belongs to. -/
def EnumValue.kind : EnumValue → EnumValueKind
  | .string _ => .string
  | .number _ => .number

/-- The closed property-key kind a property key belongs to. -/
def PropertyKey.kind : PropertyKey → PropertyKeyKind
  | .string _ => .string
  | .number _ => .number
  | .globalSymbol _ => .globalSymbol

/--
Every literal kind is inhabited by a literal payload value.

With the kind alphabet's own census this is the anti-drift law between the two
layers: neither can gain or lose a row unnoticed.
-/
theorem LiteralValue.kind_surjective (kind : LiteralKind) :
    ∃ value : LiteralValue, LiteralValue.kind value = kind := by
  cases kind with
  | string => exact ⟨.string "", rfl⟩
  | number => exact ⟨.number Float64.zero, rfl⟩
  | bigint => exact ⟨.bigint 0, rfl⟩
  | boolean => exact ⟨.boolean false, rfl⟩

/-- Every enum-value kind is inhabited by an enum member value. -/
theorem EnumValue.kind_surjective (kind : EnumValueKind) :
    ∃ value : EnumValue, EnumValue.kind value = kind := by
  cases kind with
  | string => exact ⟨.string "", rfl⟩
  | number => exact ⟨.number Float64.zero, rfl⟩

/-- Every property-key kind is inhabited by a property key. -/
theorem PropertyKey.kind_surjective (kind : PropertyKeyKind) :
    ∃ key : PropertyKey, PropertyKey.kind key = kind := by
  cases kind with
  | string => exact ⟨.string "", rfl⟩
  | number => exact ⟨.number Float64.zero, rfl⟩
  | globalSymbol => exact ⟨.globalSymbol ⟨""⟩, rfl⟩

/--
The constructor cap on literal payload values.

Kind surjectivity alone does not cap these carriers: an extra constructor could
reuse an existing kind and leave every kind theorem passing. This closes that
hole, and a fifth constructor makes it unprovable.
-/
theorem LiteralValue.cases_census (value : LiteralValue) :
    (∃ text : String, value = LiteralValue.string text) ∨
    (∃ number : Float64, value = LiteralValue.number number) ∨
    (∃ number : Int, value = LiteralValue.bigint number) ∨
    (∃ flag : Bool, value = LiteralValue.boolean flag) := by
  cases value <;> simp

/-- The constructor cap on enum member values. A third constructor breaks it. -/
theorem EnumValue.cases_census (value : EnumValue) :
    (∃ text : String, value = EnumValue.string text) ∨
    (∃ number : Float64, value = EnumValue.number number) := by
  cases value <;> simp

/-- The constructor cap on property keys. A fourth constructor breaks it. -/
theorem PropertyKey.cases_census (key : PropertyKey) :
    (∃ text : String, key = PropertyKey.string text) ∨
    (∃ number : Float64, key = PropertyKey.number number) ∨
    (∃ symbol : GlobalSymbolKey, key = PropertyKey.globalSymbol symbol) := by
  cases key <;> simp

/--
The value-level companion of `EnumValueKind.toLiteralKind`, which is
**total**.

`E4-SCHEMA-CE-023` fired at the kind layer: `toLiteralKind` maps kinds and says
nothing about values. The value layer was first modelled as partial, on the
reasoning that the `Enum` number leg is `Schema.Number` while the `Literal`
number leg is `Schema.Finite`. That put the refusal in the wrong place.
Executed evidence against the pin shows a non-finite number survives as a
discriminated string escape, so the datum is representable; what refuses it is
the literal leg at *admission*, which D7 states separately. A partial
embedding would discard the datum before admission could speak about it.
`E4-SCHEMA-CE-028`.
-/
def EnumValue.toLiteralValue : EnumValue → LiteralValue
  | .string value => .string value
  | .number value => .number value

/-- A string enum value carries across unchanged. -/
theorem EnumValue.toLiteralValue_string (value : String) :
    EnumValue.toLiteralValue (.string value) = .string value := rfl

/--
A number enum value carries across unchanged, finite or not.

The embedding copies raw data and decides nothing about admissibility. A
non-finite binary64 datum *is* representable as a `LiteralValue.number`;
whether such a literal is field-admissible is the separate D7 question, and
there the `Literal` leg refuses it. Making the embedding partial here would
put the refusal in the wrong layer and lose the datum before admission could
speak about it. `E4-SCHEMA-CE-028`.
-/
theorem EnumValue.toLiteralValue_number (value : Float64) :
    EnumValue.toLiteralValue (.number value) = .number value := rfl

/-- The embedding loses nothing: distinct enum values stay distinct. -/
theorem EnumValue.toLiteralValue_injective :
    Function.Injective EnumValue.toLiteralValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [EnumValue.toLiteralValue]

/-- The value map agrees with the frozen kind map on the nose. -/
theorem EnumValue.toLiteralValue_kind (value : EnumValue) :
    LiteralValue.kind (EnumValue.toLiteralValue value) =
      EnumValueKind.toLiteralKind (EnumValue.kind value) := by
  cases value with
  | string _ => rfl
  | number _ => rfl

/-!
## The mutual carrier

`Representation` and `Check` are mutually recursive through **two** edges:
`FilterGroup.checks` (`SchemaRepresentation.ts:461`, codec `:966`), and
`Filter.representation.schemas` (`:37`, codec `:924`, used by `FilterSchema` at
`:958`). The second is easy to miss because `Filter` has no `checks` field, and
rc.112's own lowering walks it first. `E4-SCHEMA-CE-033`.
-/

mutual

/--
The rc.112 persisted representation payload tree.

Constructor order is the frozen census order of `RepresentationTag`, and
`Representation.tag` below is the law that keeps the two layers in step. The
pin's own `RepresentationUnion` is in a different, decode order; neither list may
be derived from the other.

The twelve shape-identical keyword-shaped nodes stay twelve constructors,
because the persisted `_tag` string is itself observable content
(`E4-SCHEMA-CE-026`).

`Suspend.thunk` is a plain nested representation — first-order at the pin, so no
closure, wrapper, `Option`, or reference key — and its `checks` field is present
and constrained empty by admission rather than removed from the carrier
(`E4-SCHEMA-CE-031`).

`Declaration.representation` is optional in the rc.112 interface (`:146`) and
required by the persisted codec (`:979`); the carrier follows the codec.
-/
inductive Representation where
  /-- An opaque declaration with a codec-required representation annotation
  and ordered type parameters. -/
  | declaration (representation : RepresentationAnnotation)
      (annotations : Annotations) (typeParameters : List Representation)
      (checks : List Check)
  /-- A `$ref` into a document's references table. Exactly `_tag` and `$ref`. -/
  | reference (ref : ReferenceKey)
  /-- A lazy boundary whose persisted `checks` are exactly empty. -/
  | suspend (annotations : Annotations) (checks : List Check)
      (thunk : Representation)
  /-- The `null` keyword. -/
  | null (annotations : Annotations) (checks : List Check)
  /-- The `undefined` keyword. -/
  | undefined (annotations : Annotations) (checks : List Check)
  /-- The `void` keyword. -/
  | void (annotations : Annotations) (checks : List Check)
  /-- The `never` keyword. -/
  | never (annotations : Annotations) (checks : List Check)
  /-- The `unknown` keyword. -/
  | unknown (annotations : Annotations) (checks : List Check)
  /-- The `any` keyword. -/
  | any (annotations : Annotations) (checks : List Check)
  /-- The `string` keyword. -/
  | string (annotations : Annotations) (checks : List Check)
  /-- The `number` keyword. -/
  | number (annotations : Annotations) (checks : List Check)
  /-- The `boolean` keyword. -/
  | boolean (annotations : Annotations) (checks : List Check)
  /-- The `bigint` keyword. -/
  | bigint (annotations : Annotations) (checks : List Check)
  /-- The `symbol` keyword. -/
  | symbol (annotations : Annotations) (checks : List Check)
  /-- One tagged string, finite-number, bigint, or boolean literal. -/
  | literal (annotations : Annotations) (checks : List Check)
      (literal : LiteralValue)
  /-- A persistable global symbol. -/
  | uniqueSymbol (annotations : Annotations) (checks : List Check)
      (symbol : GlobalSymbolKey)
  /-- The `object` keyword, distinct from the structural `objects` node. -/
  | objectKeyword (annotations : Annotations) (checks : List Check)
  /-- Ordered `[name, value]` entries. Aliases are permitted. -/
  | enum (annotations : Annotations) (checks : List Check) (enums : List EnumEntry)
  /-- Ordered template-literal parts. -/
  | templateLiteral (annotations : Annotations) (checks : List Check)
      (parts : List Representation)
  /-- Ordered `elements` together with ordered `rest` representations. -/
  | arrays (annotations : Annotations) (checks : List Check)
      (elements : List (ElementOf Representation)) (rest : List Representation)
  /-- Property-signature and index-signature collections. -/
  | objects (annotations : Annotations) (checks : List Check)
      (propertySignatures : List (PropertySignatureOf Representation))
      (indexSignatures : List (IndexSignatureOf Representation))
  /-- Ordered member `types` with mode `anyOf` or `oneOf`. -/
  | union (annotations : Annotations) (checks : List Check)
      (types : List Representation) (mode : UnionMode)

/--
The rc.112 persisted check node, exactly `Filter | FilterGroup`.

`Filter` has no `checks` field and is nevertheless not a leaf: its
`representation.schemas` is the second recursion edge. `Filter.representation`
is optional in the interface (`:446`) and required by the codec (`:958`), so it
is not an `Option` here; `FilterGroup.representation` is optional in both
(`:459`, `:964`) and is.

`FilterGroup` does carry `annotations` (`:460`, codec `:965`); the ruling's
census table is silent on that field and a silence is not an absence
(`E4-SCHEMA-CE-034`).
-/
inductive Check where
  /-- A single filter carrying a codec-required representation annotation. -/
  | filter (representation : CheckRepresentationAnnotationOf Representation)
      (annotations : Annotations) (aborted : Bool)
  /-- A group whose ordered `checks` are made non-empty by admission. -/
  | filterGroup
      (representation : Option (CheckRepresentationAnnotationOf Representation))
      (annotations : Annotations) (checks : List Check)

end

/-! The pin's own names for the applied record children. -/

/-- One ordered tuple element of a representation. -/
abbrev Element := ElementOf Representation

/-- One property signature of a representation. -/
abbrev PropertySignature := PropertySignatureOf Representation

/-- One index signature of a representation. -/
abbrev IndexSignature := IndexSignatureOf Representation

/-- A check's representation annotation. -/
abbrev CheckRepresentationAnnotation := CheckRepresentationAnnotationOf Representation

/-!
## Decidable structural equality

`deriving DecidableEq` has no handler for a mutual nested inductive on Lean
4.33.1, and none for the nested `Json` either. The instances below are therefore
built the long way: a Boolean structural comparison, an agreement theorem proved
by structural recursion over the same block, and `decidable_of_iff`.

Only the recursive positions are compared by these functions. Every other field
is compared with `==` through the derived instance of its own type, which is
where `DecidableEq Float64` and `DecidableEq Json` enter.
-/

mutual

/-- Structural equality on representations, as a Boolean. -/
private def Representation.beq : Representation → Representation → Bool
  | .declaration rep₁ ann₁ tps₁ cs₁, .declaration rep₂ ann₂ tps₂ cs₂ =>
      (rep₁ == rep₂) && (ann₁ == ann₂) && Representation.beqList tps₁ tps₂ &&
        Check.beqList cs₁ cs₂
  | .reference key₁, .reference key₂ =>
      (key₁ == key₂)
  | .suspend ann₁ cs₁ th₁, .suspend ann₂ cs₂ th₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && Representation.beq th₁ th₂
  | .null ann₁ cs₁, .null ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .undefined ann₁ cs₁, .undefined ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .void ann₁ cs₁, .void ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .never ann₁ cs₁, .never ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .unknown ann₁ cs₁, .unknown ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .any ann₁ cs₁, .any ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .string ann₁ cs₁, .string ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .number ann₁ cs₁, .number ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .boolean ann₁ cs₁, .boolean ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .bigint ann₁ cs₁, .bigint ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .symbol ann₁ cs₁, .symbol ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .literal ann₁ cs₁ lit₁, .literal ann₂ cs₂ lit₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && (lit₁ == lit₂)
  | .uniqueSymbol ann₁ cs₁ sym₁, .uniqueSymbol ann₂ cs₂ sym₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && (sym₁ == sym₂)
  | .objectKeyword ann₁ cs₁, .objectKeyword ann₂ cs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂
  | .enum ann₁ cs₁ es₁, .enum ann₂ cs₂ es₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && (es₁ == es₂)
  | .templateLiteral ann₁ cs₁ ps₁, .templateLiteral ann₂ cs₂ ps₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && Representation.beqList ps₁ ps₂
  | .arrays ann₁ cs₁ els₁ rs₁, .arrays ann₂ cs₂ els₂ rs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ &&
        Representation.beqElements els₁ els₂ && Representation.beqList rs₁ rs₂
  | .objects ann₁ cs₁ props₁ idxs₁, .objects ann₂ cs₂ props₂ idxs₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ &&
        Representation.beqProperties props₁ props₂ &&
        Representation.beqIndexes idxs₁ idxs₂
  | .union ann₁ cs₁ ts₁ md₁, .union ann₂ cs₂ ts₂ md₂ =>
      (ann₁ == ann₂) && Check.beqList cs₁ cs₂ && Representation.beqList ts₁ ts₂ &&
        (md₁ == md₂)
  | _, _ => false

/-- Elementwise structural equality on an ordered list of representations. -/
private def Representation.beqList : List Representation → List Representation → Bool
  | [], [] => true
  | first₁ :: rest₁, first₂ :: rest₂ =>
      Representation.beq first₁ first₂ && Representation.beqList rest₁ rest₂
  | _, _ => false

/-- Elementwise structural equality on an ordered list of tuple elements. -/
private def Representation.beqElements :
    List (ElementOf Representation) → List (ElementOf Representation) → Bool
  | [], [] => true
  | ⟨opt₁, ty₁, ann₁⟩ :: rest₁, ⟨opt₂, ty₂, ann₂⟩ :: rest₂ =>
      (opt₁ == opt₂) && Representation.beq ty₁ ty₂ && (ann₁ == ann₂) &&
        Representation.beqElements rest₁ rest₂
  | _, _ => false

/-- Elementwise structural equality on an ordered list of property signatures. -/
private def Representation.beqProperties :
    List (PropertySignatureOf Representation) →
      List (PropertySignatureOf Representation) → Bool
  | [], [] => true
  | ⟨nm₁, ty₁, opt₁, mut₁, ann₁⟩ :: rest₁, ⟨nm₂, ty₂, opt₂, mut₂, ann₂⟩ :: rest₂ =>
      (nm₁ == nm₂) && Representation.beq ty₁ ty₂ && (opt₁ == opt₂) &&
        (mut₁ == mut₂) && (ann₁ == ann₂) &&
        Representation.beqProperties rest₁ rest₂
  | _, _ => false

/-- Elementwise structural equality on an ordered list of index signatures. -/
private def Representation.beqIndexes :
    List (IndexSignatureOf Representation) →
      List (IndexSignatureOf Representation) → Bool
  | [], [] => true
  | ⟨par₁, ty₁⟩ :: rest₁, ⟨par₂, ty₂⟩ :: rest₂ =>
      Representation.beq par₁ par₂ && Representation.beq ty₁ ty₂ &&
        Representation.beqIndexes rest₁ rest₂
  | _, _ => false

/-- Structural equality on a check's representation annotation, which carries
the second recursion edge. -/
private def Representation.beqCheckAnnotation :
    CheckRepresentationAnnotationOf Representation →
      CheckRepresentationAnnotationOf Representation → Bool
  | ⟨id₁, payload₁, schemas₁⟩, ⟨id₂, payload₂, schemas₂⟩ =>
      (id₁ == id₂) && (payload₁ == payload₂) &&
        (match schemas₁, schemas₂ with
         | none, none => true
         | some list₁, some list₂ => Representation.beqList list₁ list₂
         | _, _ => false)

/-- Structural equality on an optional check representation annotation. -/
private def Representation.beqOptionCheckAnnotation :
    Option (CheckRepresentationAnnotationOf Representation) →
      Option (CheckRepresentationAnnotationOf Representation) → Bool
  | none, none => true
  | some first, some second => Representation.beqCheckAnnotation first second
  | _, _ => false

/-- Structural equality on checks, as a Boolean. -/
private def Check.beq : Check → Check → Bool
  | .filter rep₁ ann₁ ab₁, .filter rep₂ ann₂ ab₂ =>
      Representation.beqCheckAnnotation rep₁ rep₂ && (ann₁ == ann₂) &&
        (ab₁ == ab₂)
  | .filterGroup rep₁ ann₁ cs₁, .filterGroup rep₂ ann₂ cs₂ =>
      Representation.beqOptionCheckAnnotation rep₁ rep₂ && (ann₁ == ann₂) &&
        Check.beqList cs₁ cs₂
  | _, _ => false

/-- Elementwise structural equality on an ordered list of checks. -/
private def Check.beqList : List Check → List Check → Bool
  | [], [] => true
  | first₁ :: rest₁, first₂ :: rest₂ =>
      Check.beq first₁ first₂ && Check.beqList rest₁ rest₂
  | _, _ => false

end

mutual

/--
Boolean structural equality agrees with propositional equality on
representations.

`Suspend` is the only constructor with a direct `Representation` child, so it is
the only case that recurses into this theorem itself; every other recursive
position goes through one of the list companions below.
-/
private theorem Representation.beq_iff (first second : Representation) :
    Representation.beq first second = true ↔ first = second := by
  cases first
  case suspend ann₁ cs₁ th₁ =>
    cases second
    case suspend ann₂ cs₂ th₂ =>
      simp [Representation.beq, Check.beqList_iff, Representation.beq_iff th₁ th₂,
        and_assoc]
    all_goals simp [Representation.beq]
  all_goals
    cases second <;>
      simp [Representation.beq, Representation.beqList_iff, Check.beqList_iff,
        Representation.beqElements_iff, Representation.beqProperties_iff,
        Representation.beqIndexes_iff, and_assoc]
termination_by structural first

/-- Agreement for an ordered list of representations. -/
private theorem Representation.beqList_iff (first second : List Representation) :
    Representation.beqList first second = true ↔ first = second := by
  match first, second with
  | [], [] => simp [Representation.beqList]
  | [], _ :: _ => simp [Representation.beqList]
  | _ :: _, [] => simp [Representation.beqList]
  | head₁ :: tail₁, head₂ :: tail₂ =>
      simp [Representation.beqList, Representation.beq_iff head₁ head₂,
        Representation.beqList_iff tail₁ tail₂]
termination_by structural first

/-- Agreement for an ordered list of tuple elements. -/
private theorem Representation.beqElements_iff (first second : List (ElementOf Representation)) :
    Representation.beqElements first second = true ↔ first = second := by
  match first, second with
  | [], [] => simp [Representation.beqElements]
  | [], _ :: _ => simp [Representation.beqElements]
  | _ :: _, [] => simp [Representation.beqElements]
  | ⟨opt₁, ty₁, ann₁⟩ :: tail₁, ⟨opt₂, ty₂, ann₂⟩ :: tail₂ =>
      simp [Representation.beqElements, Representation.beq_iff ty₁ ty₂,
        Representation.beqElements_iff tail₁ tail₂, and_assoc]
termination_by structural first

/-- Agreement for an ordered list of property signatures. -/
private theorem Representation.beqProperties_iff
    (first second : List (PropertySignatureOf Representation)) :
    Representation.beqProperties first second = true ↔ first = second := by
  match first, second with
  | [], [] => simp [Representation.beqProperties]
  | [], _ :: _ => simp [Representation.beqProperties]
  | _ :: _, [] => simp [Representation.beqProperties]
  | ⟨nm₁, ty₁, opt₁, mut₁, ann₁⟩ :: tail₁, ⟨nm₂, ty₂, opt₂, mut₂, ann₂⟩ :: tail₂ =>
      simp [Representation.beqProperties, Representation.beq_iff ty₁ ty₂,
        Representation.beqProperties_iff tail₁ tail₂, and_assoc]
termination_by structural first

/-- Agreement for an ordered list of index signatures. -/
private theorem Representation.beqIndexes_iff
    (first second : List (IndexSignatureOf Representation)) :
    Representation.beqIndexes first second = true ↔ first = second := by
  match first, second with
  | [], [] => simp [Representation.beqIndexes]
  | [], _ :: _ => simp [Representation.beqIndexes]
  | _ :: _, [] => simp [Representation.beqIndexes]
  | ⟨par₁, ty₁⟩ :: tail₁, ⟨par₂, ty₂⟩ :: tail₂ =>
      simp [Representation.beqIndexes, Representation.beq_iff par₁ par₂,
        Representation.beq_iff ty₁ ty₂, Representation.beqIndexes_iff tail₁ tail₂,
        and_assoc]
termination_by structural first

/-- Agreement for a check's representation annotation. -/
private theorem Representation.beqCheckAnnotation_iff
    (first second : CheckRepresentationAnnotationOf Representation) :
    Representation.beqCheckAnnotation first second = true ↔ first = second := by
  match first, second with
  | ⟨id₁, payload₁, schemas₁⟩, ⟨id₂, payload₂, schemas₂⟩ =>
      cases schemas₁ <;> cases schemas₂ <;>
        simp [Representation.beqCheckAnnotation, Representation.beqList_iff,
          and_assoc]
termination_by structural first

/-- Agreement for an optional check representation annotation. -/
private theorem Representation.beqOptionCheckAnnotation_iff
    (first second : Option (CheckRepresentationAnnotationOf Representation)) :
    Representation.beqOptionCheckAnnotation first second = true ↔ first = second := by
  match first, second with
  | none, none => simp [Representation.beqOptionCheckAnnotation]
  | none, some _ => simp [Representation.beqOptionCheckAnnotation]
  | some _, none => simp [Representation.beqOptionCheckAnnotation]
  | some value₁, some value₂ =>
      simp [Representation.beqOptionCheckAnnotation,
        Representation.beqCheckAnnotation_iff value₁ value₂]
termination_by structural first

/-- Boolean structural equality agrees with propositional equality on checks. -/
private theorem Check.beq_iff (first second : Check) :
    Check.beq first second = true ↔ first = second := by
  cases first <;> cases second <;>
    simp [Check.beq, Representation.beqCheckAnnotation_iff,
      Representation.beqOptionCheckAnnotation_iff, Check.beqList_iff, and_assoc]
termination_by structural first

/-- Agreement for an ordered list of checks. -/
private theorem Check.beqList_iff (first second : List Check) :
    Check.beqList first second = true ↔ first = second := by
  match first, second with
  | [], [] => simp [Check.beqList]
  | [], _ :: _ => simp [Check.beqList]
  | _ :: _, [] => simp [Check.beqList]
  | head₁ :: tail₁, head₂ :: tail₂ =>
      simp [Check.beqList, Check.beq_iff head₁ head₂, Check.beqList_iff tail₁ tail₂]
termination_by structural first

end

/-- `SC-REP-03`, payload half: decidable structural equality on representations. -/
instance : DecidableEq Representation :=
  fun first second => decidable_of_iff _ (Representation.beq_iff first second)

/-- `SC-REP-03`, payload half: decidable structural equality on checks. -/
instance : DecidableEq Check :=
  fun first second => decidable_of_iff _ (Check.beq_iff first second)

/-!
## Tag projection and the constructor cap

`tag` is the anti-drift law between this payload layer and the frozen tag
alphabet. Without it a 21- or 23-constructor carrier typechecks and every census
theorem in `Effect4Test/Schema/RepresentationContract.lean` still passes
(`E4-SCHEMA-CE-027`). It is a non-recursive constructor match, so each of its
twenty-two equations holds by `rfl`.

`cases_census` is the constructor cap. The exact-recursor device the tag packet
uses is unavailable here: Lean generates the recursor of a nested mutual
inductive with one extra motive per nested container instance, and that motive
list is an elaborator detail rather than a contracted API. A twenty-two-fold
existential disjunction achieves the one property wanted — a twenty-third
constructor makes it unprovable — and depends on nothing generated. It is
weaker in one recorded respect: it fixes the constructor *set*, not the
constructor *order*.
-/

/-- The census tag of a representation node. -/
def Representation.tag : Representation → RepresentationTag
  | .declaration _ _ _ _ => .declaration
  | .reference _ => .reference
  | .suspend _ _ _ => .suspend
  | .null _ _ => .null
  | .undefined _ _ => .undefined
  | .void _ _ => .void
  | .never _ _ => .never
  | .unknown _ _ => .unknown
  | .any _ _ => .any
  | .string _ _ => .string
  | .number _ _ => .number
  | .boolean _ _ => .boolean
  | .bigint _ _ => .bigint
  | .symbol _ _ => .symbol
  | .literal _ _ _ => .literal
  | .uniqueSymbol _ _ _ => .uniqueSymbol
  | .objectKeyword _ _ => .objectKeyword
  | .enum _ _ _ => .enum
  | .templateLiteral _ _ _ => .templateLiteral
  | .arrays _ _ _ _ => .arrays
  | .objects _ _ _ _ => .objects
  | .union _ _ _ _ => .union

/-- The census tag of a check node. -/
def Check.tag : Check → CheckTag
  | .filter _ _ _ => .filter
  | .filterGroup _ _ _ => .filterGroup

/-- A representation witnessing each census tag, used only for surjectivity. -/
private def Representation.tagWitness : RepresentationTag → Representation
  | .declaration => Representation.declaration ⟨"", Json.null⟩ none [] []
  | .reference => Representation.reference ⟨""⟩
  | .suspend => Representation.suspend none [] (Representation.never none [])
  | .null => Representation.null none []
  | .undefined => Representation.undefined none []
  | .void => Representation.void none []
  | .never => Representation.never none []
  | .unknown => Representation.unknown none []
  | .any => Representation.any none []
  | .string => Representation.string none []
  | .number => Representation.number none []
  | .boolean => Representation.boolean none []
  | .bigint => Representation.bigint none []
  | .symbol => Representation.symbol none []
  | .literal => Representation.literal none [] (LiteralValue.boolean false)
  | .uniqueSymbol => Representation.uniqueSymbol none [] ⟨""⟩
  | .objectKeyword => Representation.objectKeyword none []
  | .enum => Representation.enum none [] []
  | .templateLiteral => Representation.templateLiteral none [] []
  | .arrays => Representation.arrays none [] [] []
  | .objects => Representation.objects none [] [] []
  | .union => Representation.union none [] [] UnionMode.anyOf

/-- The tag projection is surjective onto the frozen representation alphabet. -/
theorem Representation.tag_surjective (tag : RepresentationTag) :
    ∃ representation : Representation, Representation.tag representation = tag :=
  ⟨Representation.tagWitness tag, by cases tag <;> rfl⟩

/-- The tag projection is surjective onto the frozen check alphabet. -/
theorem Check.tag_surjective (tag : CheckTag) :
    ∃ check : Check, Check.tag check = tag := by
  cases tag with
  | filter => exact ⟨Check.filter ⟨"", Json.null, none⟩ none false, rfl⟩
  | filterGroup => exact ⟨Check.filterGroup none none [], rfl⟩

/--
The constructor cap: every representation is one of exactly twenty-two shapes.

A twenty-third constructor makes this unprovable. It fixes the constructor set
and not the constructor order.
-/
theorem Representation.cases_census (representation : Representation) :
    (∃ (rep : RepresentationAnnotation) (ann : Annotations)
        (tps : List Representation) (cs : List Check),
        representation = Representation.declaration rep ann tps cs) ∨
    (∃ (key : ReferenceKey), representation = Representation.reference key) ∨
    (∃ (ann : Annotations) (cs : List Check) (thunk : Representation),
        representation = Representation.suspend ann cs thunk) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.null ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.undefined ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.void ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.never ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.unknown ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.any ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.string ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.number ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.boolean ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.bigint ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.symbol ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check) (lit : LiteralValue),
        representation = Representation.literal ann cs lit) ∨
    (∃ (ann : Annotations) (cs : List Check) (sym : GlobalSymbolKey),
        representation = Representation.uniqueSymbol ann cs sym) ∨
    (∃ (ann : Annotations) (cs : List Check),
        representation = Representation.objectKeyword ann cs) ∨
    (∃ (ann : Annotations) (cs : List Check) (es : List EnumEntry),
        representation = Representation.enum ann cs es) ∨
    (∃ (ann : Annotations) (cs : List Check) (ps : List Representation),
        representation = Representation.templateLiteral ann cs ps) ∨
    (∃ (ann : Annotations) (cs : List Check) (els : List (ElementOf Representation))
        (rs : List Representation),
        representation = Representation.arrays ann cs els rs) ∨
    (∃ (ann : Annotations) (cs : List Check)
        (props : List (PropertySignatureOf Representation))
        (idxs : List (IndexSignatureOf Representation)),
        representation = Representation.objects ann cs props idxs) ∨
    (∃ (ann : Annotations) (cs : List Check) (ts : List Representation)
        (md : UnionMode),
        representation = Representation.union ann cs ts md) := by
  cases representation <;> simp

/-- The constructor cap for checks. -/
theorem Check.cases_census (check : Check) :
    (∃ (rep : CheckRepresentationAnnotationOf Representation) (ann : Annotations)
        (aborted : Bool), check = Check.filter rep ann aborted) ∨
    (∃ (rep : Option (CheckRepresentationAnnotationOf Representation))
        (ann : Annotations) (cs : List Check),
        check = Check.filterGroup rep ann cs) := by
  cases check
  case filter => exact Or.inl ⟨_, _, _, rfl⟩
  case filterGroup => exact Or.inr ⟨_, _, _, rfl⟩

/--
Absent and empty annotations build distinct carrier values.

`pruneAnnotations` omits the key when nothing survives while decode passes `{}`
through unchanged, so the two are distinct raw states with one canonical form. A
carrier that collapsed them would leave `SC-WIRE-04` nothing to normalize and
make `SC-WIRE-03` unstatable. `E4-SCHEMA-CE-036`.
-/
theorem Representation.absent_ne_empty_annotations :
    Representation.never none [] ≠ Representation.never (some []) [] := by
  intro equal
  injection equal with annotationsEqual _
  exact absurd annotationsEqual (by simp)

end Effect4
