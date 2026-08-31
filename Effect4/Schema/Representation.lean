import Std

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
