import Effect4.Schema.Check

/-!
# Schema authoring conveniences

Small constructors over the canonical raw Schema carriers. This module does
not define a second schema AST or executable predicate language.
-/

namespace Effect4.Schema

universe u v

/-! ## Higher-order executable predicates -/

/-- Derive an executable Boolean predicate from a decidable proposition. -/
def Predicate.decide {α : Type u} (property : α → Prop) [DecidablePred property] : α → Bool :=
  fun value => if property value then true else false

/-- The derived Boolean predicate reflects its proposition. -/
theorem Predicate.decide_iff {α : Type u} (property : α → Prop) [DecidablePred property]
    (value : α) :
    Predicate.decide property value = true ↔ property value := by
  simp [Predicate.decide]

/-- Conjunction of executable predicates. -/
def Predicate.and {α : Type u} (left right : α → Bool) : α → Bool :=
  fun value => left value && right value

/-- Disjunction of executable predicates. -/
def Predicate.or {α : Type u} (left right : α → Bool) : α → Bool :=
  fun value => left value || right value

/-- Negation of an executable predicate. -/
def Predicate.not {α : Type u} (predicate : α → Bool) : α → Bool :=
  fun value => !predicate value

/-- Read a predicate through a projection. This is the usual contravariant
composition operation and is the basis for derived field predicates. -/
def Predicate.contramap {α : Type u} {β : Type v}
    (project : β → α) (predicate : α → Bool) : β → Bool :=
  fun value => predicate (project value)

/-- Every predicate in an ordered list must hold. -/
def Predicate.all {α : Type u} (predicates : List (α → Bool)) : α → Bool :=
  fun value => predicates.all fun predicate => predicate value

/-- At least one predicate in an ordered list must hold. -/
def Predicate.any {α : Type u} (predicates : List (α → Bool)) : α → Bool :=
  fun value => predicates.any fun predicate => predicate value

/-- Lift an element predicate to every member of a list. -/
def Predicate.each {α : Type u} (predicate : α → Bool) : List α → Bool :=
  fun values => values.all predicate

/-- Execute a higher-order predicate. Kept as a named boundary so authoring
code reads `Schema.check predicate value`. -/
def check {α : Type u} (predicate : α → Bool) (value : α) : Bool := predicate value

theorem check_eq {α : Type u} (predicate : α → Bool) (value : α) :
    check predicate value = predicate value := rfl

theorem Predicate.and_eq_true {α : Type u} (left right : α → Bool) (value : α) :
    Predicate.and left right value = true ↔
      left value = true ∧ right value = true := by
  simp [Predicate.and]

theorem Predicate.or_eq_true {α : Type u} (left right : α → Bool) (value : α) :
    Predicate.or left right value = true ↔
      left value = true ∨ right value = true := by
  simp [Predicate.or]

theorem Predicate.not_eq_true {α : Type u} (predicate : α → Bool) (value : α) :
    Predicate.not predicate value = true ↔ predicate value = false := by
  simp [Predicate.not]

@[simp] theorem Predicate.contramap_apply {α : Type u} {β : Type v}
    (project : β → α) (predicate : α → Bool) (value : β) :
    Predicate.contramap project predicate value = predicate (project value) := rfl

theorem Predicate.contramap_id {α : Type u} (predicate : α → Bool) :
    Predicate.contramap id predicate = predicate := by
  funext value
  rfl

theorem Predicate.contramap_comp {α : Type u} {β : Type v} {γ : Type _}
    (first : β → α) (second : γ → β) (predicate : α → Bool) :
    Predicate.contramap second (Predicate.contramap first predicate) =
      Predicate.contramap (first ∘ second) predicate := by
  funext value
  rfl

theorem Predicate.all_eq_true {α : Type u}
    (predicates : List (α → Bool)) (value : α) :
    Predicate.all predicates value = true ↔
      ∀ predicate ∈ predicates, predicate value = true := by
  simp [Predicate.all]

theorem Predicate.any_eq_true {α : Type u}
    (predicates : List (α → Bool)) (value : α) :
    Predicate.any predicates value = true ↔
      ∃ predicate ∈ predicates, predicate value = true := by
  simp [Predicate.any]

theorem Predicate.each_eq_true {α : Type u}
    (predicate : α → Bool) (values : List α) :
    Predicate.each predicate values = true ↔
      ∀ value ∈ values, predicate value = true := by
  simp [Predicate.each]

/-! ## Registered, persisted check descriptions -/

/-- A persisted, registered predicate description.

The `id` selects a host reviver and the payload is its first-order argument.
This value does not itself execute a Lean predicate. -/
def Check.named (id : String) (payload : Json := .null)
    (schemas : Option (List Representation) := none)
    (annotations : Annotations := none) (aborted : Bool := false) : Check :=
  .filter { id, payload, schemas } annotations aborted

/-- Group one or more predicate descriptions without inventing a second check
carrier. -/
def Check.group (first : Check) (rest : List Check := [])
    (annotations : Annotations := none)
    (representation : Option CheckRepresentationAnnotation := none) : Check :=
  .filterGroup representation annotations (first :: rest)

def Check.trimmed : Check := Check.named "effect/schema/isTrimmed"
def Check.stringFinite : Check := Check.named "effect/schema/isStringFinite"
def Check.stringBigInt : Check := Check.named "effect/schema/isStringBigInt"
def Check.stringSymbol : Check := Check.named "effect/schema/isStringSymbol"
def Check.finite : Check := Check.named "effect/schema/isFinite"
def Check.int : Check := Check.named "effect/schema/isInt"
def Check.uppercased : Check := Check.named "effect/schema/isUppercased"
def Check.lowercased : Check := Check.named "effect/schema/isLowercased"
def Check.capitalized : Check := Check.named "effect/schema/isCapitalized"
def Check.uncapitalized : Check := Check.named "effect/schema/isUncapitalized"
def Check.unique : Check := Check.named "effect/schema/isUnique"

def Check.pattern (source : String) (flags : String := "") : Check :=
  Check.named "effect/schema/isPattern"
    (.obj [("source", .str source), ("flags", .str flags)])

def Check.startsWith (start : String) : Check :=
  Check.named "effect/schema/isStartsWith" (.obj [("startsWith", .str start)])

def Check.endsWith (suffix : String) : Check :=
  Check.named "effect/schema/isEndsWith" (.obj [("endsWith", .str suffix)])

def Check.includes (substring : String) : Check :=
  Check.named "effect/schema/isIncludes" (.obj [("includes", .str substring)])

/-! ## Raw representation constructors -/

def null : Representation := .null none []
def undefined : Representation := .undefined none []
def void : Representation := .void none []
def never : Representation := .never none []
def unknown : Representation := .unknown none []
def any : Representation := .any none []
def string : Representation := .string none []
def number : Representation := .number none []
def boolean : Representation := .boolean none []
def bigint : Representation := .bigint none []
def symbol : Representation := .symbol none []
def objectKeyword : Representation := .objectKeyword none []

def literal (value : LiteralValue) : Representation := .literal none [] value
def literalString (value : String) : Representation := literal (.string value)
def literalNumber (value : Float64) : Representation := literal (.number value)
def literalBigInt (value : Int) : Representation := literal (.bigint value)
def literalBoolean (value : Bool) : Representation := literal (.boolean value)

def globalSymbol (key : String) : Representation :=
  .uniqueSymbol none [] ⟨key⟩

/-- Effect's ordinary homogeneous array spelling: no fixed elements and one
rest representation. -/
def array (item : Representation) : Representation :=
  .arrays none [] [] [item]

/-- An ordered tuple. Empty and otherwise unusual raw shapes remain
representable; field admission and later denotation decide them. -/
def tuple (elements : List Element) (rest : List Representation := []) : Representation :=
  .arrays none [] elements rest

def element (type : Representation) (isOptional : Bool := false)
    (annotations : Annotations := none) : Element :=
  { isOptional, type, annotations }

def property (name : String) (type : Representation)
    (isOptional : Bool := false) (isMutable : Bool := false)
    (annotations : Annotations := none) : PropertySignature :=
  { name := .string name, type, isOptional, isMutable, annotations }

def index (parameter type : Representation) : IndexSignature :=
  { parameter, type }

def struct (properties : List PropertySignature)
    (indexes : List IndexSignature := []) : Representation :=
  .objects none [] properties indexes

def anyOf (first : Representation) (rest : List Representation := []) : Representation :=
  .union none [] (first :: rest) .anyOf

/-- A tagged struct: the discriminant `_tag` first, a required string literal, then the
fields. This is the one shape every target spells as a case of a sum type
(`docs/research/2026-09-04-codegen-api-design.md` §7.2). -/
def tagged (tag : String) (properties : List PropertySignature) : Representation :=
  struct (property "_tag" (literalString tag) :: properties)

/-- A sum type: the `anyOf` of one tagged struct per case, in declaration order. -/
def variant (cases : List (String × List PropertySignature)) : Representation :=
  .union none [] (cases.map fun case => tagged case.1 case.2) .anyOf

def oneOf (first : Representation) (rest : List Representation := []) : Representation :=
  .union none [] (first :: rest) .oneOf

def reference (key : String) : Representation := .reference ⟨key⟩

def suspend (thunk : Representation) : Representation := .suspend none [] thunk

def document (representation : Representation)
    (references : List ReferenceEntry := []) : Document :=
  { representation, references }

/-! ## Check attachment -/

/-- Append checks when the persisted node has an unconstrained `checks` field.

`Reference` has no such field and `Suspend` requires it to remain empty, so
both return `none`. -/
def withChecks? (newChecks : List Check) : Representation → Option Representation
  | .declaration rep ann tps checks =>
      some (.declaration rep ann tps (checks ++ newChecks))
  | .reference _ => none
  | .suspend _ _ _ => none
  | .null ann checks => some (.null ann (checks ++ newChecks))
  | .undefined ann checks => some (.undefined ann (checks ++ newChecks))
  | .void ann checks => some (.void ann (checks ++ newChecks))
  | .never ann checks => some (.never ann (checks ++ newChecks))
  | .unknown ann checks => some (.unknown ann (checks ++ newChecks))
  | .any ann checks => some (.any ann (checks ++ newChecks))
  | .string ann checks => some (.string ann (checks ++ newChecks))
  | .number ann checks => some (.number ann (checks ++ newChecks))
  | .boolean ann checks => some (.boolean ann (checks ++ newChecks))
  | .bigint ann checks => some (.bigint ann (checks ++ newChecks))
  | .symbol ann checks => some (.symbol ann (checks ++ newChecks))
  | .literal ann checks value => some (.literal ann (checks ++ newChecks) value)
  | .uniqueSymbol ann checks key => some (.uniqueSymbol ann (checks ++ newChecks) key)
  | .objectKeyword ann checks => some (.objectKeyword ann (checks ++ newChecks))
  | .enum ann checks entries => some (.enum ann (checks ++ newChecks) entries)
  | .templateLiteral ann checks parts =>
      some (.templateLiteral ann (checks ++ newChecks) parts)
  | .arrays ann checks elements rest =>
      some (.arrays ann (checks ++ newChecks) elements rest)
  | .objects ann checks properties indexes =>
      some (.objects ann (checks ++ newChecks) properties indexes)
  | .union ann checks types mode =>
      some (.union ann (checks ++ newChecks) types mode)

/-- Effect-style convenience: attach a non-empty ordered list of checks. -/
def withCheck (representation : Representation) (first : Check)
    (rest : List Check := []) : Option Representation :=
  withChecks? (first :: rest) representation

theorem withCheck_reference (key : String) (first : Check) (rest : List Check) :
    withCheck (reference key) first rest = none := rfl

theorem withCheck_suspend (thunk : Representation) (first : Check) (rest : List Check) :
    withCheck (suspend thunk) first rest = none := rfl

theorem withCheck_string (first : Check) (rest : List Check) :
    withCheck string first rest = some (.string none (first :: rest)) := by
  simp [withCheck, withChecks?, string]

end Effect4.Schema
