import Effect4.Program.Typing
import Effect4.Program.Eff
import Effect4.Schema.Authoring
import Effect4.Schema.Document
import Effect4.Schema.Payload

/-!
# Effect4.Schema.Bridge — Program Type to Schema Representation Bridge (S-1 / S-2)

This module implements Decision 12 (S-1, S-2) from `docs/research/2026-09-10-schema-at-boundaries.md`:
1. `Ty.schema : Ty → Representation`: Lowering any program type into an rc.112 `SchemaRepresentation`.
2. `Ty.ofSchema : Representation → Option Ty`: Partial inverse recovering the first-order program type.
3. `ofSchema_schema`: Constructive retraction theorem proving `ofSchema (schema t) = some t` for all types.
4. `EffTy.document` & `Row.document`: As-an-effect and as-a-plain-object schema documents for program boundaries.

Per findings from Seat A and Seat B:
* `Ty.nat` is distinguished from `Ty.int` via `isGreaterThanOrEqualTo 0` (`Check.nonNegative`).
* `Ty.fiberOf` preserves type arguments in its declaration node without host encoding.
* The retraction theorem holds constructively over all 16 `Ty` constructors at `[propext]`.
-/

namespace Effect4.Schema.Bridge

open Effect4 Effect4.Program Effect4.Schema

/-- Persisted check selecting rc.112 integer refinement (`isInt`). -/
def isIntCheck : Check := Check.named "effect/schema/isInt"

/-- Persisted check selecting non-negative integers (`isGreaterThanOrEqualTo 0`). -/
def nonNegativeCheck : Check :=
  Check.named "effect/schema/isGreaterThanOrEqualTo" (.obj [("minimum", .number Float64.zero)])

/-- The rc.112 `Defect` declaration schema node (`Schema.ts:10844`). -/
def defectRep : Representation :=
  .declaration ⟨"effect/schema/Defect", .null⟩ none [] []

/-- Lowers any first-order `Ty` into its canonical rc.112 `SchemaRepresentation`. -/
def schema : Ty → Representation
  | .never => Schema.never
  | .unit => Schema.void
  | .nat => .number none [isIntCheck, nonNegativeCheck]
  | .int => .number none [isIntCheck]
  | .string => Schema.string
  | .bool => Schema.boolean
  | .lit s => Schema.literalString s
  | .handle target => .declaration ⟨target, .null⟩ none [] []
  | .option inner => .declaration ⟨"effect/schema/Option", .null⟩ none [schema inner] []
  | .list inner => Schema.array (schema inner)
  | .prod left right => Schema.tuple [Schema.element (schema left), Schema.element (schema right)]
  | .except error value => .declaration ⟨"effect/schema/Result", .null⟩ none [schema value, schema error] []
  | .exitOf value error => .declaration ⟨"effect/schema/Exit", .null⟩ none [schema value, schema error, defectRep] []
  | .causeOf error => .declaration ⟨"effect/schema/Cause", .null⟩ none [schema error, defectRep] []
  | .fiberOf value error => .declaration ⟨"effect/schema/Fiber", .null⟩ none [schema value, schema error] []
  | .union left right => .union none [] [schema left, schema right] .anyOf

/-- Extracts the identifier of a persisted check. -/
def checkId : Check → String
  | .filter rep _ _ => rep.id
  | .filterGroup (some rep) _ _ => rep.id
  | .filterGroup none _ _ => ""

/-- The defect slot of an `Exit` or `Cause` declaration is the `Defect` declaration `schema` mints
(`defectRep`), nothing else. -/
def isDefect : Representation → Bool
  | .declaration ⟨"effect/schema/Defect", .null⟩ _ [] [] => true
  | _ => false

/-- Reconstitutes a first-order `Ty` from an rc.112 `SchemaRepresentation` (decisions row 6):
exactly the nodes `schema` mints, modulo annotations. A node with checks `schema` does not mint
(`number`'s two, nothing else), a declaration whose payload is not `null`, a declaration whose
defect slot is not the `Defect` declaration, an optional or annotated tuple element, is refused
— `Ty` cannot represent it, and answering would widen the read into something `schema` never
writes. Annotations are not read: `ofSchema r = some t` says `r` is `schema t` up to them. -/
def ofSchema : Representation → Option Ty
  | .never _ [] => some .never
  | .void _ [] => some .unit
  | .number _ checks =>
    match checks.map checkId with
    | ["effect/schema/isInt", "effect/schema/isGreaterThanOrEqualTo"] => some .nat
    | ["effect/schema/isInt"] => some .int
    | _ => none
  | .string _ [] => some .string
  | .boolean _ [] => some .bool
  | .literal _ [] (.string s) => some (.lit s)
  | .declaration ⟨id, .null⟩ _ [val] [] =>
    if id == "effect/schema/Option" then do
      let t ← ofSchema val
      some (.option t)
    else none
  | .declaration ⟨id, .null⟩ _ [a, b] [] =>
    if id == "effect/schema/Result" then do
      let tv ← ofSchema a
      let te ← ofSchema b
      some (.except te tv)
    else if id == "effect/schema/Fiber" then do
      let tv ← ofSchema a
      let te ← ofSchema b
      some (.fiberOf tv te)
    else if id == "effect/schema/Cause" && isDefect b then do
      let te ← ofSchema a
      some (.causeOf te)
    else none
  | .declaration ⟨id, .null⟩ _ [val, err, defect] [] =>
    if id == "effect/schema/Exit" && isDefect defect then do
      let tv ← ofSchema val
      let te ← ofSchema err
      some (.exitOf tv te)
    else none
  | .declaration ⟨id, .null⟩ _ [] [] =>
    some (.handle id)
  | .arrays _ [] [] [item] => do
    let t ← ofSchema item
    some (.list t)
  | .arrays _ [] [⟨false, a, none⟩, ⟨false, b, none⟩] [] => do
    let ta ← ofSchema a
    let tb ← ofSchema b
    some (.prod ta tb)
  | .union _ [] [a, b] .anyOf => do
    let ta ← ofSchema a
    let tb ← ofSchema b
    some (.union ta tb)
  | _ => none

/-- Q5 Retraction Theorem: `ofSchema` is a left inverse to `schema` across all 16 `Ty` constructors
(`schema` mints no checks but `number`'s, `null` payloads, plain elements, so every guard passes). -/
theorem ofSchema_schema (t : Ty) : ofSchema (schema t) = some t := by
  induction t with
  | never => rfl
  | unit => rfl
  | nat => rfl
  | int => rfl
  | string => rfl
  | bool => rfl
  | lit s => rfl
  | handle target => rfl
  | option inner ih =>
    dsimp [schema, ofSchema]
    rw [ih]
    rfl
  | list inner ih =>
    dsimp [schema, ofSchema, Schema.array]
    rw [ih]
    rfl
  | prod a b iha ihb =>
    dsimp [schema, ofSchema, Schema.tuple, Schema.element]
    rw [iha, ihb]
    rfl
  | except e a ihe iha =>
    dsimp [schema, ofSchema]
    rw [iha, ihe]
    rfl
  | exitOf a e iha ihe =>
    dsimp [schema, ofSchema]
    rw [iha, ihe]
    rfl
  | causeOf e ihe =>
    dsimp [schema, ofSchema]
    rw [ihe]
    rfl
  | fiberOf a e iha ihe =>
    dsimp [schema, ofSchema]
    rw [iha, ihe]
    rfl
  | union a b iha ihb =>
    dsimp [schema, ofSchema]
    rw [iha, ihb]
    rfl

/-- Retraction over canonical types `CTy`. -/
theorem ofSchema_schema_cty (t : CTy) : ofSchema (schema t.toRaw) = some t.toRaw :=
  ofSchema_schema t.toRaw

/-- As an effect: the exit schema root with answer, error, and requirement references (S-2). -/
def effDocument (eff : EffTy) : Document :=
  { representation := schema (.exitOf eff.answer.normalize eff.error.normalize)
    references :=
      [ ⟨"answer", schema eff.answer.normalize⟩
      , ⟨"error", schema eff.error.normalize⟩ ] ++
      eff.requires.elems.map (fun k => ⟨s!"service_{k.name.value}", schema (.handle s!"service_{k.name.value}")⟩) }

/-- As a plain object: the answer schema alone (S-2). -/
def effObjectDocument (eff : EffTy) : Document :=
  { representation := schema eff.answer.normalize
    references := [] }

/-- A row's schema document: request, answer, and error (S-2). -/
def rowDocument (row : Effect4.Program.Row) : Document :=
  { representation := schema (.exitOf row.answer.normalize row.error.normalize)
    references :=
      [ ⟨"request", schema row.request.normalize⟩
      , ⟨"answer", schema row.answer.normalize⟩
      , ⟨"error", schema row.error.normalize⟩ ] }

end Effect4.Schema.Bridge

namespace Effect4.Program.Ty

/-- Effect Schema representation of this type (Decision 12 / S-1). -/
abbrev schema (t : Effect4.Program.Ty) : Effect4.Representation :=
  Effect4.Schema.Bridge.schema t.normalize

/-- Reconstitute a `Ty` from its Effect Schema representation (Decision 12 / S-1). -/
abbrev ofSchema (r : Effect4.Representation) : Option Effect4.Program.Ty :=
  Effect4.Schema.Bridge.ofSchema r

end Effect4.Program.Ty

namespace Effect4.Program.EffTy

/-- As an effect: the Schema Document describing running this program (Exit with requirements). -/
abbrev document (eff : Effect4.Program.EffTy) : Effect4.Document :=
  Effect4.Schema.Bridge.effDocument eff

end Effect4.Program.EffTy

namespace Effect4.Program.Row

/-- Schema Document describing the request, answer, and error of this operation row. -/
abbrev document (row : Effect4.Program.Row) : Effect4.Document :=
  Effect4.Schema.Bridge.rowDocument row

end Effect4.Program.Row

namespace Effect4.Program.CTy

/-- Schema projection of a canonical type. -/
def schema (t : CTy) : Effect4.Representation := Ty.schema t.toRaw

/-- The public schema boundary retracts on canonical types; integer parsing is retained. -/
theorem ofSchema_schema (t : CTy) : Ty.ofSchema (schema t) = some t.toRaw := by
  change Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema t.val.normalize) = _
  rw [t.property]
  exact Effect4.Schema.Bridge.ofSchema_schema t.toRaw

end Effect4.Program.CTy
