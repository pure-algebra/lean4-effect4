import Effect4.Program.Typing
import Effect4.Program.Eff
import Effect4.Program.Fold
import Effect4.Schema.Authoring
import Effect4.Schema.Document
import Effect4.Schema.Fold
import Effect4.Schema.Payload

/-!
# Effect4.Schema.Bridge — Program Type to Schema Representation Bridge (S-1 / S-2)

This module implements Decision 12 (S-1, S-2) from `docs/research/2026-09-10-schema-at-boundaries.md`:
1. `Ty.schema : Ty → Representation`: Lowering any program type into an rc.112 `SchemaRepresentation`.
2. `Ty.ofSchema : Representation → Option Ty`: the reader, recovering the first-order program type.
3. `ofSchema_schema`: raw retraction on closed types in `reservedFree`'s exact profile.
   The profile excludes unsupported nodes, nonstring map keys, the two-item tuple alias, and the reserved handle id.
4. `ofSchema_exact`: exactness (decisions row 128): `ofSchema r = some t → normS r = schema t`, so
   the pair is an exact embedding modulo `normS` (`N_S`, a fold), not a retraction alone.
5. `EffTy.document` & `Row.document`: As-an-effect and as-a-plain-object schema documents for program boundaries.

Per findings from Seat A and Seat B:
* `Ty.nat` is distinguished from `Ty.int` via `isGreaterThanOrEqualTo 0` (`Check.nonNegative`).
* `Ty.fiberOf` preserves type arguments in its declaration node without host encoding.

Exactness is stated at the bridge (`schema`, `ofSchema` on raw types), where `schema` writes and
`ofSchema` reads one order, so `N_S` reorders nothing. The public writer `Ty.schema` normalizes the
type first; a statement against it would need `N_S` to sort and to reorder union members, which
rc.112's ordered `anyOf` observes (probe S, `docs/research/2026-10-01-type-language-probe/S/note.md`
§1.1). The proofs are seat P's (`.../P/probes/P8Schema.lean`, on today's functions), with row 179's
annotation policy (amended twice on 2026-10-01: a check's annotations too, and `arbitrary` erased)
in place of the probe's; the proofs read only `normAnn none = none` and the guard, so the key list
can change without touching them.
-/

namespace Effect4.Schema.Bridge

open Effect4 Effect4.Program Effect4.Schema

/-- Persisted check selecting rc.112 integer refinement (`isInt`, `Schema.ts:8298-8304`). -/
def isIntCheck : Check := Check.named "effect/schema/isInt"

/-- Persisted check selecting non-negative integers (`isGreaterThanOrEqualTo 0`). -/
def nonNegativeCheck : Check :=
  Check.named "effect/schema/isGreaterThanOrEqualTo" (.obj [("minimum", .number Float64.zero)])

/-- The defect slot of rc.112's `Exit` and `Cause` documents. `Schema.Defect()` is a transformation
over `Schema.Json` (`Schema.ts:10844-10853`) and persists as the `Json` declaration
(`SchemaAST.ts:4352-4362`, id `effect/schema/Json`; tested under bun by probe S,
`docs/research/2026-10-01-type-language-probe/S/host/logs/q4-defect.log`). Until 2026-10-01 this
node named `effect/schema/Defect`, an id rc.112 never writes: rc.112 could not revive Lean's
`Exit`/`Cause` documents and `ofSchema` refused rc.112's own (`E4-SCHEMA-CE-061`). -/
def defectRep : Representation :=
  .declaration ⟨"effect/schema/Json", .null⟩ none [] []

/-- The declaration the bridge writes for a data-wave form it does not lower yet (decisions row
162: every appended constructor is refused by name until its Schema commit). `reservedFree` is
false at each, so the retraction never claims one. Its payload is not `null`, which every
declaration arm of `ofSchema` demands, so the marker never reads back as the handle of its name
and a handle of that name keeps its own image (Codex, unlowered-boundary review). -/
def unlowered (head : String) : Representation :=
  .declaration ⟨"effect4/unlowered/" ++ head, .str "unlowered"⟩ none [] []

/-- The Schema algebra has one field for every type constructor. -/
def schemaAlg : TyAlgebra (fun _ => Representation) where
  ty_never := Schema.never
  ty_unknown := .unknown none []
  ty_unit := Schema.void
  ty_nat := .number none [isIntCheck, nonNegativeCheck]
  ty_int := .number none [isIntCheck]
  ty_string := Schema.string
  ty_bool := Schema.boolean
  ty_lit s := Schema.literalString s
  ty_handle target := .declaration ⟨target, .null⟩ none [] []
  ty_option inner := .declaration ⟨"effect/schema/Option", .null⟩ none [inner] []
  ty_list inner := Schema.array inner
  ty_prod left right := Schema.tuple [Schema.element left, Schema.element right]
  ty_except error value := .declaration ⟨"effect/schema/Result", .null⟩ none [value, error] []
  ty_exitOf value error := .declaration ⟨"effect/schema/Exit", .null⟩ none [value, error, defectRep] []
  ty_causeOf error := .declaration ⟨"effect/schema/Cause", .null⟩ none [error, defectRep] []
  ty_fiberOf value error := .declaration ⟨"effect/schema/Fiber", .null⟩ none [value, error] []
  ty_refOf value := .declaration ⟨"effect/schema/Ref", .null⟩ none [value] []
  ty_deferredOf value error := .declaration ⟨"effect/schema/Deferred", .null⟩ none [value, error] []
  ty_var _ := .declaration ⟨"effect/schema/TypeParameter", .null⟩ none [] []
  ty_union left right := .union none [] [left, right] .anyOf
  ty_record fields := Schema.struct (fields.map fun field =>
    Schema.property field.1 field.2.2 field.2.1)
  ty_map key value := Schema.struct [] [Schema.index key value]
  ty_tuple items := Schema.tuple (items.map fun item => Schema.element item)
  ty_app _ _ := unlowered "app"
  ty_null := unlowered "null"
  ty_undefined := unlowered "undefined"
  ty_number := unlowered "number"
  ty_bytes := unlowered "bytes"

/-- Write a type through the generated fold. The public writer normalizes first. -/
def schema (t : Ty) : Representation := cata_ty schemaAlg t

/-- The record fold retains raw declaration order and each optional flag. -/
theorem schema_record (fields : List (String × Bool × Ty)) :
    schema (.record fields) = Schema.struct
      (fields.map fun field => Schema.property field.1 (schema field.2.2) field.2.1) := by
  rw [schema, cata_ty_record]
  simp only [schemaAlg, List.map_map, Function.comp_def, prodMapSnd]
  rfl

/-- The tuple fold retains the complete ordered child list. -/
theorem schema_tuple (items : List Ty) :
    schema (.tuple items) = Schema.tuple (items.map fun item => Schema.element (schema item)) := by
  rw [schema, cata_ty_tuple]
  simp only [schemaAlg, List.map_map, Function.comp_def]
  rfl

/-- Extracts the identifier of a persisted check. The reader no longer reads a check by its id
(row 128: it compares whole checks); this stays the id projection the fold census registers
(`Laws/Program/Folds/Representation.lean`) and the red control of the id reading uses. -/
def checkId : Check → String
  | .filter rep _ _ => rep.id
  | .filterGroup (some rep) _ _ => rep.id
  | .filterGroup none _ _ => ""

/-! ## `N_S`: the annotation policy and the normaliser (decisions rows 128, 179)

One policy for the normaliser and the reader's guard (row 179, ruled 2026-10-01; amended the same
day twice: a check's annotations are covered, and `arbitrary` is erased). The principle: an
annotation that does not change decoding is erased, one that does (or that is unknown) is refused.
The erased keys are revision 5's eight documentation keys
(`docs/research/2026-10-01-type-language-probe/S-inputs/revision-5/annotation-review.md`: rc.112
reads them for diagnostics, references and documentation, never for acceptance or decoded values)
and `arbitrary`, a fast-check generator hint with no decoding meaning, which rc.112's own
`Schema.Int` writes on its `isInt` filter (probe S, E9d). `normAnn` erases those entries and keeps
every other entry, and a bag left empty is `none`; the reader admits a bag only when nothing is left
(`normAnn ann = none`), at every bag it reads: each node, each check, each tuple element, the defect
slot. Every other key, `parseOptions` among them, is refused. `normS` applies `normAnn` to every bag
of the tree, checks and properties included, and changes nothing else. -/

/-- The annotation keys that change nothing rc.112 accepts or decodes, erased by `N_S` (row 179:
revision 5's eight documentation keys, seat S's allowlist, and `arbitrary`, the ninth, a generator
hint rc.112's own `Schema.Int` writes). -/
def erasedKeys : List String :=
  ["identifier", "title", "description", "documentation", "examples", "default", "message",
   "expected", "arbitrary"]

/-- An annotation bag modulo the erased keys: those entries erased, the rest kept in order, an
empty remainder `none` (so an absent bag and a bag of erased keys only are one). -/
def normAnn : Annotations → Annotations
  | none => none
  | some entries =>
    match entries.filter (fun e => !erasedKeys.contains e.key) with
    | [] => none
    | rest => some rest

/-- A tuple element with its annotation bag normalised. -/
def normElement (e : ElementOf Representation) : ElementOf Representation :=
  { e with annotations := normAnn e.annotations }

/-- A property signature with its annotation bag normalised. -/
def normProperty (p : PropertySignatureOf Representation) : PropertySignatureOf Representation :=
  { p with annotations := normAnn p.annotations }

/-- `N_S`'s algebra: every node, check, element and property rebuilt with its annotation bag
normalised; nothing else changes. -/
def normSAlg : RepresentationAlgebra RepresentationSelfCarrier where
  representation_declaration a0 a1 a2 a3 := .declaration a0 (normAnn a1) a2 a3
  representation_reference a0 := .reference a0
  representation_suspend a0 a1 a2 := .suspend (normAnn a0) a1 a2
  representation_null a0 a1 := .null (normAnn a0) a1
  representation_undefined a0 a1 := .undefined (normAnn a0) a1
  representation_void a0 a1 := .void (normAnn a0) a1
  representation_never a0 a1 := .never (normAnn a0) a1
  representation_unknown a0 a1 := .unknown (normAnn a0) a1
  representation_any a0 a1 := .any (normAnn a0) a1
  representation_string a0 a1 := .string (normAnn a0) a1
  representation_number a0 a1 := .number (normAnn a0) a1
  representation_boolean a0 a1 := .boolean (normAnn a0) a1
  representation_bigint a0 a1 := .bigint (normAnn a0) a1
  representation_symbol a0 a1 := .symbol (normAnn a0) a1
  representation_literal a0 a1 a2 := .literal (normAnn a0) a1 a2
  representation_uniqueSymbol a0 a1 a2 := .uniqueSymbol (normAnn a0) a1 a2
  representation_objectKeyword a0 a1 := .objectKeyword (normAnn a0) a1
  representation_enum a0 a1 a2 := .enum (normAnn a0) a1 a2
  representation_templateLiteral a0 a1 a2 := .templateLiteral (normAnn a0) a1 a2
  representation_arrays a0 a1 a2 a3 := .arrays (normAnn a0) a1 (a2.map normElement) a3
  representation_objects a0 a1 a2 a3 := .objects (normAnn a0) a1 (a2.map normProperty) a3
  representation_union a0 a1 a2 a3 := .union (normAnn a0) a1 a2 a3
  check_filter a0 a1 a2 := .filter a0 (normAnn a1) a2
  check_filterGroup a0 a1 a2 := .filterGroup a0 (normAnn a1) a2

/-- **`N_S`**, a fold: a representation modulo the annotation entries that change no decoding. -/
def normS (r : Representation) : Representation := cata_representation normSAlg r

/-- A check modulo the erased keys: `N_S`'s check arm. The reader compares a check with `schema`'s
bare checks after this, so a documented `isInt`, or rc.112's own with `arbitrary`, is `isInt`. -/
def normCheck (c : Check) : Check := cata_check normSAlg c

/-! ## The reader -/

/-- The defect slot of an `Exit` or `Cause` declaration is the `Json` declaration `schema` mints
(`defectRep`), with an annotation bag of erased keys only (rc.112 writes `expected` there); nothing
else. -/
def isDefect : Representation → Bool
  | .declaration ⟨"effect/schema/Json", .null⟩ ann [] [] => decide (normAnn ann = none)
  | _ => false

/-- Read a plain string property after reading its child type. -/
def readProperty (name : PropertyKey) (optional mutable : Bool) (ann : Annotations)
    (child : Option Ty) : Option (String × Bool × Ty) :=
  match name with
  | .string key =>
    if mutable = false ∧ normAnn ann = none then child.map (fun ty => (key, optional, ty))
    else none
  | _ => none

/-- Read a required plain tuple element after reading its child type. -/
def readElement (optional : Bool) (ann : Annotations) (child : Option Ty) : Option Ty :=
  if optional = false ∧ normAnn ann = none then child else none

/-- Reconstitutes a first-order `Ty` from an rc.112 `SchemaRepresentation` (decisions rows 6 and
128): exactly the nodes `schema` mints, modulo `N_S`. Each arm reads its annotation bag first and
refuses a key outside the erased ones (row 179). A `number`'s checks are compared whole, after
`N_S`, with the two `schema` mints (`[isInt, ≥ 0]` reads `nat`, `[isInt]` reads `int`): until row
128's commit they were read by id, so `≥ 5` read as `nat` and a filter group as `int`. The
template parameter's declaration (`effect/schema/TypeParameter`, what `schema (.var i)` writes) is
refused by name: until then it read back as a handle. A declaration whose payload is not `null`, a
defect slot that is not the `Json` declaration, an optional tuple element, a check on a node
`schema` writes without one, are refused: `Ty` cannot represent them, and answering would widen
the read into something `schema` never writes. `ofSchema r = some t` says `normS r = schema t`
(`ofSchema_exact`). -/
def ofSchema : Representation → Option Ty
  | .never ann [] => if normAnn ann = none then some .never else none
  | .unknown ann [] => if normAnn ann = none then some .unknown else none
  | .void ann [] => if normAnn ann = none then some .unit else none
  | .number ann checks =>
    if normAnn ann = none then
      if checks.map normCheck = [isIntCheck, nonNegativeCheck] then some .nat
      else if checks.map normCheck = [isIntCheck] then some .int
      else none
    else none
  | .string ann [] => if normAnn ann = none then some .string else none
  | .boolean ann [] => if normAnn ann = none then some .bool else none
  | .literal ann [] (.string s) => if normAnn ann = none then some (.lit s) else none
  | .declaration ⟨id, .null⟩ ann [val] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Option" then do
        let t ← ofSchema val
        some (.option t)
      else if id == "effect/schema/Ref" then do
        let t ← ofSchema val
        some (.refOf t)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [a, b] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Result" then do
        let tv ← ofSchema a
        let te ← ofSchema b
        some (.except te tv)
      else if id == "effect/schema/Fiber" then do
        let tv ← ofSchema a
        let te ← ofSchema b
        some (.fiberOf tv te)
      else if id == "effect/schema/Deferred" then do
        let tv ← ofSchema a
        let te ← ofSchema b
        some (.deferredOf tv te)
      else if id == "effect/schema/Cause" && isDefect b then do
        let te ← ofSchema a
        some (.causeOf te)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [val, err, defect] [] =>
    if normAnn ann = none then
      if id == "effect/schema/Exit" && isDefect defect then do
        let tv ← ofSchema val
        let te ← ofSchema err
        some (.exitOf tv te)
      else none
    else none
  | .declaration ⟨id, .null⟩ ann [] [] =>
    if normAnn ann = none then
      if id = "effect/schema/TypeParameter" then none else some (.handle id)
    else none
  | .arrays ann [] [] [item] =>
    if normAnn ann = none then do
      let t ← ofSchema item
      some (.list t)
    else none
  | .arrays ann [] [⟨false, a, annA⟩, ⟨false, b, annB⟩] [] =>
    if normAnn ann = none ∧ normAnn annA = none ∧ normAnn annB = none then do
      let ta ← ofSchema a
      let tb ← ofSchema b
      some (.prod ta tb)
    else none
  | .union ann [] [a, b] .anyOf =>
    if normAnn ann = none then do
      let ta ← ofSchema a
      let tb ← ofSchema b
      some (.union ta tb)
    else none
  | .objects ann [] properties [] =>
    if normAnn ann = none then
      (properties.mapM fun property => readProperty property.name property.isOptional
        property.isMutable property.annotations (ofSchema property.type)).map Ty.record
    else none
  | .objects ann [] [] [⟨.string keyAnn [], value⟩] =>
    if normAnn ann = none ∧ normAnn keyAnn = none then
      (ofSchema value).map (Ty.map .string)
    else none
  | .arrays ann [] elements [] =>
    if normAnn ann = none ∧ elements.length ≠ 2 then
      (elements.mapM fun element =>
        readElement element.isOptional element.annotations (ofSchema element.type)).map Ty.tuple
    else none
  | _ => none

decreasing_by
  all_goals simp_wf
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rename_i hproperty
    have hsize := List.sizeOf_lt_of_mem hproperty
    cases property
    simp only [PropertySignatureOf.mk.sizeOf_spec] at hsize
    simp only
    omega
  · omega
  · rename_i helement
    have hsize := List.sizeOf_lt_of_mem helement
    cases element
    simp only [ElementOf.mk.sizeOf_spec] at hsize
    simp only
    omega

/-! ## `N_S` at each node `schema` writes (the fold's equations) -/

theorem normS_never (ann : Annotations) (checks : List Check) :
    normS (.never ann checks) = .never (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_never]
  rfl

theorem normS_unknown (ann : Annotations) (checks : List Check) :
    normS (.unknown ann checks) = .unknown (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_unknown]
  rfl

theorem normS_void (ann : Annotations) (checks : List Check) :
    normS (.void ann checks) = .void (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_void]
  rfl

theorem normS_number (ann : Annotations) (checks : List Check) :
    normS (.number ann checks) = .number (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_number]
  rfl

theorem normS_string (ann : Annotations) (checks : List Check) :
    normS (.string ann checks) = .string (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_string]
  rfl

theorem normS_boolean (ann : Annotations) (checks : List Check) :
    normS (.boolean ann checks) = .boolean (normAnn ann) (checks.map normCheck) := by
  rw [normS, cata_representation_boolean]
  rfl

theorem normS_literal (ann : Annotations) (checks : List Check) (l : LiteralValue) :
    normS (.literal ann checks l) = .literal (normAnn ann) (checks.map normCheck) l := by
  rw [normS, cata_representation_literal]
  rfl

theorem normS_declaration (rep : RepresentationAnnotation) (ann : Annotations)
    (tps : List Representation) (checks : List Check) :
    normS (.declaration rep ann tps checks) =
      .declaration rep (normAnn ann) (tps.map normS) (checks.map normCheck) := by
  rw [normS, cata_representation_declaration]
  rfl

theorem normS_arrays (ann : Annotations) (checks : List Check)
    (els : List (ElementOf Representation)) (rest : List Representation) :
    normS (.arrays ann checks els rest) =
      .arrays (normAnn ann) (checks.map normCheck) ((els.map (ElementOf.map normS)).map normElement)
        (rest.map normS) := by
  rw [normS, cata_representation_arrays]
  rfl

/-- Object normalization retains property order, optional flags, and index signatures. -/
theorem normS_objects (ann : Annotations) (checks : List Check)
    (properties : List PropertySignature) (indexes : List IndexSignature) :
    normS (.objects ann checks properties indexes) =
      .objects (normAnn ann) (checks.map normCheck)
        ((properties.map (PropertySignatureOf.map normS)).map normProperty)
        (indexes.map (IndexSignatureOf.map normS)) := by
  rw [normS, cata_representation_objects]
  rfl

theorem normS_union (ann : Annotations) (checks : List Check) (types : List Representation)
    (mode : UnionMode) :
    normS (.union ann checks types mode) =
      .union (normAnn ann) (checks.map normCheck) (types.map normS) mode := by
  rw [normS, cata_representation_union]
  rfl

/-- The defect slot the reader admits is `defectRep` modulo `N_S`. -/
theorem normS_of_isDefect {b : Representation} (h : isDefect b = true) : normS b = defectRep := by
  unfold isDefect at h
  split at h
  · rw [normS_declaration, of_decide_eq_true h]
    rfl
  · exact nomatch h

/-- `schema` mints no annotation, so `N_S` fixes its image. -/
theorem normS_schema (t : Ty) : normS (schema t) = schema t := by
  induction t with
  | never => rfl
  | unknown => rfl
  | unit => rfl
  | nat => rfl
  | int => rfl
  | string => rfl
  | bool => rfl
  | lit _ => rfl
  | handle _ => rfl
  | var _ => rfl
  | option a ih =>
    show normS (.declaration _ none [schema a] []) = _
    rw [normS_declaration, List.map_cons, List.map_nil, ih]
    rfl
  | list a ih =>
    show normS (.arrays none [] [] [schema a]) = _
    rw [normS_arrays, List.map_cons, List.map_nil, ih]
    rfl
  | prod a b iha ihb =>
    show normS (.arrays none [] [Schema.element (schema a), Schema.element (schema b)] []) = _
    rw [normS_arrays]
    simp only [List.map_cons, List.map_nil, Schema.element, ElementOf.map, normElement, iha, ihb]
    rfl
  | except e a ihe iha =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, ihe, iha]
    rfl
  | exitOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e, defectRep] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | causeOf e ih =>
    show normS (.declaration _ none [schema e, defectRep] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, ih]
    rfl
  | fiberOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | refOf a ih =>
    show normS (.declaration _ none [schema a] []) = _
    rw [normS_declaration, List.map_cons, List.map_nil, ih]
    rfl
  | deferredOf a e iha ihe =>
    show normS (.declaration _ none [schema a, schema e] []) = _
    rw [normS_declaration, List.map_cons, List.map_cons, List.map_nil, iha, ihe]
    rfl
  | union a b iha ihb =>
    show normS (.union none [] [schema a, schema b] .anyOf) = _
    rw [normS_union, List.map_cons, List.map_cons, List.map_nil, iha, ihb]
    rfl
  | record fields ih =>
    rw [schema_record, Schema.struct, normS_objects]
    simp only [List.map_nil, normAnn, List.map_map]
    congr 1
    apply List.map_congr_left
    intro field hfield
    simp only [Function.comp_apply, Schema.property, PropertySignatureOf.map, normProperty,
      normAnn, ih field hfield]
  | map key value ihk ihv =>
    change normS (.objects none [] [] [Schema.index (schema key) (schema value)]) = _
    rw [normS_objects]
    simp only [List.map_nil, List.map_cons, Schema.index, IndexSignatureOf.map,
      normAnn, ihk, ihv]
    rfl
  | tuple items ih =>
    rw [schema_tuple, Schema.tuple, normS_arrays]
    simp only [List.map_nil, normAnn, List.map_map]
    congr 1
    apply List.map_congr_left
    intro item hitem
    simp only [Function.comp_apply, Schema.element, ElementOf.map, normElement,
      normAnn, ih item hitem]
  | app _ _ _ | null | undefined | number | bytes => rfl

/-! ## The retraction and exactness -/

/-- The raw profile and an exact-string discriminator, computed together by the type fold. -/
def reservedProfileAlg : TyAlgebra (fun _ => Bool × Bool) where
  ty_never := (false, true)
  ty_unit := (false, true)
  ty_nat := (false, true)
  ty_int := (false, true)
  ty_string := (true, true)
  ty_bool := (false, true)
  ty_handle target := (false, decide (target ≠ "effect/schema/TypeParameter"))
  ty_option a := (false, a.2)
  ty_list a := (false, a.2)
  ty_prod a b := (false, a.2 && b.2)
  ty_except a b := (false, a.2 && b.2)
  ty_exitOf a b := (false, a.2 && b.2)
  ty_causeOf a := (false, a.2)
  ty_fiberOf a b := (false, a.2 && b.2)
  ty_union a b := (false, a.2 && b.2)
  ty_lit _ := (false, true)
  ty_refOf a := (false, a.2)
  ty_deferredOf a b := (false, a.2 && b.2)
  ty_var _ := (false, true)
  ty_unknown := (false, true)
  ty_record fields := (false, fields.all fun field => field.2.2.2)
  ty_map key value := (false, key.1 && value.2)
  ty_tuple items := (false, decide (items.length ≠ 2) && items.all Prod.snd)
  ty_app _ _ := (false, false)
  ty_null := (false, false)
  ty_undefined := (false, false)
  ty_number := (false, false)
  ty_bytes := (false, false)

/-- The raw Schema profile: supported nodes, string map keys, no two-item tuple alias,
and no reserved type-parameter handle. The public writer normalizes first. -/
def reservedFree (t : Ty) : Bool := (cata_ty reservedProfileAlg t).2

/-- The profile's discriminator recognizes exactly the raw string constructor. -/
theorem reservedProfile_string (t : Ty) :
    (cata_ty reservedProfileAlg t).1 = decide (t = .string) := by
  cases t <;> rfl

/-- Record profile admission checks every declared field, including absent optional fields. -/
theorem reservedFree_record (fields : List (String × Bool × Ty)) :
    reservedFree (.record fields) = fields.all (fun field => reservedFree field.2.2) := by
  rw [reservedFree, cata_ty_record]
  simp only [reservedProfileAlg, List.all_map, Function.comp_def, prodMapSnd]
  rfl

/-- A map in the raw Schema profile has exactly the string key constructor. -/
theorem reservedFree_map (key value : Ty) :
    reservedFree (.map key value) = (decide (key = .string) && reservedFree value) := by
  rw [reservedFree, cata_ty_map]
  change ((cata_ty reservedProfileAlg key).1 && reservedFree value) = _
  rw [reservedProfile_string]

/-- The raw tuple profile excludes the product alias and checks every item. -/
theorem reservedFree_tuple (items : List Ty) :
    reservedFree (.tuple items) = (decide (items.length ≠ 2) && items.all reservedFree) := by
  rw [reservedFree, cata_ty_tuple]
  simp only [reservedProfileAlg, List.length_map, List.all_map, Function.comp_def]
  rfl

/-- Pointwise successful reconstruction lifts to an ordered child list. -/
private theorem mapM_retract {α β : Type} (write : α → β) (read : β → Option α)
    (values : List α) (h : ∀ value ∈ values, read (write value) = some value) :
    (values.map write).mapM read = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    rw [List.map_cons, List.mapM_cons, h value List.mem_cons_self,
      ih (fun item hi => h item (List.mem_cons_of_mem value hi))]
    rfl

/-- Outside arity two, the plain array reader uses the tuple branch. -/
private theorem ofSchema_tuple (ann : Annotations) (elements : List Element)
    (hne : elements.length ≠ 2) :
    ofSchema (.arrays ann [] elements []) =
      if normAnn ann = none then
        (elements.mapM fun element =>
          readElement element.isOptional element.annotations (ofSchema element.type)).map Ty.tuple
      else none := by
  have guard (xs : List Element) (hx : xs.length ≠ 2) :
      (if normAnn ann = none ∧ xs.length ≠ 2 then
        (xs.mapM fun element =>
          readElement element.isOptional element.annotations (ofSchema element.type)).map Ty.tuple
      else none) =
      if normAnn ann = none then
        (xs.mapM fun element =>
          readElement element.isOptional element.annotations (ofSchema element.type)).map Ty.tuple
      else none := by
    by_cases ha : normAnn ann = none
    · rw [if_pos ⟨ha, hx⟩, if_pos ha]
    · rw [if_neg (fun h => ha h.1), if_neg ha]
  cases elements with
  | nil =>
    rw [ofSchema.eq_def]
    exact guard [] hne
  | cons a elements =>
    cases elements with
    | nil =>
      rcases a with ⟨optional, type, annotations⟩
      cases optional <;> rw [ofSchema.eq_def] <;> exact guard _ hne
    | cons b elements =>
      cases elements with
      | nil => exact False.elim (hne rfl)
      | cons c elements =>
        rcases a with ⟨optionalA, typeA, annotationsA⟩
        cases optionalA with
        | true => rw [ofSchema.eq_def]; exact guard _ hne
        | false =>
          rcases b with ⟨optionalB, typeB, annotationsB⟩
          cases optionalB <;> rw [ofSchema.eq_def] <;> exact guard _ hne

/-- Raw Schema retraction on the closed exact profile.
The profile excludes unsupported forms, nonstring map keys, two-item tuples, and the reserved handle id. -/
theorem ofSchema_schema (t : Ty) (h : t.closed = true) (hr : reservedFree t = true) :
    ofSchema (schema t) = some t := by
  induction t with
  | never => rw [ofSchema.eq_def]; rfl
  | unknown => rw [ofSchema.eq_def]; rfl
  | unit => rw [ofSchema.eq_def]; rfl
  | nat => rw [ofSchema.eq_def]; decide +kernel
  | int => rw [ofSchema.eq_def]; decide +kernel
  | string => rw [ofSchema.eq_def]; rfl
  | bool => rw [ofSchema.eq_def]; rfl
  | lit _ => rw [ofSchema.eq_def]; rfl
  | handle target =>
    have hne : target ≠ "effect/schema/TypeParameter" := of_decide_eq_true hr
    rw [ofSchema.eq_def]
    show (if normAnn none = none then
      (if target = "effect/schema/TypeParameter" then none else some (Ty.handle target)) else none) = _
    rw [if_pos (show normAnn none = none from rfl), if_neg hne]
  | var _ => exact Bool.noConfusion h
  | app _ _ _ | null | undefined | number | bytes => exact Bool.noConfusion hr
  | record fields ih =>
    rw [Ty.closed, Ty.closedFields_eq_all] at h
    rw [reservedFree_record] at hr
    have hread := mapM_retract
      (fun field : String × Bool × Ty => Schema.property field.1 (schema field.2.2) field.2.1)
      (fun property => readProperty property.name property.isOptional property.isMutable
        property.annotations (ofSchema property.type)) fields (by
          intro field hf
          obtain ⟨name, optional, ty⟩ := field
          have ht := ih (name, optional, ty) hf
            (List.all_eq_true.mp h _ hf) (List.all_eq_true.mp hr _ hf)
          change (if false = false ∧ normAnn none = none then
            (ofSchema (schema ty)).map (fun t => (name, optional, t)) else none) = _
          rw [if_pos ⟨rfl, rfl⟩, ht]
          rfl)
    rw [schema_record, Schema.struct, ofSchema.eq_def]
    dsimp only
    rw [if_pos (show normAnn none = none from rfl), hread]
    rfl
  | map key value _ ihv =>
    rw [reservedFree_map, Bool.and_eq_true] at hr
    have hk : key = .string := of_decide_eq_true hr.1
    subst key
    rw [Ty.closed, Bool.and_eq_true] at h
    change ofSchema (.objects none [] [] [⟨.string none [], schema value⟩]) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [if_pos (show normAnn none = none ∧ normAnn none = none from ⟨rfl, rfl⟩),
      ihv h.2 hr.2]
    rfl
  | tuple items ih =>
    rw [Ty.closed, Ty.closedItems_eq_all] at h
    rw [reservedFree_tuple, Bool.and_eq_true] at hr
    have hne : items.length ≠ 2 := of_decide_eq_true hr.1
    have hread := mapM_retract
      (fun item => Schema.element (schema item))
      (fun element => readElement element.isOptional element.annotations (ofSchema element.type))
      items (by
        intro item hi
        have ht := ih item hi (List.all_eq_true.mp h _ hi) (List.all_eq_true.mp hr.2 _ hi)
        change (if false = false ∧ normAnn none = none then ofSchema (schema item) else none) = _
        rw [if_pos ⟨rfl, rfl⟩, ht])
    rw [schema_tuple, Schema.tuple, ofSchema_tuple _ _ (by simpa only [List.length_map] using hne),
      if_pos (show normAnn none = none from rfl), hread]
    rfl
  | option a ih =>
    show ofSchema (.declaration ⟨"effect/schema/Option", .null⟩ none [schema a] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [ih h hr]
    rfl
  | list a ih =>
    show ofSchema (.arrays none [] [] [schema a]) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [ih h hr]
    rfl
  | prod a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree b = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.arrays none [] [⟨false, schema a, none⟩, ⟨false, schema b, none⟩] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, iha h.1 hr'.1, ihb h.2 hr'.2]
    rfl
  | except e a ihe iha =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree e = true ∧ reservedFree a = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Result", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [iha h.2 hr'.2, ihe h.1 hr'.1]
    rfl
  | exitOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Exit", .null⟩ none
      [schema a, schema e, defectRep] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | causeOf e ih =>
    show ofSchema (.declaration ⟨"effect/schema/Cause", .null⟩ none [schema e, defectRep] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [ih h hr]
    rfl
  | fiberOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Fiber", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | refOf a ih =>
    show ofSchema (.declaration ⟨"effect/schema/Ref", .null⟩ none [schema a] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [ih h hr]
    rfl
  | deferredOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Deferred", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | union a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree b = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.union none [] [schema a, schema b] .anyOf) = _
    rw [ofSchema.eq_def]
    dsimp only
    rw [iha h.1 hr'.1, ihb h.2 hr'.2]
    rfl

/-- Retraction over canonical types `CTy`. -/
theorem ofSchema_schema_cty (t : CTy) (h : t.toRaw.closed = true)
    (hr : reservedFree t.toRaw = true) : ofSchema (schema t.toRaw) = some t.toRaw :=
  ofSchema_schema t.toRaw h hr

/-- Lift a successful child reader's reconstruction equation to the ordered list. -/
private theorem mapM_reconstruct {α β : Type} (read : α → Option β) (write : β → α)
    (norm : α → α) (xs : List α) (ys : List β)
    (pointwise : ∀ x ∈ xs, ∀ y, read x = some y → norm x = write y)
    (h : xs.mapM read = some ys) : xs.map norm = ys.map write := by
  induction xs generalizing ys with
  | nil => rw [List.mapM_nil] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : read x with
    | none => rw [hx] at h; exact nomatch h
    | some y =>
      cases hxs : xs.mapM read with
      | none => rw [hx, hxs] at h; exact nomatch h
      | some rest =>
        rw [hx, hxs] at h
        cases h
        rw [List.map_cons, List.map_cons, pointwise x List.mem_cons_self y hx,
          ih rest (fun a ha => pointwise a (List.mem_cons_of_mem x ha)) hxs]

/-- A successful plain property read retains its name and optional flag. -/
private theorem readProperty_exact (p : PropertySignature) (field : String × Bool × Ty)
    (child : ∀ t, ofSchema p.type = some t → normS p.type = schema t)
    (h : readProperty p.name p.isOptional p.isMutable p.annotations (ofSchema p.type) = some field) :
    normProperty (PropertySignatureOf.map normS p) =
      Schema.property field.1 (schema field.2.2) field.2.1 := by
  obtain ⟨name, rep, optional, mutable, ann⟩ := p
  cases name with
  | string key =>
    change (if mutable = false ∧ normAnn ann = none then
      (ofSchema rep).map (fun t => (key, optional, t)) else none) = some field at h
    split at h
    · rename_i admitted
      obtain ⟨ty, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, hann⟩ := admitted
      simp only [PropertySignatureOf.map, normProperty, Schema.property, child ty ht, hann]
    · exact nomatch h
  | number _ => exact nomatch h
  | globalSymbol _ => exact nomatch h

/-- A successful plain element read retains its child and has no optional flag. -/
private theorem readElement_exact (element : Element) (ty : Ty)
    (child : ∀ t, ofSchema element.type = some t → normS element.type = schema t)
    (h : readElement element.isOptional element.annotations (ofSchema element.type) = some ty) :
    normElement (ElementOf.map normS element) = Schema.element (schema ty) := by
  obtain ⟨optional, rep, ann⟩ := element
  change (if optional = false ∧ normAnn ann = none then ofSchema rep else none) = some ty at h
  split at h
  · rename_i admitted
    obtain ⟨rfl, hann⟩ := admitted
    simp only [ElementOf.map, normElement, Schema.element, child ty h, hann]
  · exact nomatch h

/-- **Exactness of the reader, modulo `N_S`** (decisions row 128): a representation `ofSchema`
reads is the read type's schema up to the annotation entries that change no decoding. By
`fun_induction ofSchema`: one case per arm and branch of the reader, the refusing ones closed by
`nomatch`. -/
theorem ofSchema_exact (r : Representation) : ∀ t, ofSchema r = some t → normS r = schema t := by
  fun_induction ofSchema r
  case case1 ann hann => intro t h; cases h; rw [normS_never, hann]; rfl
  case case2 => intro t h; exact nomatch h
  case case3 ann hann => intro t h; cases h; rw [normS_unknown, hann]; rfl
  case case4 => intro t h; exact nomatch h
  case case5 ann hann => intro t h; cases h; rw [normS_void, hann]; rfl
  case case6 => intro t h; exact nomatch h
  case case7 ann checks hann hchecks =>
    simp only [List.attach_map_val] at hchecks
    intro t h
    rw [if_pos hchecks] at h
    cases h
    rw [normS_number, hann, hchecks]
    rfl
  case case8 ann checks hann hnot hchecks =>
    simp only [List.attach_map_val] at hnot hchecks
    intro t h
    rw [if_neg hnot, if_pos hchecks] at h
    cases h
    rw [normS_number, hann, hchecks]
    rfl
  case case9 ann checks _ hnot hnot' =>
    simp only [List.attach_map_val] at hnot hnot'
    intro t h
    rw [if_neg hnot, if_neg hnot'] at h
    exact nomatch h
  case case10 => intro t h; exact nomatch h
  case case11 ann hann => intro t h; cases h; rw [normS_string, hann]; rfl
  case case12 => intro t h; exact nomatch h
  case case13 ann hann => intro t h; cases h; rw [normS_boolean, hann]; rfl
  case case14 => intro t h; exact nomatch h
  case case15 ann s hann => intro t h; cases h; rw [normS_literal, hann]; rfl
  case case16 => intro t h; exact nomatch h
  case case17 id ann val hann hid ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case18 id ann val hann _ hid ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case19 => intro t h; exact nomatch h
  case case20 => intro t h; exact nomatch h
  case case21 id ann a b hann hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case22 id ann a b hann _ hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case23 id ann a b hann _ _ hid iha ihb =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain rfl := beq_iff_eq.mp hid
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha tv hv, ihb te he]
    rfl
  case case24 id ann a b hann _ _ _ hid iha =>
    intro t h
    obtain ⟨te, he, h1⟩ := Option.bind_eq_some_iff.mp h
    cases h1
    obtain ⟨hid1, hdef⟩ := Bool.and_eq_true_iff.mp hid
    obtain rfl := beq_iff_eq.mp hid1
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_nil, iha te he,
      normS_of_isDefect hdef]
    rfl
  case case25 => intro t h; exact nomatch h
  case case26 => intro t h; exact nomatch h
  case case27 id ann val err defect hann hid ihv ihe =>
    intro t h
    obtain ⟨tv, hv, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨te, he, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain ⟨hid1, hdef⟩ := Bool.and_eq_true_iff.mp hid
    obtain rfl := beq_iff_eq.mp hid1
    rw [normS_declaration, hann, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      ihv tv hv, ihe te he, normS_of_isDefect hdef]
    rfl
  case case28 => intro t h; exact nomatch h
  case case29 => intro t h; exact nomatch h
  case case30 => intro t h; exact nomatch h
  case case31 id ann hann _ => intro t h; cases h; rw [normS_declaration, hann]; rfl
  case case32 => intro t h; exact nomatch h
  case case33 ann item hann ih =>
    intro t h
    obtain ⟨u, hu, h'⟩ := Option.bind_eq_some_iff.mp h
    cases h'
    rw [normS_arrays, hann, List.map_cons, List.map_nil, ih u hu]
    rfl
  case case34 => intro t h; exact nomatch h
  case case35 ann a annA b annB hann iha ihb =>
    intro t h
    obtain ⟨ta, ha, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tb, hb, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    obtain ⟨h0, hA, hB⟩ := hann
    rw [normS_arrays, h0]
    simp only [List.map_cons, List.map_nil, ElementOf.map, normElement, hA, hB, iha ta ha,
      ihb tb hb]
    rfl
  case case36 => intro t h; exact nomatch h
  case case37 ann a b hann iha ihb =>
    intro t h
    obtain ⟨ta, ha, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tb, hb, h2⟩ := Option.bind_eq_some_iff.mp h1
    cases h2
    rw [normS_union, hann, List.map_cons, List.map_cons, List.map_nil, iha ta ha, ihb tb hb]
    rfl
  case case38 => intro t h; exact nomatch h
  case case39 ann properties hann ih =>
    intro t h
    obtain ⟨fields, hfields, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [schema_record, Schema.struct, normS_objects, hann]
    simp only [List.map_nil, List.map_map]
    congr 1
    exact mapM_reconstruct
      (fun p => readProperty p.name p.isOptional p.isMutable p.annotations (ofSchema p.type))
      (fun field => Schema.property field.1 (schema field.2.2) field.2.1)
      (fun p => normProperty (PropertySignatureOf.map normS p)) properties fields
      (fun p hp field hf => readProperty_exact p field (ih p hp) hf) hfields
  case case40 => intro t h; exact nomatch h
  case case41 ann keyAnn value hann ih =>
    intro t h
    obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp h
    change normS (.objects ann [] [] [⟨.string keyAnn [], value⟩]) =
      .objects none [] [] [⟨.string none [], schema ty⟩]
    rw [normS_objects, hann.1]
    simp only [List.map_nil, List.map_cons, IndexSignatureOf.map, ih ty hty,
      normS_string, hann.2]
  case case42 => intro t h; exact nomatch h
  case case43 ann elements _ hann ih =>
    intro t h
    obtain ⟨items, hitems, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [schema_tuple, Schema.tuple, normS_arrays, hann.1]
    simp only [List.map_nil, List.map_map]
    congr 1
    exact mapM_reconstruct
      (fun e => readElement e.isOptional e.annotations (ofSchema e.type))
      (fun ty => Schema.element (schema ty))
      (fun e => normElement (ElementOf.map normS e)) elements items
      (fun e he ty ht => readElement_exact e ty (ih e he) ht) hitems
  case case44 => intro t h; exact nomatch h
  case case45 => intro t h; exact nomatch h

/-- Exactness in the vocabulary's shape (`AGENTS.md`, exact embedding): `r ≡ schema t` modulo `N_S`. -/
theorem ofSchema_exact' {r : Representation} {t : Ty} (h : ofSchema r = some t) :
    normS r = normS (schema t) := by
  rw [normS_schema]
  exact ofSchema_exact r t h

/-- A requirement's reference key: the whole `ServiceKey`, its name and its service code, spelled
as the printer spells a service key's runtime identity, `k{name}_{service}`
(`Codegen/PrintLeaf.lean`'s `printKey`, `Codegen/Read.lean`'s `keyText`). Schema sits below
Codegen, so the spelling is restated here; `Test/Schema/DialectContract.lean` proves the two equal
and the key injective. Two keys that share a name and differ in service are two references
(decisions row 8). -/
def requirementKey (k : ServiceKey) : String :=
  "k" ++ toString k.name.value ++ "_" ++ toString k.service.value

/-- As an effect: the exit schema root with answer, error, and requirement references (S-2). A
requirement is filed under its `requirementKey`, with a placeholder declaration of that name. -/
def effDocument (eff : EffTy) : Document :=
  { representation := schema (.exitOf eff.answer.normalize eff.error.normalize)
    references :=
      [ ⟨"answer", schema eff.answer.normalize⟩
      , ⟨"error", schema eff.error.normalize⟩ ] ++
      eff.requires.elems.map (fun k => ⟨requirementKey k, schema (.handle (requirementKey k))⟩) }

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

/-- Public Schema retraction on closed canonical types in the exact raw profile.
Normalization has already replaced every two-item tuple with its product. -/
theorem ofSchema_schema (t : CTy) (h : t.toRaw.closed = true)
    (hr : Effect4.Schema.Bridge.reservedFree t.toRaw = true) :
    Ty.ofSchema (schema t) = some t.toRaw := by
  change Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema t.val.normalize) = _
  rw [t.property]
  exact Effect4.Schema.Bridge.ofSchema_schema t.toRaw h hr

end Effect4.Program.CTy
