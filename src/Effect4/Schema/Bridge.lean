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
3. `ofSchema_schema`: the retraction `ofSchema (schema t) = some t`, on closed types whose handles
   avoid the reserved type-parameter id (`reservedFree`).
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
annotation policy (amended 2026-10-01: a check's annotations too) in place of the probe's.
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

/-- Lowers any first-order `Ty` into its canonical rc.112 `SchemaRepresentation`. -/
def schema : Ty → Representation
  | .never => Schema.never
  | .unknown => .unknown none []
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
  | .refOf value => .declaration ⟨"effect/schema/Ref", .null⟩ none [schema value] []
  | .deferredOf value error => .declaration ⟨"effect/schema/Deferred", .null⟩ none [schema value, schema error] []
  -- a row template's parameter has no schema: an opaque node `ofSchema` refuses by name
  | .var _ => .declaration ⟨"effect/schema/TypeParameter", .null⟩ none [] []
  | .union left right => .union none [] [schema left, schema right] .anyOf

/-- Extracts the identifier of a persisted check. The reader no longer reads a check by its id
(row 128: it compares whole checks); this stays the id projection the fold census registers
(`Laws/Program/Folds/Representation.lean`) and the red control of the id reading uses. -/
def checkId : Check → String
  | .filter rep _ _ => rep.id
  | .filterGroup (some rep) _ _ => rep.id
  | .filterGroup none _ _ => ""

/-! ## `N_S`: the annotation policy and the normaliser (decisions rows 128, 179)

One policy for the normaliser and the reader's guard (row 179, ruled 2026-10-01; amended the same
day to cover a check's annotations): an annotation bag is read modulo revision 5's eight
documentation keys (`docs/research/2026-10-01-type-language-probe/S-inputs/revision-5/annotation-review.md`:
rc.112 reads them for diagnostics, references and documentation, never for acceptance or decoded
values). `normAnn` erases those entries and keeps every other entry, and a bag left empty is
`none`; the reader admits a bag only when nothing is left (`normAnn ann = none`), at every bag it
reads: each node, each check, each tuple element, the defect slot. Every other key, `parseOptions`
and `arbitrary` among them, is refused. `normS` applies `normAnn` to every bag of the tree, checks
and properties included, and changes nothing else. -/

/-- The annotation keys that change nothing rc.112 accepts or decodes (row 179: seat S's
allowlist, revision 5's eight documentation keys). -/
def documentationKeys : List String :=
  ["identifier", "title", "description", "documentation", "examples", "default", "message",
   "expected"]

/-- An annotation bag modulo the documentation keys: those entries erased, the rest kept in order,
an empty remainder `none` (so an absent bag and an all-documentation bag are one). -/
def normAnn : Annotations → Annotations
  | none => none
  | some entries =>
    match entries.filter (fun e => !documentationKeys.contains e.key) with
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

/-- A check modulo the documentation keys: `N_S`'s check arm. The reader compares a check with
`schema`'s bare checks after this, so a documented `isInt` is `isInt`. -/
def normCheck (c : Check) : Check := cata_check normSAlg c

/-! ## The reader -/

/-- The defect slot of an `Exit` or `Cause` declaration is the `Json` declaration `schema` mints
(`defectRep`), with a documentation-only annotation bag (rc.112 writes `expected` there); nothing
else. -/
def isDefect : Representation → Bool
  | .declaration ⟨"effect/schema/Json", .null⟩ ann [] [] => decide (normAnn ann = none)
  | _ => false

/-- Reconstitutes a first-order `Ty` from an rc.112 `SchemaRepresentation` (decisions rows 6 and
128): exactly the nodes `schema` mints, modulo `N_S`. Each arm reads its annotation bag first and
refuses a key that is not documentation (row 179). A `number`'s checks are compared whole, after
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
  | _ => none

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

/-! ## The retraction and exactness -/

/-- The fold behind `reservedFree`: a handle's target is checked against the reserved id, every
other node conjoins its children. -/
def reservedFreeAlg : TyAlgebra (fun _ => Bool) where
  ty_never := true
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle target := decide (target ≠ "effect/schema/TypeParameter")
  ty_option a := a
  ty_list a := a
  ty_prod a b := a && b
  ty_except a b := a && b
  ty_exitOf a b := a && b
  ty_causeOf a := a
  ty_fiberOf a b := a && b
  ty_union a b := a && b
  ty_lit _ := true
  ty_refOf a := a
  ty_deferredOf a b := a && b
  ty_var _ := true
  ty_unknown := true

/-- No handle target is the reserved type-parameter id `effect/schema/TypeParameter`: the premise
the retraction gains when the reader refuses that id by name (a fold; formation should refuse such
a handle, and then the premise goes). -/
def reservedFree (t : Ty) : Bool := cata_ty reservedFreeAlg t

/-- **The retraction**: `ofSchema` is a left inverse to `schema` on every closed type whose handles
avoid the reserved type-parameter id (`schema` mints no annotation, no check but `number`'s, `null`
payloads and plain elements, so every guard passes; a row template's parameter is not a program
type and has no schema to read back). Until row 128's commit the premise `reservedFree` was not
needed, because the reader read the type parameter's declaration back as a handle. -/
theorem ofSchema_schema (t : Ty) (h : t.closed = true) (hr : reservedFree t = true) :
    ofSchema (schema t) = some t := by
  induction t with
  | never => rfl
  | unknown => rfl
  | unit => rfl
  | nat => decide +kernel
  | int => decide +kernel
  | string => rfl
  | bool => rfl
  | lit _ => rfl
  | handle target =>
    have hne : target ≠ "effect/schema/TypeParameter" := of_decide_eq_true hr
    show (if normAnn none = none then
      (if target = "effect/schema/TypeParameter" then none else some (Ty.handle target)) else none) = _
    rw [if_pos (show normAnn none = none from rfl), if_neg hne]
  | var _ => exact Bool.noConfusion h
  | option a ih =>
    show ofSchema (.declaration ⟨"effect/schema/Option", .null⟩ none [schema a] []) = _
    rw [ofSchema, ih h hr]
    rfl
  | list a ih =>
    show ofSchema (.arrays none [] [] [schema a]) = _
    rw [ofSchema, ih h hr]
    rfl
  | prod a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree b = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.arrays none [] [⟨false, schema a, none⟩, ⟨false, schema b, none⟩] []) = _
    rw [ofSchema, if_pos ⟨rfl, rfl, rfl⟩, iha h.1 hr'.1, ihb h.2 hr'.2]
    rfl
  | except e a ihe iha =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree e = true ∧ reservedFree a = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Result", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema, iha h.2 hr'.2, ihe h.1 hr'.1]
    rfl
  | exitOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Exit", .null⟩ none
      [schema a, schema e, defectRep] []) = _
    rw [ofSchema, iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | causeOf e ih =>
    show ofSchema (.declaration ⟨"effect/schema/Cause", .null⟩ none [schema e, defectRep] []) = _
    rw [ofSchema, ih h hr]
    rfl
  | fiberOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Fiber", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema, iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | refOf a ih =>
    show ofSchema (.declaration ⟨"effect/schema/Ref", .null⟩ none [schema a] []) = _
    rw [ofSchema, ih h hr]
    rfl
  | deferredOf a e iha ihe =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree e = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.declaration ⟨"effect/schema/Deferred", .null⟩ none [schema a, schema e] []) = _
    rw [ofSchema, iha h.1 hr'.1, ihe h.2 hr'.2]
    rfl
  | union a b iha ihb =>
    rw [Ty.closed, Bool.and_eq_true] at h
    have hr' : reservedFree a = true ∧ reservedFree b = true := Bool.and_eq_true _ _ ▸ hr
    show ofSchema (.union none [] [schema a, schema b] .anyOf) = _
    rw [ofSchema, iha h.1 hr'.1, ihb h.2 hr'.2]
    rfl

/-- Retraction over canonical types `CTy`. -/
theorem ofSchema_schema_cty (t : CTy) (h : t.toRaw.closed = true)
    (hr : reservedFree t.toRaw = true) : ofSchema (schema t.toRaw) = some t.toRaw :=
  ofSchema_schema t.toRaw h hr

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
    intro t h; cases h; rw [normS_number, hann, hchecks]; rfl
  case case8 ann checks hann _ hchecks =>
    intro t h; cases h; rw [normS_number, hann, hchecks]; rfl
  case case9 => intro t h; exact nomatch h
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
  case case39 => intro t h; exact nomatch h

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

/-- The public schema boundary retracts on closed canonical types whose handles avoid the reserved
type-parameter id; integer parsing is retained. A row template's parameter is not a program type
(`Ty.closed`). -/
theorem ofSchema_schema (t : CTy) (h : t.toRaw.closed = true)
    (hr : Effect4.Schema.Bridge.reservedFree t.toRaw = true) :
    Ty.ofSchema (schema t) = some t.toRaw := by
  change Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema t.val.normalize) = _
  rw [t.property]
  exact Effect4.Schema.Bridge.ofSchema_schema t.toRaw h hr

end Effect4.Program.CTy
