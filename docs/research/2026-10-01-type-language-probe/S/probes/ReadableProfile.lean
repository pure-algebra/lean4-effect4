import Effect4.Schema.Representation
import Effect4.Schema.Payload
import Effect4.Schema.Fold
import Effect4.Schema.Bridge
import Effect4.Codegen.Schema
import TypeScript
import TypeScript.Render

/-!
# Seat S, question 3: the readable profile, per form

Revision 5 of the Schema scouting (`S-inputs/revision-5/DefinitiveSchemaProbe.lean`, SHA-256
`8ec10148…f4e8`, reproduced in `S/rev5/`) is the base, kept line for line; this file extends it
(`diff rev5/DefinitiveSchemaProbe.lean probes/ReadableProfile.lean` is the new work), each change
under a `-- [S:<what>]` marker:

* exact property spelling: an identifier bare, any other name quoted, `__proto__` computed
  (revision 5 refuses `__proto__`); a name that needs escapes falls back to the all-quoted object,
  and beside `__proto__` it refuses by name (the target syntax has no per-key spelling yet);
* maps: an `objects` node with one index signature over `Schema.String` and no property emits
  `Schema.Record(Schema.String, V)` (revision 5 refuses every index signature);
* unions: a union of plain literals emits `Schema.Literals([…])`, and an `anyOf` union's last
  member that is itself an emitted union is spliced (`N_S`'s spine step, so `Ty.schema`'s nested
  binary unions print flat);
* the profile predicate `admits` and the agreement `admits r = true ↔ emission succeeds`.

The annotation policy is revision 5's, as the amended brief adopts it: the eight documentation
keys of `annotation-review.md` are erased under the observation "structural type, acceptance and
decoded value"; every other key refuses by name with its path.
-/

open Effect4 TypeScript

namespace SeatS.Readable

/-- A located refusal that records the hierarchical path and reason for rejection. -/
structure SchemaRefusal where
  path : List String
  reason : String
deriving DecidableEq, Repr

abbrev Result (α : Type) := Except SchemaRefusal α

/-- Prefix a path segment to a located refusal. -/
def prefixPath (segment : String) : Result α → Result α
  | .ok a => .ok a
  | .error e => .error { e with path := segment :: e.path }

/-- Helper to index a list with 0-based position. -/
def listZipIdx (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | y :: ys => (i, y) :: go (i + 1) ys
  go 0 xs

/-! ## 1. Fail-Closed Annotation Policy -/

/-- Allowed documentation and diagnostic annotation keys that are safely erasable
under the structural validation and typing observation. -/
def allowedDocKeys : List String :=
  ["identifier", "title", "description", "documentation", "examples", "default", "message", "expected"]

/-- Validate an annotation bag:
- Empty (none or some []) passes.
- Entries whose keys are in `allowedDocKeys` pass (erasable documentation metadata).
- Any semantic or unadmitted annotation (e.g. "parseOptions") is strictly refused with path and reason. -/
def validateAnnotations (path : List String) (annotations : Annotations) : Result Unit :=
  match annotations with
  | none => .ok ()
  | some entries => do
      let rec checkEntries : List AnnotationEntry → Result Unit
        | [] => .ok ()
        | entry :: rest =>
            if allowedDocKeys.contains entry.key then checkEntries rest
            else .error ⟨path ++ ["annotations"], s!"Semantic or unadmitted annotation '{entry.key}' not supported in readable profile"⟩
      checkEntries entries

/-! ## 2. Validated Checks Carrier -/

inductive ValidatedCheck where
  | isInt
  | nonNegative (minimum : Float64)
deriving DecidableEq, Repr

/-- Validate a persisted Check against admitted canonical checks with full payload inspection,
annotation validation, and recursive child schema validation. Never discards failed child schemas. -/
def validateFilter (rep : CheckRepresentationAnnotationOf (Result Expr))
    (annotations : Annotations) (aborted : Bool) : Result ValidatedCheck := do
  if aborted then
    .error ⟨[], s!"Aborted checks not supported in readable profile (check {rep.id})"⟩
  -- 1. Validate filter annotations: refuse semantic annotations like parseOptions!
  validateAnnotations [] annotations
  -- 2. Strictly traverse any recursive child schemas so child errors are never swallowed!
  match rep.schemas with
  | some schemas =>
      let _ ← (listZipIdx schemas).mapM fun (i, s) =>
        prefixPath s!"schemas[{i}]" s
      if !schemas.isEmpty then
        .error ⟨["schemas"], s!"Child schemas on canonical check '{rep.id}' not supported in readable profile"⟩
  | none => pure ()

  -- 3. Inspect check ID and payload
  if rep.id == "effect/schema/isInt" then
    if rep.payload == .null then .ok .isInt
    else .error ⟨[], "isInt check has unexpected non-null payload"⟩
  else if rep.id == "effect/schema/isGreaterThanOrEqualTo" then
    match rep.payload with
    | .obj [("minimum", .number min)] =>
        if min == Float64.zero then .ok (.nonNegative min)
        else .error ⟨[], s!"isGreaterThanOrEqualTo with non-zero minimum ({min.toBits}) not admitted in Stage 1 nat profile"⟩
    | _ => .error ⟨[], "isGreaterThanOrEqualTo check missing expected 'minimum' float payload"⟩
  else
    .error ⟨[], s!"Unknown or unsupported check '{rep.id}'"⟩

/-! ## 3. Object Field Processing with Duplicate, Prototype & Annotation Refusal -/

-- [S:spelling] The bytes a JavaScript string literal must escape (the target renderer's set).
def needsEscape (name : String) : Bool :=
  name.toUTF8.data.toList.any fun b => b == 34 || b == 92 || b == 10 || b == 13 || b == 9

-- [S:spelling] A property's spelling in an object literal, rendered here only where no escape is
-- needed: `__proto__` computed (a quoted or bare `__proto__` sets the prototype: question 2 E8),
-- an identifier bare, any other name quoted; `none` when the name needs escapes.
def keySpelling (name : String) : Option String :=
  if name == "__proto__" then some "[\"__proto__\"]"
  else if targetIdentifier name then some name
  else if needsEscape name then none
  else some ("\"" ++ name ++ "\"")

-- [S:spelling] The struct's object: per-key spelling when every key has one; otherwise the
-- all-quoted object (the renderer escapes), refused beside `__proto__`.
def structObject (fields : List (String × Expr)) : Result Expr :=
  match fields.mapM (fun f => (keySpelling f.1).map (fun k => (k, f.2))) with
  | some spelled => .ok (.object spelled)
  | none =>
    if fields.any (fun f => f.1 == "__proto__") then
      match fields.find? (fun f => needsEscape f.1) with
      | some f => .error ⟨[f.1], "A name needing escapes beside '__proto__': per-key spelling needs the target syntax"⟩
      | none => .ok (.objectQuoted fields)
    else .ok (.objectQuoted fields)

/-- Process object properties: verifies no duplicates, validates property annotations. -/
def processProperties (properties : List (PropertySignatureOf (Result Expr))) : Result (List (String × Expr)) :=
  let rec go (seen : List String) (acc : List (String × Expr)) : List (PropertySignatureOf (Result Expr)) → Result (List (String × Expr))
    | [] => .ok acc.reverse
    | prop :: rest =>
        match prop.name with
        | .string name =>
            if seen.contains name then
              .error ⟨[name], s!"Duplicate object field '{name}' not admitted in readable profile (TS1117)"⟩
            else do
              -- Validate property-level annotations
              validateAnnotations [name] prop.annotations
              let fieldSchema ← prefixPath name prop.type
              let mut expr := fieldSchema
              if prop.isMutable then
                expr := .call (.ident "Schema.mutableKey") [expr]
              if prop.isOptional then
                expr := .call (.ident "Schema.optionalKey") [expr]
              go (name :: seen) ((name, expr) :: acc) rest
        | .number n =>
            .error ⟨[s!"numeric_key_{n.toBits}"], "Numeric property keys not supported in readable profile"⟩
        | .globalSymbol s =>
            .error ⟨[s.key], "Global symbol property keys not supported in readable profile"⟩
  go [] [] properties

-- [S:union] A member emitted as `Schema.Literal(x)`: its argument.
def literalArg : Expr → Option Expr
  | .call (.ident "Schema.Literal") [x] => some x
  | _ => none

-- [S:union] The last member, when it is an emitted union, spliced into the list (the right
-- spine of `Ty`'s binary unions; rc.112 decodes the nested and the flat union alike, question 2
-- E10f, and `N_S` identifies them).
def spliceLastMember (ms : List Expr) : List Expr :=
  match ms.getLast? with
  | some (.call (.ident "Schema.Union") [.arr inner]) => ms.dropLast ++ inner
  | some (.call (.ident "Schema.Literals") [.arr lits]) =>
    ms.dropLast ++ lits.map (fun l => .call (.ident "Schema.Literal") [l])
  | _ => ms

/-! ## 4. Fold-Indexed Readable Algebra -/

def ResultFam : RepresentationFam → Type
  | .representation => Result Expr
  | .check => Result ValidatedCheck

def definitiveAlgebra : RepresentationAlgebra ResultFam where
  representation_declaration _ annotations _ _ := do
    validateAnnotations [] annotations
    .error ⟨[], "Custom declarations not supported in readable profile"⟩
  representation_reference key :=
    .error ⟨[key.value], "References require Document context"⟩
  representation_suspend annotations _ _ := do
    validateAnnotations [] annotations
    .error ⟨[], "Suspended schemas not supported in Stage 1"⟩
  representation_null annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Null")
    else .error ⟨[], "Checks on Null not supported"⟩
  representation_undefined annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Undefined")
    else .error ⟨[], "Checks on Undefined not supported"⟩
  representation_void annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Void")
    else .error ⟨[], "Checks on Void not supported"⟩
  representation_never annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Never")
    else .error ⟨[], "Checks on Never not supported"⟩
  representation_unknown annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Unknown")
    else .error ⟨[], "Checks on Unknown not supported"⟩
  representation_any annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Any")
    else .error ⟨[], "Checks on Any not supported"⟩
  representation_string annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.String")
    else .error ⟨[], "Custom checks on String not supported"⟩
  representation_number annotations checks := do
    validateAnnotations [] annotations
    let validatedChecks ← (listZipIdx checks).mapM fun (i, c) =>
      prefixPath s!"check[{i}]" c
    match validatedChecks with
    | [] => .ok (.ident "Schema.Number")
    | [ValidatedCheck.isInt] => .ok (.ident "Schema.Int")
    | [ValidatedCheck.isInt, ValidatedCheck.nonNegative min] =>
        if min == Float64.zero then
          .ok (.ident "Schema.Natural")
        else
          .error ⟨["checks"], s!"Non-zero minimum ({min.toBits}) not supported"⟩
    | _ =>
        .error ⟨["checks"], s!"Combination of number checks not admitted in readable profile"⟩
  representation_boolean annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Boolean")
    else .error ⟨[], "Checks on Boolean not supported"⟩
  representation_bigint annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.BigInt")
    else .error ⟨[], "Checks on BigInt not supported"⟩
  representation_symbol annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.Symbol")
    else .error ⟨[], "Checks on Symbol not supported"⟩
  representation_literal annotations checks value := do
    validateAnnotations [] annotations
    if !checks.isEmpty then .error ⟨[], "Checks on Literal not supported"⟩
    match value with
    | .string s => .ok (.call (.ident "Schema.Literal") [.str s])
    | .number n => .ok (.call (.ident "Schema.Literal") [.float64Bits n.toBits])
    | .boolean b => .ok (.call (.ident "Schema.Literal") [.bool b])
    | .bigint i => .error ⟨[], s!"BigInt literals ({i}) require BigInt syntax extension"⟩
  representation_uniqueSymbol annotations _ _ := do
    validateAnnotations [] annotations
    .error ⟨[], "UniqueSymbol not supported in readable profile"⟩
  representation_objectKeyword annotations checks := do
    validateAnnotations [] annotations
    if checks.isEmpty then .ok (.ident "Schema.ObjectKeyword")
    else .error ⟨[], "Checks on ObjectKeyword not supported"⟩
  representation_enum annotations _ _ := do
    validateAnnotations [] annotations
    .error ⟨[], "Enum not supported in readable profile"⟩
  representation_templateLiteral annotations _ _ := do
    validateAnnotations [] annotations
    .error ⟨[], "TemplateLiteral not supported in readable profile"⟩
  representation_arrays annotations checks elements rest := do
    validateAnnotations [] annotations
    if !checks.isEmpty then .error ⟨[], "Checks on arrays/tuples not supported"⟩
    let restExprs ← (listZipIdx rest).mapM fun (i, r) => prefixPath s!"rest[{i}]" r
    let elemExprs ← (listZipIdx elements).mapM fun (i, e) => do
      validateAnnotations [s!"elements[{i}]"] e.annotations
      let t ← prefixPath s!"elements[{i}]" e.type
      .ok (e.isOptional, t)
    match elemExprs, restExprs with
    | [], [inner] => .ok (.call (.ident "Schema.Array") [inner])
    | elems, [] =>
        let tupleElems ← (listZipIdx elems).mapM fun (i, opt, expr) =>
          if opt then .error ⟨[s!"elements[{i}]"], "Optional tuple elements not supported"⟩
          else .ok expr
        .ok (.call (.ident "Schema.Tuple") [.arr tupleElems])
    | _, _ => .error ⟨[], "Tuple with rest elements not supported in Stage 1"⟩
  representation_objects annotations checks properties indexes := do
    validateAnnotations [] annotations
    if !checks.isEmpty then .error ⟨[], "Checks on objects not supported"⟩
    match properties, indexes with
    -- [S:map] `Schema.Record(Schema.String, V)`: one index signature over a plain `Schema.String`
    | [], [⟨.ok (.ident "Schema.String"), v⟩] => do
        let ve ← prefixPath "indexSignatures[0]" v
        .ok (.call (.ident "Schema.Record") [.ident "Schema.String", ve])
    | [], [⟨p, _⟩] => do
        let _ ← prefixPath "indexSignatures[0]" (prefixPath "parameter" p)
        .error ⟨["indexSignatures[0]", "parameter"], "A map is keyed by Schema.String only (row 125)"⟩
    | _, [] => do
        let fieldExprs ← processProperties properties
        -- [S:spelling]
        let obj ← structObject fieldExprs
        .ok (.call (.ident "Schema.Struct") [obj])
    | _, _ => .error ⟨["indexSignatures"], "Index signatures beside properties (StructWithRest) not supported"⟩
  representation_union annotations checks types mode := do
    validateAnnotations [] annotations
    if !checks.isEmpty then .error ⟨[], "Checks on unions not supported"⟩
    if mode != UnionMode.anyOf then .error ⟨[], "oneOf union mode not supported"⟩
    let memberExprs ← (listZipIdx types).mapM fun (i, t) => prefixPath s!"union[{i}]" t
    -- [S:union] `N_S`'s spine step, then the literal union's own spelling
    let flat := spliceLastMember memberExprs
    match flat.mapM literalArg with
    | some lits => .ok (.call (.ident "Schema.Literals") [.arr lits])
    | none => .ok (.call (.ident "Schema.Union") [.arr flat])
  check_filter rep annotations aborted :=
    validateFilter rep annotations aborted
  check_filterGroup _ _ _ :=
    .error ⟨[], "Check filter groups not supported in readable profile"⟩

/-- Main entry point for readable Schema expression generation. -/
def toReadableSchema (rep : Representation) : Result Expr :=
  cata_representation definitiveAlgebra rep

open Effect4.Program

/-! ## Positive & Negative Asserting Controls -/

-- 1. Canonical Bridge.schema .nat emits Schema.Natural
def natRep : Representation := Effect4.Schema.Bridge.schema .nat

#guard match toReadableSchema natRep with
  | .ok (.ident "Schema.Natural") => true
  | _ => false

-- 2. Canonical Bridge.schema .int emits Schema.Int
def intRep : Representation := Effect4.Schema.Bridge.schema .int

#guard match toReadableSchema intRep with
  | .ok (.ident "Schema.Int") => true
  | _ => false

-- 3. Nested child error inside check.schemas is NOT swallowed: surfaced at schemas[0]!
def checkWithFailingChildRep : Representation :=
  .number none [Check.filter ⟨"effect/schema/isInt", Json.null, some [.declaration ⟨"custom/opaque", Json.null⟩ none [] []]⟩ none false]

#guard match toReadableSchema checkWithFailingChildRep with
  | .error ⟨["check[0]", "schemas[0]"], reason⟩ => reason.contains "Custom declarations not supported"
  | _ => false

-- 4. Check with nonempty valid child schemas is refused for canonical check:
def checkWithNonEmptyChildRep : Representation :=
  .number none [Check.filter ⟨"effect/schema/isInt", Json.null, some [.string none []]⟩ none false]

#guard match toReadableSchema checkWithNonEmptyChildRep with
  | .error ⟨["check[0]", "schemas"], reason⟩ => reason.contains "Child schemas on canonical check 'effect/schema/isInt' not supported"
  | _ => false

-- 5. Duplicate object field is REFUSED with exact path ["a"] (preventing TS1117)
def duplicateFieldRep : Representation :=
  .objects none []
    [ { name := .string "a", type := .number none [], isOptional := false, isMutable := false, annotations := none }
    , { name := .string "a", type := .string none [], isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema duplicateFieldRep with
  | .error ⟨["a"], reason⟩ => reason.contains "Duplicate object field 'a'"
  | _ => false

-- 6. [S:spelling] "__proto__" is now EMITTED, computed (revision 5 refused it at ["config", "__proto__"])
def protoRep : Representation :=
  .objects none []
    [ { name := .string "config"
      , type := .objects none []
          [ { name := .string "__proto__", type := .number none [], isOptional := false, isMutable := false, annotations := none } ]
          []
      , isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema protoRep with
  | .ok (.call (.ident "Schema.Struct") [.object [("config", .call (.ident "Schema.Struct")
      [.object [("[\"__proto__\"]", .ident "Schema.Number")]])]]) => true
  | _ => false

-- 7. Deeply nested check failure in user.address retains full path ["user", "address", "check[0]"]
def nestedCheckFailureRep : Representation :=
  .objects none []
    [ { name := .string "user"
      , type := .objects none []
          [ { name := .string "address"
            , type := .number none [Check.filter ⟨"unknown/check", Json.null, none⟩ none false]
            , isOptional := false, isMutable := false, annotations := none } ]
          []
      , isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema nestedCheckFailureRep with
  | .error ⟨["user", "address", "check[0]"], reason⟩ => reason.startsWith "Unknown or unsupported check"
  | _ => false

-- 8. Valid nested struct emits correctly with Schema.Natural
def validNestedRep : Representation :=
  .objects none []
    [ { name := .string "user"
      , type := .objects none []
          [ { name := .string "age", type := natRep, isOptional := false, isMutable := false, annotations := none }
          , { name := .string "name", type := .string none [], isOptional := false, isMutable := false, annotations := none } ]
          []
      , isOptional := false, isMutable := false, annotations := none } ]
    []

-- [S:spelling] identifier names are now bare (`.object`), not quoted
#guard match toReadableSchema validNestedRep with
  | .ok (.call (.ident "Schema.Struct") [.object [("user", .call (.ident "Schema.Struct") [.object [("age", .ident "Schema.Natural"), ("name", .ident "Schema.String")]])]]) => true
  | _ => false

/-! ## 5. Fail-Closed Annotation Controls (Resolving Revision 4) -/

-- A. Object annotation parseOptions: { onExcessProperty: "error" } is REFUSED at ["annotations"]!
def objParseOptionsErrorRep : Representation :=
  .objects (some [⟨"parseOptions", .obj [("onExcessProperty", .str "error")]⟩]) []
    [ { name := .string "a", type := .number none [], isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema objParseOptionsErrorRep with
  | .error ⟨["annotations"], reason⟩ => reason.contains "parseOptions"
  | _ => false

-- B. Object annotation parseOptions: { onExcessProperty: "preserve" } is REFUSED at ["annotations"]!
def objParseOptionsPreserveRep : Representation :=
  .objects (some [⟨"parseOptions", .obj [("onExcessProperty", .str "preserve")]⟩]) []
    [ { name := .string "a", type := .number none [], isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema objParseOptionsPreserveRep with
  | .error ⟨["annotations"], reason⟩ => reason.contains "parseOptions"
  | _ => false

-- C. Filter annotation parseOptions: { disableChecks: true } on isInt check is REFUSED at ["check[0]", "annotations"]!
def intCheckDisableChecksRep : Representation :=
  .number none
    [ Check.filter ⟨"effect/schema/isInt", Json.null, none⟩
        (some [⟨"parseOptions", .obj [("disableChecks", .bool true)]⟩]) false ]

#guard match toReadableSchema intCheckDisableChecksRep with
  | .error ⟨["check[0]", "annotations"], reason⟩ => reason.contains "parseOptions"
  | _ => false

-- D. Unknown annotation key is REFUSED at ["annotations"]!
def unknownAnnotationRep : Representation :=
  .string (some [⟨"customMeta", .str "val"⟩]) []

#guard match toReadableSchema unknownAnnotationRep with
  | .error ⟨["annotations"], reason⟩ => reason.contains "customMeta"
  | _ => false

-- E. Mixed bag: allowed "title" and unadmitted "parseOptions" is REFUSED at ["annotations"]!
def mixedAnnotationRep : Representation :=
  .string (some [⟨"title", .str "MyString"⟩, ⟨"parseOptions", .obj []⟩]) []

#guard match toReadableSchema mixedAnnotationRep with
  | .error ⟨["annotations"], reason⟩ => reason.contains "parseOptions"
  | _ => false

-- F. Nested semantic annotation in field user.address is REFUSED at ["user", "address", "annotations"]!
def nestedSemanticAnnotationRep : Representation :=
  .objects none []
    [ { name := .string "user"
      , type := .objects none []
          [ { name := .string "address"
            , type := .string (some [⟨"parseOptions", .obj []⟩]) []
            , isOptional := false, isMutable := false, annotations := none } ]
          []
      , isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema nestedSemanticAnnotationRep with
  | .error ⟨["user", "address", "annotations"], reason⟩ => reason.contains "parseOptions"
  | _ => false

-- G. Positive control: Allowed documentation metadata ("title", "description") is safely admitted!
def allowedDocAnnotationRep : Representation :=
  .string (some [⟨"title", .str "UserName"⟩, ⟨"description", .str "A user's handle"⟩]) []

#guard match toReadableSchema allowedDocAnnotationRep with
  | .ok (.ident "Schema.String") => true
  | _ => false

-- H. Positive control: Empty bags (none and some []) pass!
def emptyBagRep : Representation :=
  .string (some []) []

#guard match toReadableSchema emptyBagRep with
  | .ok (.ident "Schema.String") => true
  | _ => false

/-! ## 6. [S] The profile, per form: the predicate, the emissions, the refusals -/

/-- The readable profile's admission predicate: the domain of the emission, with its located
refusal (`explain`). Admitted (each arm above): `Null`, `Undefined`, `Void`, `Never`, `Unknown`,
`Any`, `String`, `Boolean`, `BigInt`, `Symbol`, `ObjectKeyword` with no check; `Number` with no
check, `[isInt]` or `[isInt, isGreaterThanOrEqualTo 0]` (the checks `Bridge.schema` writes,
compared whole); string, number and boolean literals; arrays (one rest) and tuples (plain
elements, no rest); structs of string-named properties, no repeat, `optionalKey`/`mutableKey`
kept; one index signature over `Schema.String` (a map); `anyOf` unions. Annotations: revision
5's eight documentation keys, erased; every other key refused by name, at its path. Observation:
the emitted schema's structural `Type`, its acceptance and its decoded values, against the
document's own (`S/host/q3-profile.ts`); messages, identifiers and brands are outside it. -/
def admits (r : Representation) : Bool :=
  match toReadableSchema r with
  | .ok _ => true
  | .error _ => false

def explain (r : Representation) : Option SchemaRefusal :=
  match toReadableSchema r with
  | .ok _ => none
  | .error e => some e

theorem admits_iff_explain (r : Representation) : admits r = true ↔ explain r = none := by
  unfold admits explain
  split <;> simp only [reduceCtorEq]

def text (r : Representation) : Option String :=
  match toReadableSchema r with
  | .ok e => some (Render.expr house0 0 e)
  | .error _ => none

def refusedAt (path : List String) (r : Representation) : Bool :=
  match explain r with
  | some e => e.path == path
  | none => false

def prop (n : String) (r : Representation) (opt : Bool := false) (isMut : Bool := false) :
    PropertySignature :=
  { name := .string n, type := r, isOptional := opt, isMutable := isMut, annotations := none }
def lit (s : String) : Representation := .literal none [] (.string s)
def tagged (tag : String) (ps : List PropertySignature) : Representation :=
  .objects none [] (prop "_tag" (lit tag) :: ps) []
def intRepS : Representation := Effect4.Schema.Bridge.schema .int
def natRepS : Representation := Effect4.Schema.Bridge.schema .nat

-- the per-form inputs: what `schema` writes for each form (`S/probes/K2Copy.lean` §4), and rc.112's
def recordRep : Representation := .objects none [] [prop "a" intRepS, prop "b" (.string none [])] []
def optionalRep : Representation :=
  .objects none [] [prop "a" intRepS (opt := true), prop "b" (.string none [])] []
def optionalUndefRep : Representation :=
  .objects none [] [prop "a" (.union none [] [intRepS, .undefined none []] .anyOf) (opt := true)] []
def mapRep : Representation := .objects none [] [] [{ parameter := .string none [], type := intRepS }]
def tagged2Rep : Representation := .union none []
  [tagged "A" [prop "x" intRepS], tagged "B" [prop "y" (.string none [])]] .anyOf
def tagged3Rep : Representation := .union none []
  [tagged "A" [prop "x" intRepS], .union none []
    [tagged "B" [prop "y" (.string none [])], tagged "C" []] .anyOf] .anyOf
def lit3NestedRep : Representation := .union none [] [lit "a", .union none [] [lit "b", lit "c"] .anyOf] .anyOf
def lit3FlatRep : Representation := .union none [] [lit "a", lit "b", lit "c"] .anyOf
def tuple3Rep : Representation := .arrays none []
  [⟨false, intRepS, none⟩, ⟨false, .string none [], none⟩, ⟨false, .boolean none [], none⟩] []
def arrayRep : Representation := .arrays none [] [] [.string none []]
def specialRep : Representation := .objects none []
  [prop "__proto__" intRepS, prop "a-b" (.string none []), prop "é" (.boolean none []),
   prop "constructor" (.string none []), prop "" intRepS, prop "10" intRepS, prop "9" natRepS] []
def escapedRep : Representation := .objects none [] [prop "x\"y" (.string none []), prop "a" intRepS] []
def mutableRep : Representation := .objects none [] [prop "a-b" (.string none []) (opt := true) (isMut := true)] []

#guard text recordRep = some "Schema.Struct({ a: Schema.Int, b: Schema.String })"
#guard text optionalRep = some "Schema.Struct({ a: Schema.optionalKey(Schema.Int), b: Schema.String })"
#guard text optionalUndefRep =
  some "Schema.Struct({ a: Schema.optionalKey(Schema.Union([Schema.Int, Schema.Undefined])) })"
#guard text mapRep = some "Schema.Record(Schema.String, Schema.Int)"
#guard text tagged2Rep = some ("Schema.Union([Schema.Struct({ _tag: Schema.Literal(\"A\"), x: Schema.Int }), " ++
  "Schema.Struct({ _tag: Schema.Literal(\"B\"), y: Schema.String })])")
-- a nested union prints flat (N_S's spine step); a literal union as `Schema.Literals`
#guard text tagged3Rep = some ("Schema.Union([Schema.Struct({ _tag: Schema.Literal(\"A\"), x: Schema.Int }), " ++
  "Schema.Struct({ _tag: Schema.Literal(\"B\"), y: Schema.String }), Schema.Struct({ _tag: Schema.Literal(\"C\") })])")
#guard text lit3NestedRep = some "Schema.Literals([\"a\", \"b\", \"c\"])"
#guard text lit3FlatRep = text lit3NestedRep
-- a tuple is not an array
#guard text tuple3Rep = some "Schema.Tuple([Schema.Int, Schema.String, Schema.Boolean])"
#guard text arrayRep = some "Schema.Array(Schema.String)"
-- exact property spelling: computed, quoted, bare; and the all-quoted fallback for escapes
#guard text specialRep = some ("Schema.Struct({ [\"__proto__\"]: Schema.Int, \"a-b\": Schema.String, " ++
  "\"é\": Schema.Boolean, constructor: Schema.String, \"\": Schema.Int, \"10\": Schema.Int, \"9\": Schema.Natural })")
#guard text escapedRep = some "Schema.Struct({ \"x\\\"y\": Schema.String, \"a\": Schema.Int })"
-- a mutable field keeps `mutableKey`
#guard text mutableRep = some "Schema.Struct({ \"a-b\": Schema.optionalKey(Schema.mutableKey(Schema.String)) })"
-- the refusals, located
def escapedProtoRep : Representation := .objects none [] [prop "__proto__" intRepS, prop "x\"y" (.string none [])] []
#guard refusedAt ["x\"y"] escapedProtoRep
def mapNumberRep : Representation := .objects none [] [] [{ parameter := .number none [], type := intRepS }]
#guard refusedAt ["indexSignatures[0]", "parameter"] mapNumberRep
def restRep : Representation := .objects none [] [prop "a" intRepS] [{ parameter := .string none [], type := intRepS }]
#guard refusedAt ["indexSignatures"] restRep
def oneOfRep : Representation := .union none [] [.string none [], .number none []] .oneOf
#guard refusedAt [] oneOfRep
def bigintLitRep : Representation := .literal none [] (.bigint 1)
#guard refusedAt [] bigintLitRep
-- an annotation on an unsupported node refuses (revision 5: the node's own refusal, after its bag)
#guard refusedAt ["annotations"] (.enum (some [⟨"parseOptions", .obj []⟩]) [] [])
-- rc.112's own persisted `Schema.Int` carries `arbitrary` (question 2 E9d): outside the eight keys
def rcIntRep : Representation := .number none [.filter ⟨"effect/schema/isInt", .null, none⟩
  (some [⟨"expected", .str "an integer"⟩, ⟨"arbitrary", .obj [("constraint", .obj [("integer", .bool true)])]⟩]) false]
#guard refusedAt ["check[0]", "annotations"] rcIntRep
#guard admits recordRep && admits mapRep && admits tagged3Rep && !admits restRep && explain recordRep == none

/-! ## 7. [S] The examples for the host harness (`S/host/q3-profile.ts`) -/

def examples : List (String × Representation) :=
  [ ("NAT", natRepS), ("INT", intRepS), ("RECORD", recordRep), ("OPTIONAL", optionalRep),
    ("OPTIONAL_UNDEF", optionalUndefRep), ("MAP", mapRep), ("TAGGED2", tagged2Rep),
    ("TAGGED3", tagged3Rep), ("LIT3_NESTED", lit3NestedRep), ("LIT3_FLAT", lit3FlatRep),
    ("TUPLE3", tuple3Rep), ("ARRAY", arrayRep), ("NESTED", validNestedRep),
    ("SPECIAL", specialRep), ("ESCAPED", escapedRep), ("MUTABLE", mutableRep),
    ("ESC_PROTO", escapedProtoRep), ("MAP_NUMBER", mapNumberRep), ("REST", restRep),
    ("RC_INT", rcIntRep) ]

#eval do
  for (name, rep) in examples do
    let expr := match text rep with
      | some t => t
      | none => "REFUSED"
    -- the renderer's own string literal (it escapes quote, backslash, newline, return, tab): JSON
    IO.println ("EXPR_" ++ name ++ ":" ++ Render.quoted house0 expr)
    IO.println ("REPR_" ++ name ++ ":" ++
      Render.quoted house0 (Effect4.Codegen.Schema.representationSource rep))

end SeatS.Readable

#print axioms SeatS.Readable.validateAnnotations
#print axioms SeatS.Readable.validateFilter
#print axioms SeatS.Readable.processProperties
#print axioms SeatS.Readable.structObject
#print axioms SeatS.Readable.keySpelling
#print axioms SeatS.Readable.toReadableSchema
#print axioms SeatS.Readable.admits
#print axioms SeatS.Readable.admits_iff_explain

