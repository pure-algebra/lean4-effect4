import Effect4.Schema.Representation
import Effect4.Schema.Payload
import Effect4.Schema.Fold
import Effect4.Schema.Bridge
import TypeScript
import TypeScript.Render

open Effect4 TypeScript

namespace DefinitiveSchemaScout

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

/-- Process object properties: verifies no duplicates, refuses __proto__, validates property annotations. -/
def processProperties (properties : List (PropertySignatureOf (Result Expr))) : Result (List (String × Expr)) :=
  let rec go (seen : List String) (acc : List (String × Expr)) : List (PropertySignatureOf (Result Expr)) → Result (List (String × Expr))
    | [] => .ok acc.reverse
    | prop :: rest =>
        match prop.name with
        | .string name =>
            if seen.contains name then
              .error ⟨[name], s!"Duplicate object field '{name}' not admitted in readable profile (TS1117)"⟩
            else if name == "__proto__" then
              .error ⟨[name], "Field '__proto__' requires computed property syntax not yet supported in target AST"⟩
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
    if !indexes.isEmpty then .error ⟨[], "Index signatures not supported in Stage 1"⟩
    let fieldExprs ← processProperties properties
    .ok (.call (.ident "Schema.Struct") [.objectQuoted fieldExprs])
  representation_union annotations checks types mode := do
    validateAnnotations [] annotations
    if !checks.isEmpty then .error ⟨[], "Checks on unions not supported"⟩
    if mode != UnionMode.anyOf then .error ⟨[], "oneOf union mode not supported"⟩
    let memberExprs ← (listZipIdx types).mapM fun (i, t) => prefixPath s!"union[{i}]" t
    .ok (.call (.ident "Schema.Union") [.arr memberExprs])
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

-- 6. "__proto__" is REFUSED with exact path ["config", "__proto__"]
def protoRep : Representation :=
  .objects none []
    [ { name := .string "config"
      , type := .objects none []
          [ { name := .string "__proto__", type := .number none [], isOptional := false, isMutable := false, annotations := none } ]
          []
      , isOptional := false, isMutable := false, annotations := none } ]
    []

#guard match toReadableSchema protoRep with
  | .error ⟨["config", "__proto__"], reason⟩ => reason.contains "requires computed property syntax"
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

#guard match toReadableSchema validNestedRep with
  | .ok (.call (.ident "Schema.Struct") [.objectQuoted [("user", .call (.ident "Schema.Struct") [.objectQuoted [("age", .ident "Schema.Natural"), ("name", .ident "Schema.String")]])]]) => true
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

end DefinitiveSchemaScout

#print axioms DefinitiveSchemaScout.validateAnnotations
#print axioms DefinitiveSchemaScout.validateFilter
#print axioms DefinitiveSchemaScout.processProperties
#print axioms DefinitiveSchemaScout.toReadableSchema

namespace FinalSchemaAudit
open Effect4 TypeScript DefinitiveSchemaScout
set_option maxRecDepth 4096

def field (name : String) (rep : Representation) : PropertySignatureOf Representation :=
  ⟨.string name, rep, false, false, none⟩
def uniqueRecord : Representation := .objects none []
  [field "a" (.number none []), field "b" (.string none [])] []
def bad : Representation := .declaration ⟨"custom/missing", .null⟩ none [] []
def intWithChildren (children : Option (List Representation)) : Representation :=
  .number none [.filter ⟨"effect/schema/isInt", .null, children⟩ none false]
def nonAdjacentDuplicate : Representation := .objects none []
  [field "a" (.number none []), field "b" (.string none []), field "a" (.string none [])] []
def nestedDuplicate : Representation := .objects none [] [field "config" nonAdjacentDuplicate] []
def modifierRecord : Representation := .objects none [] [
  {name := .string "a-b", type := .string none [], isOptional := true,
   isMutable := true, annotations := none}] []
def escapedRecord : Representation := .objects none [] [field "x\"\n\\y" (.string none [])] []
def objectWithOption (option : String) : Representation := .objects
  (some [⟨"parseOptions", .obj [("onExcessProperty", .str option)]⟩]) []
  [field "a" (.number none [])] []
def intWithDisabledCheck : Representation := .number none [
  .filter ⟨"effect/schema/isInt", .null, none⟩
    (some [⟨"parseOptions", .obj [("disableChecks", .bool true)]⟩]) false]

theorem semantic_object_annotation_refused (option : String) :
    toReadableSchema (objectWithOption option) = .error ⟨["annotations"], "Semantic or unadmitted annotation 'parseOptions' not supported in readable profile"⟩ := rfl
theorem check_disabling_annotation_refused :
    toReadableSchema intWithDisabledCheck = .error ⟨["check[0]", "annotations"], "Semantic or unadmitted annotation 'parseOptions' not supported in readable profile"⟩ := rfl

theorem child_error_preserved : toReadableSchema (intWithChildren (some [.string none [], bad])) =
    .error ⟨["check[0]", "schemas[1]"], "Custom declarations not supported in readable profile"⟩ := rfl
theorem empty_children_normalized : toReadableSchema (intWithChildren (some [])) =
    toReadableSchema (intWithChildren none) := rfl
theorem nonempty_children_refused : toReadableSchema (intWithChildren (some [.string none []])) =
    .error ⟨["check[0]", "schemas"], "Child schemas on canonical check 'effect/schema/isInt' not supported in readable profile"⟩ := rfl
theorem duplicate_refused : toReadableSchema nestedDuplicate =
    .error ⟨["config", "a"], "Duplicate object field 'a' not admitted in readable profile (TS1117)"⟩ := rfl

-- Keep former rejecting controls rather than replacing them with only the latest examples.
#guard match toReadableSchema (.number none [.filter ⟨"custom/unknown", .null, none⟩ none false]) with
  | .error ⟨["check[0]"], _⟩ => true
  | _ => false
#guard match toReadableSchema (.number none [.filter ⟨"effect/schema/isInt", .bool true, none⟩ none false]) with
  | .error ⟨["check[0]"], _⟩ => true
  | _ => false
#guard match toReadableSchema (.number none [.filter ⟨"effect/schema/isInt", .null, none⟩ none true]) with
  | .error ⟨["check[0]"], _⟩ => true
  | _ => false
#guard match toReadableSchema (.number none [.filterGroup none none [Effect4.Schema.Bridge.isIntCheck]]) with
  | .error ⟨["check[0]"], _⟩ => true
  | _ => false
#guard match toReadableSchema (.number none [Effect4.Schema.Bridge.isIntCheck,
    .filter ⟨"effect/schema/isGreaterThanOrEqualTo", .obj [("minimum", .number (Float64.ofBits 0x3ff0000000000000))], none⟩ none false]) with
  | .error ⟨["check[1]"], _⟩ => true
  | _ => false
#guard match toReadableSchema (.objects none [] [field "left" uniqueRecord, field "right" uniqueRecord] []) with
  | .ok _ => true
  | _ => false

#print axioms child_error_preserved
#print axioms empty_children_normalized
#print axioms nonempty_children_refused
#print axioms duplicate_refused
#print axioms semantic_object_annotation_refused
#print axioms check_disabling_annotation_refused
#print axioms DefinitiveSchemaScout.validateFilter
#print axioms DefinitiveSchemaScout.processProperties
#print axioms DefinitiveSchemaScout.toReadableSchema

def badAnnotations : Annotations := some [⟨"parseOptions", .obj []⟩]
def docAnnotations : Annotations := some [⟨"title", .str "Example"⟩, ⟨"description", .str "Fixture"⟩]
def annotateAcceptedNodes : List (Annotations → Representation) := [
  fun a => .null a [], fun a => .undefined a [], fun a => .void a [],
  fun a => .never a [], fun a => .unknown a [], fun a => .any a [],
  fun a => .string a [], fun a => .number a [], fun a => .boolean a [],
  fun a => .bigint a [], fun a => .symbol a [],
  fun a => .literal a [] (.string "x"), fun a => .objectKeyword a [],
  fun a => .arrays a [] [⟨false, .string none [], none⟩] [],
  fun a => .objects a [] [field "a" (.number none [])] [],
  fun a => .union a [] [.string none [], .number none []] .anyOf]

def refusedAt (path : List String) (rep : Representation) : Bool :=
  match toReadableSchema rep with
  | .error e => e.path == path
  | .ok _ => false
def emits (rep : Representation) : Bool :=
  match toReadableSchema rep with
  | .ok _ => true
  | .error _ => false

-- Covers every accepted node constructor; neighbors prevent an always-refusing validator.
#guard annotateAcceptedNodes.all fun f => refusedAt ["annotations"] (f badAnnotations)
#guard annotateAcceptedNodes.all fun f => emits (f docAnnotations)
#guard annotateAcceptedNodes.all fun f => emits (f (some [])) && emits (f none)

def annotatedProperty (a : Annotations) : Representation := .objects none []
  [{name := .string "child", type := .string none [], isOptional := false,
    isMutable := false, annotations := a}] []
def annotatedElement (a : Annotations) : Representation := .arrays none []
  [⟨false, .string none [], a⟩] []
def annotatedFilter (a : Annotations) : Representation := .number none [
  .filter ⟨"effect/schema/isInt", .null, none⟩ a false]

#guard refusedAt ["child", "annotations"] (annotatedProperty badAnnotations)
#guard refusedAt ["elements[0]", "annotations"] (annotatedElement badAnnotations)
#guard refusedAt ["check[0]", "annotations"] (annotatedFilter badAnnotations)
#guard emits (annotatedProperty docAnnotations) && emits (annotatedElement docAnnotations)
  && emits (annotatedFilter docAnnotations)
#guard refusedAt ["elements[0]", "annotations"]
  (.arrays none [] [⟨false, .string badAnnotations [], none⟩] [])
#guard refusedAt ["rest[0]", "annotations"] (.arrays none [] [] [.string badAnnotations []])
#guard refusedAt ["union[1]", "annotations"] (.union none [] [.string none [], .number badAnnotations []] .anyOf)
#guard refusedAt ["outer", "child", "annotations"]
  (.objects none [] [field "outer" (annotatedProperty badAnnotations)] [])
#guard refusedAt ["check[0]", "schemas[0]", "annotations"]
  (intWithChildren (some [.string badAnnotations []]))
#guard refusedAt ["annotations"] (.string
  (some [⟨"title", .str "Okay"⟩, ⟨"unknownKey", .null⟩, ⟨"description", .str "Okay"⟩]) [])
#guard refusedAt ["annotations"] (.string (some [⟨"brands", .arr [.str "Brand"]⟩]) [])
#guard allowedDocKeys.all fun key => emits (.string (some [⟨key, .str "Fixture"⟩]) [])

-- Both semantic-option variants must now refuse; the previous erasure equation is not retained.
#guard refusedAt ["annotations"] (objectWithOption "error")
#guard refusedAt ["annotations"] (objectWithOption "preserve")

#eval do
  for (name, rep) in [
    ("NAT", natRep), ("INT", intRep), ("NUMBER", .number none []),
    ("NESTED", validNestedRep), ("UNIQUE", uniqueRecord),
    ("DUP", nestedDuplicate), ("CHECK_CHILD", intWithChildren (some [bad])),
    ("MODIFIER", modifierRecord), ("ESCAPE", escapedRecord),
    ("ANNOT_ERROR", objectWithOption "error"),
    ("ANNOT_PRESERVE", objectWithOption "preserve"),
    ("ANNOT_DISABLE", intWithDisabledCheck),
    ("DOC_STRING", .string docAnnotations []),
    ("DOC_PROPERTY", annotatedProperty docAnnotations),
    ("DOC_ELEMENT", annotatedElement docAnnotations),
    ("DOC_FILTER", annotatedFilter docAnnotations),
    ("TUPLE", .arrays none [] [⟨false, .string none [], none⟩] []),
    ("ARRAY", .arrays none [] [] [.string none []]),
    ("UNION", .union none [] [.string none [], .number none []] .anyOf)] do
    match toReadableSchema rep with
    | .ok e => IO.println ("EXPR_" ++ name ++ ":" ++ Render.expr house0 0 e)
    | .error _ => IO.println ("EXPR_" ++ name ++ ":REFUSED")

end FinalSchemaAudit
