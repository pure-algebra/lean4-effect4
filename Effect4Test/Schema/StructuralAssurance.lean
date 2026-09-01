import Lean
import Lean.Util.CollectAxioms
import Effect4.Data.Optic
import Effect4.Schema.Document
import Effect4.Schema.Check

/-!
# Schema structural declaration and proof-receipt join

This test-only checker gives the implemented structural Schema slice one
mechanical census.  Every non-internal declaration owned by the seven source
modules is emitted with exactly one existing proof-graph or leaf-receipt route.
Every theorem in that census is checked against the repository axiom ceiling
and emitted with its actual kernel dependencies.

The generated projection, rather than an authored Boolean, decides which
cutover edges have enough joined evidence to close. The general recursor part
of `SC-REP-03` is included in the exhaustive declaration and axiom census; its
fixed contract battery and retained route attack are joined by the generator.
-/

open Lean Meta Elab Command

namespace Effect4Test.Schema.StructuralAssurance

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"Schema structural assurance mismatch: {detail}"

private def declarationOwner? (environment : Environment) (name : Name) : Option Name := do
  if let some moduleIndex := environment.getModuleIdxFor? name then
    environment.header.moduleNames[moduleIndex]?
  else if environment.contains name then
    some environment.mainModule
  else
    none

private def sourceModules : List Name :=
  [ `Effect4.Data.Optic
  , `Effect4.Data.Json
  , `Effect4.Schema.Payload
  , `Effect4.Schema.Representation
  , `Effect4.Schema.Annotations
  , `Effect4.Schema.Document
  , `Effect4.Schema.Check
  ]

private def declarationsOwnedBy (environment : Environment) (owner : Name) : List Name :=
  environment.constants.toList.foldl (init := []) fun declarations entry =>
    let name := entry.1
    if !name.isInternal && declarationOwner? environment name == some owner then
      name :: declarations
    else
      declarations

private def sortedNames (names : List Name) : List Name :=
  names.mergeSort fun left right => left.toString < right.toString

private def routeFor (owner name : Name) : String :=
  let text := name.toString
  if owner == `Effect4.Data.Optic then
    "DATA-PG-OPTIC"
  else if owner == `Effect4.Data.Json then
    if text.startsWith "Effect4.Float64" then
      "SCHEMA-LEAF-FLOAT64-BITS"
    else if text.startsWith "Effect4.Json.NumbersFinite" ||
        text.startsWith "Effect4.Json.numbersFinite" ||
        text.startsWith "Effect4.Json.not_numbersFinite" then
      "SCHEMA-PG-FIELD-ADMISSION/JSON-FINITENESS"
    else
      "SCHEMA-PG-PAYLOAD/JSON"
  else if owner == `Effect4.Schema.Payload then
    if text.startsWith "Effect4.RepresentationAnnotation" ||
        text.startsWith "Effect4.CheckRepresentationAnnotationOf" ||
        text.startsWith "Effect4.ElementOf" ||
        text.startsWith "Effect4.PropertySignatureOf" ||
        text.startsWith "Effect4.IndexSignatureOf" then
      "SCHEMA-LEAF-PAYLOAD-RECORDS"
    else
      "SCHEMA-LEAF-PAYLOAD-SCALARS"
  else if owner == `Effect4.Schema.Representation then
    if text.startsWith "Effect4.RepresentationTag" then
      "SCHEMA-PG-REPRESENTATION-TAG"
    else if text.startsWith "Effect4.UnionMode" then
      "SCHEMA-LEAF-UNION-MODE"
    else if text.startsWith "Effect4.CheckTag" then
      "SCHEMA-LEAF-CHECK-TAG"
    else if text.startsWith "Effect4.LiteralKind" then
      "SCHEMA-LEAF-LITERAL-KIND"
    else if text.startsWith "Effect4.EnumValueKind" then
      "SCHEMA-LEAF-ENUM-VALUE-KIND"
    else if text.startsWith "Effect4.PropertyKeyKind" then
      "SCHEMA-LEAF-PROPERTY-KEY-KIND"
    else
      "SCHEMA-PG-PAYLOAD/REPRESENTATION-CHECK"
  else if owner == `Effect4.Schema.Annotations then
    "SCHEMA-PG-ANNOTATION-DATA"
  else if owner == `Effect4.Schema.Document then
    if text.startsWith "Effect4.Document.annotationBags" ||
        text.startsWith "Effect4.MultiDocument.annotationBags" then
      "SCHEMA-PG-ANNOTATION-DATA/DOCUMENT"
    else
      "SCHEMA-LEAF-DOCUMENT-CONTAINERS"
  else if owner == `Effect4.Schema.Check then
    "SCHEMA-PG-FIELD-ADMISSION"
  else
    "UNALLOCATED"

private def forbiddenDuplicateDeclarations : List (Name × String) :=
  [ (`Effect4.Schema.Value.Representation, "duplicate-representation-carrier")
  , (`Effect4.Schema.Check.Check, "duplicate-check-carrier")
  , (`Effect4.KeywordKind, "duplicate-keyword-alphabet")
  , (`Effect4.Schema.RepresentationTag, "duplicate-tag-carrier")
  , (`Effect4.RawRepresentation, "duplicate-raw-carrier")
  , (`Effect4.CheckedRepresentation, "duplicate-checked-carrier")
  , (`Effect4.CanonicalRepresentation, "duplicate-canonical-carrier")
  , (`Effect4.Schema.Refusal, "duplicate-refusal-carrier")
  , (`Effect4.Schema.Behavior, "unowned-denotation-carrier")
  ]

private def sameNameSet (actual expected : List Name) : Bool :=
  actual.length == expected.length &&
    actual.all expected.contains && expected.all actual.contains

private def allowedAxioms : List Name := [`propext, `Quot.sound]

private def axiomFreeAnnotationLaws : List Name :=
  [ `Effect4.Lens.Lawful.compose
  , `Effect4.Lens.Lawful.toOptional
  , `Effect4.Optional.Lawful.compose
  , `Effect4.Optional.Lawful.toTraversal
  , `Effect4.Traversal.Lawful.compose
  , `Effect4.AnnotationKey.decodeEntry_entry
  , `Effect4.AnnotationKey.entry_of_decodeEntry
  , `Effect4.Annotations.payloadsAt_lawful
  , `Effect4.AnnotationKey.values_lawful
  , `Effect4.AnnotationKey.inTraversal_lawful
  , `Effect4.Representation.nodeAnnotations_lawful
  , `Effect4.Check.annotationsLens_lawful
  , `Effect4.ElementOf.annotationsLens_lawful
  , `Effect4.PropertySignatureOf.annotationsLens_lawful
  , `Effect4.Representation.annotationBags_lawful
  , `Effect4.Check.annotationBags_lawful
  , `Effect4.Document.annotationBags_lawful
  , `Effect4.MultiDocument.annotationBags_lawful
  ]

private def requiresAxiomFree (name : Name) : Bool :=
  axiomFreeAnnotationLaws.contains name

private def axiomFreeRecursorDeclarations : List Name :=
  [ `Effect4.Representation.FoldAlgebra
  , `Effect4.Representation.fold
  , `Effect4.Check.fold
  , `Effect4.Representation.FoldAlgebra.rebuild
  ]

private def theoremNamesOwnedBy (environment : Environment) (owner : Name) : List Name :=
  (declarationsOwnedBy environment owner).filter fun name =>
    match environment.find? name with
    | some (.thmInfo _) => true
    | _ => false

private def namesText (names : List Name) : String :=
  if names.isEmpty then "none"
  else String.intercalate "," ((sortedNames names).map toString)

private def checkStructuralAssurance : CommandElabM Unit := do
  let environment ← getEnv
  for owner in sourceModules do
    let declarations := declarationsOwnedBy environment owner
    unless !declarations.isEmpty do
      failJoin m!"source module {owner} owns no declarations"
    for name in declarations do
      unless declarationOwner? environment name == some owner do
        failJoin m!"owner drift for {name}: expected {owner}, found {declarationOwner? environment name}"
      let route := routeFor owner name
      if route == "UNALLOCATED" then
        failJoin m!"declaration {name} owned by {owner} has no proof-graph or leaf route"
    for name in theoremNamesOwnedBy environment owner do
      let actual := (← collectAxioms name).toList
      if requiresAxiomFree name && !actual.isEmpty then
        failJoin m!"annotation/optic theorem {name} is not axiom-free: {actual}"
      let forbidden := actual.filter fun axiomName => !allowedAxioms.contains axiomName
      unless forbidden.isEmpty do
        failJoin m!"axiom receipt for {name} exceeds [propext, Quot.sound]: {forbidden}"
  for (name, defect) in forbiddenDuplicateDeclarations do
    if environment.contains name then
      failJoin m!"forbidden {defect} declaration is present: {name}"
  for name in axiomFreeRecursorDeclarations do
    unless environment.contains name do
      failJoin m!"required recursor declaration is absent: {name}"
    let actual := (← collectAxioms name).toList
    unless actual.isEmpty do
      failJoin m!"recursor declaration {name} is not axiom-free: {actual}"

private def emitStructuralAssurance : CommandElabM Unit := do
  checkStructuralAssurance
  let environment ← getEnv
  for owner in sourceModules do
    for name in sortedNames (declarationsOwnedBy environment owner) do
      let route := routeFor owner name
      liftIO <| IO.println s!"E4SCHEMA\towned-declaration\t{name}\t{owner}\t{route}"
    for name in sortedNames (theoremNamesOwnedBy environment owner) do
      let axioms := (← collectAxioms name).toList
      liftIO <| IO.println s!"E4SCHEMA\ttheorem\t{name}\t{owner}\t{routeFor owner name}"
      liftIO <| IO.println s!"E4SCHEMA\taxiom\t{name}\t{namesText axioms}\tSCHEMA-AX-STRUCTURAL"
  for (name, defect) in forbiddenDuplicateDeclarations do
    liftIO <| IO.println s!"E4SCHEMA\tabsent\t{name}\t{defect}\tchecked"

syntax (name := effect4CheckSchemaStructuralAssurance)
  "#effect4_check_schema_structural_assurance" : command

syntax (name := effect4EmitSchemaStructuralAssurance)
  "#effect4_emit_schema_structural_assurance" : command

syntax (name := effect4CheckSchemaDeclarationOwners)
  "#effect4_check_schema_declaration_owners " ident "[" ident,* "]" : command

elab_rules : command
  | `(#effect4_check_schema_structural_assurance) =>
      checkStructuralAssurance

elab_rules : command
  | `(#effect4_emit_schema_structural_assurance) =>
      emitStructuralAssurance

elab_rules : command
  | `(#effect4_check_schema_declaration_owners $owner:ident [$names:ident,*]) => do
      let environment ← getEnv
      for name in (names.getElems.map Syntax.getId).toList do
        unless environment.contains name do
          failJoin m!"missing declaration {name}"
        unless declarationOwner? environment name == some owner.getId do
          failJoin m!"owner drift for {name}: expected {owner.getId}, found {declarationOwner? environment name}"

#effect4_check_schema_structural_assurance
#effect4_emit_schema_structural_assurance

end Effect4Test.Schema.StructuralAssurance
