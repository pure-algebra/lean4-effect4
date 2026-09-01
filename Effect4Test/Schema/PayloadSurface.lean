import Lean
import Effect4.Schema.Check

/-!
# Schema payload declaration-surface gate

This test inspects Lean's elaborated environment.  It does not scrape source
text.  The tables below freeze the payload carrier's public declaration
surface: declaration kind, universe/parameter/index arity, mutual-family
membership, constructor count and order, fully-qualified constructor names,
full constructor types, structure field order and projection types, and the
four applied type aliases.

The three commands are intentionally test-only metaprogramming API.  Synthetic
mutation fixtures import this module and use the same checker, so a mutation is
killed by the detector after Lean has successfully elaborated the mutant type.
-/

open Lean Meta Elab Term Elab.Command

namespace Effect4Test.Schema.PayloadSurface

declare_syntax_cat effect4SurfaceEntry
syntax "| " ident " : " term : effect4SurfaceEntry

syntax (name := effect4CheckInductiveSurface)
  "#effect4_check_inductive_surface " ident
  " levels " num " params " num " indices " num
  " family " "[" ident,* "]" " where " ppLine effect4SurfaceEntry* : command

syntax (name := effect4CheckStructureSurface)
  "#effect4_check_structure_surface " ident
  " levels " num " params " num
  " constructor " effect4SurfaceEntry
  " fields " ppLine effect4SurfaceEntry* : command

syntax (name := effect4CheckAbbrevSurface)
  "#effect4_check_abbrev_surface " ident
  " levels " num " := " term : command

syntax (name := effect4CheckDeclarationOwners)
  "#effect4_check_declaration_owners " ident " [" ident,* "]" : command

syntax (name := effect4CheckPublicTypeSurface)
  "#effect4_check_public_type_surface " ident " [" ident,* "]" : command

private structure ExpectedEntry where
  name : Name
  typeSyntax : Syntax

private def parseEntry (entry : Syntax) : CommandElabM ExpectedEntry := do
  match entry with
  | `(effect4SurfaceEntry| | $name:ident : $type:term) =>
      pure { name := name.getId, typeSyntax := type }
  | _ => throwUnsupportedSyntax

private def parseEntries (entries : Array Syntax) : CommandElabM (Array ExpectedEntry) :=
  entries.mapM parseEntry

private def failSurface (subject : Name) (detail : MessageData) : MetaM α :=
  throwError m!"schema payload surface mismatch for {subject}: {detail}"

private def declarationModule (env : Environment) (name : Name) : MetaM Name := do
  let some moduleIndex := env.getModuleIdxFor? name
    | failSurface name "declaration is absent or local"
  let some moduleName := env.header.moduleNames[moduleIndex]?
    | failSurface name m!"invalid declaration module index {moduleIndex}"
  pure moduleName

private def checkDeclarationOwners (expectedModule : Name)
    (names : List Name) : MetaM Unit := do
  let env ← getEnv
  for name in names do
    let actualModule ← declarationModule env name
    unless actualModule == expectedModule do
      failSurface name m!"owner: expected {expectedModule}, found {actualModule}"

private def isGeneratedTypeCompanion (expected : List Name) (name : Name) : Bool :=
  match name with
  | .str parent suffix =>
      (suffix == "noConfusionType" || suffix == "ctorElimType") &&
        expected.contains parent
  | _ => false

private def isPublicTypeDeclaration (expected : List Name)
    (name : Name) (info : ConstantInfo) : MetaM Bool := do
  if name.isInternal then
    return false
  if isGeneratedTypeCompanion expected name then
    return false
  match info with
  | .inductInfo _ => return true
  | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
      forallTelescopeReducing info.type fun _ result => do
        return (← whnf result).isSort
  | _ => return false

private def checkPublicTypeSurface (namePrefix : Name) (expected : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut actual : List Name := []
  for (name, info) in env.constants.toList do
    if namePrefix.isPrefixOf name && (← isPublicTypeDeclaration expected name info) then
      actual := name :: actual
  let unexpected := actual.filter fun name => !expected.contains name
  let missing := expected.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    failSurface namePrefix m!"public type census: unexpected {unexpected.reverse}; missing {missing}"

private def checkNat (subject : Name) (label : String) (actual expected : Nat) : MetaM Unit :=
  unless actual == expected do
    failSurface subject m!"{label}: expected {expected}, found {actual}"

private def checkNameList (subject : Name) (label : String)
    (actual expected : List Name) : MetaM Unit :=
  unless actual == expected do
    failSurface subject m!"{label}: expected {expected}, found {actual}"

private def forallBinderInfos : Expr → List BinderInfo
  | .forallE _ _ body info => info :: forallBinderInfos body
  | _ => []

private def checkConstantType (subject : Name) (typeSyntax : Syntax) : TermElabM Expr := do
  let actualTerm ← mkConstWithFreshMVarLevels subject
  let actualType ← inferType actualTerm
  let expectedType ← Term.elabType typeSyntax
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq actualType expectedType do
    let actualType ← instantiateMVars actualType
    let expectedType ← instantiateMVars expectedType
    failSurface subject m!"type: expected {expectedType}, found {actualType}"
  let actualType ← instantiateMVars actualType
  let expectedType ← instantiateMVars expectedType
  unless forallBinderInfos actualType == forallBinderInfos expectedType do
    failSurface subject
      m!"binder visibility: expected {repr (forallBinderInfos expectedType)}, found {repr (forallBinderInfos actualType)}"
  pure expectedType

private def checkInductiveSurface (typeName : Name)
    (levelCount parameterCount indexCount : Nat)
    (familyNames : List Name) (expected : Array ExpectedEntry) : TermElabM Unit := do
  let env ← getEnv
  let info ← match env.find? typeName with
    | some (.inductInfo info) => pure info
    | some _ => failSurface typeName "expected an inductive declaration"
    | none => failSurface typeName "declaration is absent"
  checkNat typeName "universe parameter count" info.levelParams.length levelCount
  checkNat typeName "type parameter count" info.numParams parameterCount
  checkNat typeName "index count" info.numIndices indexCount
  checkNameList typeName "mutual-family names" info.all familyNames
  if info.isUnsafe then
    failSurface typeName "the inductive declaration is unsafe"
  let expectedNames := expected.toList.map (fun entry => entry.name)
  checkNameList typeName "constructor names/order" info.ctors expectedNames
  for h : i in [:expected.size] do
    let entry := expected[i]
    let ctorInfo ← match env.find? entry.name with
      | some (.ctorInfo info) => pure info
      | some _ => failSurface entry.name "expected a constructor declaration"
      | none => failSurface entry.name "constructor declaration is absent"
    unless ctorInfo.induct == typeName do
      failSurface entry.name m!"owner: expected {typeName}, found {ctorInfo.induct}"
    checkNat entry.name "constructor index" ctorInfo.cidx i
    checkNat entry.name "constructor parameter count" ctorInfo.numParams parameterCount
    if ctorInfo.isUnsafe then
      failSurface entry.name "the constructor declaration is unsafe"
    let expectedType ← checkConstantType entry.name entry.typeSyntax
    let expectedArity := (forallBinderInfos expectedType).length
    if expectedArity < parameterCount then
      failSurface entry.name
        m!"expected constructor type has only {expectedArity} binders for {parameterCount} parameters"
    checkNat entry.name "constructor field count" ctorInfo.numFields
      (expectedArity - parameterCount)

private def checkStructureSurface (typeName : Name) (levelCount parameterCount : Nat)
    (ctorExpected : ExpectedEntry) (fieldEntries : Array ExpectedEntry) : TermElabM Unit := do
  checkInductiveSurface typeName levelCount parameterCount 0 [typeName] #[ctorExpected]
  let env ← getEnv
  let some structureInfo := getStructureInfo? env typeName
    | failSurface typeName "expected structure metadata"
  unless structureInfo.parentInfo.isEmpty do
    failSurface typeName "expected no parent structures"
  let expectedFieldNames := fieldEntries.toList.map fun entry =>
    Name.mkSimple entry.name.getString!
  checkNameList typeName "structure field names/order"
    structureInfo.fieldNames.toList expectedFieldNames
  for entry in fieldEntries do
    let fieldName := Name.mkSimple entry.name.getString!
    let some fieldInfo := getFieldInfo? env typeName fieldName
      | failSurface entry.name "expected structure-field metadata"
    unless fieldInfo.projFn == entry.name do
      failSurface entry.name m!"projection name: expected {entry.name}, found {fieldInfo.projFn}"
    discard <| checkConstantType entry.name entry.typeSyntax

private def checkAbbrevSurface (name : Name) (levelCount : Nat)
    (expectedSyntax : Syntax) : TermElabM Unit := do
  let env ← getEnv
  let info ← match env.find? name with
    | some (.defnInfo info) => pure info
    | some _ => failSurface name "expected an abbreviation declaration"
    | none => failSurface name "abbreviation declaration is absent"
  checkNat name "universe parameter count" info.levelParams.length levelCount
  match info.hints with
  | .abbrev => pure ()
  | _ => failSurface name "expected reducibility hint .abbrev"
  if info.safety != .safe then
    failSurface name "the abbreviation declaration is not safe"
  let actual ← mkConstWithFreshMVarLevels name
  let expected ← Term.elabType expectedSyntax
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq actual expected do
    let actual ← instantiateMVars actual
    let expected ← instantiateMVars expected
    failSurface name m!"abbreviation body: expected {expected}, found {actual}"

elab_rules : command
  | `(#effect4_check_inductive_surface $typeName:ident
      levels $levelCount:num params $parameterCount:num indices $indexCount:num
      family [$familyName:ident,*] where $entries:effect4SurfaceEntry*) => do
      let entries ← parseEntries entries
      liftTermElabM <| checkInductiveSurface typeName.getId levelCount.getNat
        parameterCount.getNat indexCount.getNat
        (familyName.getElems.map Syntax.getId).toList entries

elab_rules : command
  | `(#effect4_check_structure_surface $typeName:ident
      levels $levelCount:num params $parameterCount:num
      constructor $ctorEntry:effect4SurfaceEntry
      fields $fieldEntry:effect4SurfaceEntry*) => do
      let ctorExpected ← parseEntry ctorEntry
      let fieldEntries ← parseEntries fieldEntry
      liftTermElabM <| checkStructureSurface typeName.getId levelCount.getNat
        parameterCount.getNat ctorExpected fieldEntries

elab_rules : command
  | `(#effect4_check_abbrev_surface $name:ident levels $levelCount:num := $expected:term) =>
      liftTermElabM <| checkAbbrevSurface name.getId levelCount.getNat expected

elab_rules : command
  | `(#effect4_check_declaration_owners $expectedModule:ident [$names:ident,*]) =>
      liftTermElabM <| checkDeclarationOwners expectedModule.getId
        (names.getElems.map Syntax.getId).toList

elab_rules : command
  | `(#effect4_check_public_type_surface $namePrefix:ident [$names:ident,*]) =>
      liftTermElabM <| checkPublicTypeSurface namePrefix.getId
        (names.getElems.map Syntax.getId).toList

/-! ## D0–D1: binary64 datum and raw JSON -/

#effect4_check_structure_surface Effect4.Float64 levels 0 params 0
  constructor | Effect4.Float64.mk : UInt64 → Effect4.Float64
  fields
  | Effect4.Float64.bits : Effect4.Float64 → UInt64

#effect4_check_inductive_surface Effect4.Json levels 0 params 0 indices 0
  family [Effect4.Json] where
  | Effect4.Json.null : Effect4.Json
  | Effect4.Json.bool : Bool → Effect4.Json
  | Effect4.Json.number : Effect4.Float64 → Effect4.Json
  | Effect4.Json.str : String → Effect4.Json
  | Effect4.Json.arr : List Effect4.Json → Effect4.Json
  | Effect4.Json.obj : List (String × Effect4.Json) → Effect4.Json

/-! ## D2: scalar, key, and entry carriers -/

#effect4_check_structure_surface Effect4.ReferenceKey levels 0 params 0
  constructor | Effect4.ReferenceKey.mk : String → Effect4.ReferenceKey
  fields
  | Effect4.ReferenceKey.value : Effect4.ReferenceKey → String

#effect4_check_structure_surface Effect4.GlobalSymbolKey levels 0 params 0
  constructor | Effect4.GlobalSymbolKey.mk : String → Effect4.GlobalSymbolKey
  fields
  | Effect4.GlobalSymbolKey.key : Effect4.GlobalSymbolKey → String

#effect4_check_structure_surface Effect4.AnnotationEntry levels 0 params 0
  constructor | Effect4.AnnotationEntry.mk : String → Effect4.Json → Effect4.AnnotationEntry
  fields
  | Effect4.AnnotationEntry.key : Effect4.AnnotationEntry → String
  | Effect4.AnnotationEntry.payload : Effect4.AnnotationEntry → Effect4.Json

#effect4_check_abbrev_surface Effect4.Annotations levels 0 :=
  Option (List Effect4.AnnotationEntry)

#effect4_check_inductive_surface Effect4.LiteralValue levels 0 params 0 indices 0
  family [Effect4.LiteralValue] where
  | Effect4.LiteralValue.string : String → Effect4.LiteralValue
  | Effect4.LiteralValue.number : Effect4.Float64 → Effect4.LiteralValue
  | Effect4.LiteralValue.bigint : Int → Effect4.LiteralValue
  | Effect4.LiteralValue.boolean : Bool → Effect4.LiteralValue

#effect4_check_inductive_surface Effect4.EnumValue levels 0 params 0 indices 0
  family [Effect4.EnumValue] where
  | Effect4.EnumValue.string : String → Effect4.EnumValue
  | Effect4.EnumValue.number : Effect4.Float64 → Effect4.EnumValue

#effect4_check_structure_surface Effect4.EnumEntry levels 0 params 0
  constructor | Effect4.EnumEntry.mk : String → Effect4.EnumValue → Effect4.EnumEntry
  fields
  | Effect4.EnumEntry.name : Effect4.EnumEntry → String
  | Effect4.EnumEntry.value : Effect4.EnumEntry → Effect4.EnumValue

#effect4_check_inductive_surface Effect4.PropertyKey levels 0 params 0 indices 0
  family [Effect4.PropertyKey] where
  | Effect4.PropertyKey.string : String → Effect4.PropertyKey
  | Effect4.PropertyKey.number : Effect4.Float64 → Effect4.PropertyKey
  | Effect4.PropertyKey.globalSymbol : Effect4.GlobalSymbolKey → Effect4.PropertyKey

/-! ## D3: parameterized record children -/

#effect4_check_structure_surface Effect4.RepresentationAnnotation levels 0 params 0
  constructor | Effect4.RepresentationAnnotation.mk :
    String → Effect4.Json → Effect4.RepresentationAnnotation
  fields
  | Effect4.RepresentationAnnotation.id : Effect4.RepresentationAnnotation → String
  | Effect4.RepresentationAnnotation.payload :
      Effect4.RepresentationAnnotation → Effect4.Json

#effect4_check_structure_surface Effect4.CheckRepresentationAnnotationOf levels 0 params 1
  constructor | Effect4.CheckRepresentationAnnotationOf.mk :
    { α : Type } → String → Effect4.Json → Option (List α) →
      Effect4.CheckRepresentationAnnotationOf α
  fields
  | Effect4.CheckRepresentationAnnotationOf.id :
      { α : Type } → Effect4.CheckRepresentationAnnotationOf α → String
  | Effect4.CheckRepresentationAnnotationOf.payload :
      { α : Type } → Effect4.CheckRepresentationAnnotationOf α → Effect4.Json
  | Effect4.CheckRepresentationAnnotationOf.schemas :
      { α : Type } → Effect4.CheckRepresentationAnnotationOf α → Option (List α)

#effect4_check_structure_surface Effect4.ElementOf levels 0 params 1
  constructor | Effect4.ElementOf.mk :
    { α : Type } → Bool → α → Effect4.Annotations → Effect4.ElementOf α
  fields
  | Effect4.ElementOf.isOptional : { α : Type } → Effect4.ElementOf α → Bool
  | Effect4.ElementOf.type : { α : Type } → Effect4.ElementOf α → α
  | Effect4.ElementOf.annotations :
      { α : Type } → Effect4.ElementOf α → Effect4.Annotations

#effect4_check_structure_surface Effect4.PropertySignatureOf levels 0 params 1
  constructor | Effect4.PropertySignatureOf.mk :
    { α : Type } → Effect4.PropertyKey → α → Bool → Bool →
      Effect4.Annotations → Effect4.PropertySignatureOf α
  fields
  | Effect4.PropertySignatureOf.name :
      { α : Type } → Effect4.PropertySignatureOf α → Effect4.PropertyKey
  | Effect4.PropertySignatureOf.type :
      { α : Type } → Effect4.PropertySignatureOf α → α
  | Effect4.PropertySignatureOf.isOptional :
      { α : Type } → Effect4.PropertySignatureOf α → Bool
  | Effect4.PropertySignatureOf.isMutable :
      { α : Type } → Effect4.PropertySignatureOf α → Bool
  | Effect4.PropertySignatureOf.annotations :
      { α : Type } → Effect4.PropertySignatureOf α → Effect4.Annotations

#effect4_check_structure_surface Effect4.IndexSignatureOf levels 0 params 1
  constructor | Effect4.IndexSignatureOf.mk :
    { α : Type } → α → α → Effect4.IndexSignatureOf α
  fields
  | Effect4.IndexSignatureOf.parameter :
      { α : Type } → Effect4.IndexSignatureOf α → α
  | Effect4.IndexSignatureOf.type :
      { α : Type } → Effect4.IndexSignatureOf α → α

/-! ## D4: mutual representation/check carrier -/

#effect4_check_inductive_surface Effect4.Representation levels 0 params 0 indices 0
  family [Effect4.Representation, Effect4.Check] where
  | Effect4.Representation.declaration :
      Effect4.RepresentationAnnotation → Effect4.Annotations →
      List Effect4.Representation → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.reference : Effect4.ReferenceKey → Effect4.Representation
  | Effect4.Representation.suspend :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation →
      Effect4.Representation
  | Effect4.Representation.null :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.undefined :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.void :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.never :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.unknown :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.any :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.string :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.number :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.boolean :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.bigint :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.symbol :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.literal :
      Effect4.Annotations → List Effect4.Check → Effect4.LiteralValue →
      Effect4.Representation
  | Effect4.Representation.uniqueSymbol :
      Effect4.Annotations → List Effect4.Check → Effect4.GlobalSymbolKey →
      Effect4.Representation
  | Effect4.Representation.objectKeyword :
      Effect4.Annotations → List Effect4.Check → Effect4.Representation
  | Effect4.Representation.enum :
      Effect4.Annotations → List Effect4.Check → List Effect4.EnumEntry →
      Effect4.Representation
  | Effect4.Representation.templateLiteral :
      Effect4.Annotations → List Effect4.Check → List Effect4.Representation →
      Effect4.Representation
  | Effect4.Representation.arrays :
      Effect4.Annotations → List Effect4.Check →
      List (Effect4.ElementOf Effect4.Representation) →
      List Effect4.Representation → Effect4.Representation
  | Effect4.Representation.objects :
      Effect4.Annotations → List Effect4.Check →
      List (Effect4.PropertySignatureOf Effect4.Representation) →
      List (Effect4.IndexSignatureOf Effect4.Representation) → Effect4.Representation
  | Effect4.Representation.union :
      Effect4.Annotations → List Effect4.Check → List Effect4.Representation →
      Effect4.UnionMode → Effect4.Representation

#effect4_check_inductive_surface Effect4.Check levels 0 params 0 indices 0
  family [Effect4.Representation, Effect4.Check] where
  | Effect4.Check.filter :
      Effect4.CheckRepresentationAnnotationOf Effect4.Representation →
      Effect4.Annotations → Bool → Effect4.Check
  | Effect4.Check.filterGroup :
      Option (Effect4.CheckRepresentationAnnotationOf Effect4.Representation) →
      Effect4.Annotations → List Effect4.Check → Effect4.Check

#effect4_check_abbrev_surface Effect4.Element levels 0 :=
  Effect4.ElementOf Effect4.Representation

#effect4_check_abbrev_surface Effect4.PropertySignature levels 0 :=
  Effect4.PropertySignatureOf Effect4.Representation

#effect4_check_abbrev_surface Effect4.IndexSignature levels 0 :=
  Effect4.IndexSignatureOf Effect4.Representation

#effect4_check_abbrev_surface Effect4.CheckRepresentationAnnotation levels 0 :=
  Effect4.CheckRepresentationAnnotationOf Effect4.Representation

/-! ## D6: document containers -/

#effect4_check_structure_surface Effect4.ReferenceEntry levels 0 params 0
  constructor | Effect4.ReferenceEntry.mk :
    String → Effect4.Representation → Effect4.ReferenceEntry
  fields
  | Effect4.ReferenceEntry.key : Effect4.ReferenceEntry → String
  | Effect4.ReferenceEntry.representation :
      Effect4.ReferenceEntry → Effect4.Representation

#effect4_check_structure_surface Effect4.Document levels 0 params 0
  constructor | Effect4.Document.mk :
    Effect4.Representation → List Effect4.ReferenceEntry → Effect4.Document
  fields
  | Effect4.Document.representation : Effect4.Document → Effect4.Representation
  | Effect4.Document.references : Effect4.Document → List Effect4.ReferenceEntry

#effect4_check_structure_surface Effect4.MultiDocument levels 0 params 0
  constructor | Effect4.MultiDocument.mk :
    List Effect4.Representation → List Effect4.ReferenceEntry → Effect4.MultiDocument
  fields
  | Effect4.MultiDocument.representations :
      Effect4.MultiDocument → List Effect4.Representation
  | Effect4.MultiDocument.references :
      Effect4.MultiDocument → List Effect4.ReferenceEntry

end Effect4Test.Schema.PayloadSurface
