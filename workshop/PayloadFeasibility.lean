import Effect4.Data.Json

set_option autoImplicit false

namespace Effect4.Workshop.PayloadFeasibility

/- This file is an isolated feasibility probe.  It deliberately does not
   contribute declarations to the library surface. -/

structure ReferenceKey where
  value : String
deriving DecidableEq

structure GlobalSymbolKey where
  key : String
deriving DecidableEq

structure AnnotationEntry where
  key : String
  payload : Effect4.Json
deriving DecidableEq

abbrev Annotations := Option (List AnnotationEntry)

inductive LiteralValue where
  | string (value : String)
  | number (value : Effect4.Float64)
  | bigint (value : Int)
  | boolean (value : Bool)
deriving DecidableEq

inductive EnumValue where
  | string (value : String)
  | number (value : Effect4.Float64)
deriving DecidableEq

structure EnumEntry where
  name : String
  value : EnumValue
deriving DecidableEq

inductive PropertyKey where
  | string (value : String)
  | number (value : Effect4.Float64)
  | globalSymbol (value : GlobalSymbolKey)
deriving DecidableEq

structure RepresentationAnnotation where
  id : String
  payload : Effect4.Json
deriving DecidableEq

structure CheckRepresentationAnnotationOf (alpha : Type) where
  id : String
  payload : Effect4.Json
  schemas : Option (List alpha)
deriving DecidableEq, BEq

structure ElementOf (alpha : Type) where
  isOptional : Bool
  type : alpha
  annotations : Annotations
deriving DecidableEq, BEq

structure PropertySignatureOf (alpha : Type) where
  name : PropertyKey
  type : alpha
  isOptional : Bool
  isMutable : Bool
  annotations : Annotations
deriving DecidableEq, BEq

structure IndexSignatureOf (alpha : Type) where
  parameter : alpha
  type : alpha
deriving DecidableEq, BEq

inductive UnionMode where
  | anyOf
  | oneOf
deriving DecidableEq

mutual

inductive Representation where
  | declaration (representation : RepresentationAnnotation)
      (annotations : Annotations) (typeParameters : List Representation)
      (checks : List Check)
  | reference (key : ReferenceKey)
  | suspend (annotations : Annotations) (checks : List Check)
      (thunk : Representation)
  | null (annotations : Annotations) (checks : List Check)
  | undefined (annotations : Annotations) (checks : List Check)
  | void (annotations : Annotations) (checks : List Check)
  | never (annotations : Annotations) (checks : List Check)
  | unknown (annotations : Annotations) (checks : List Check)
  | any (annotations : Annotations) (checks : List Check)
  | string (annotations : Annotations) (checks : List Check)
  | number (annotations : Annotations) (checks : List Check)
  | boolean (annotations : Annotations) (checks : List Check)
  | bigint (annotations : Annotations) (checks : List Check)
  | symbol (annotations : Annotations) (checks : List Check)
  | literal (annotations : Annotations) (checks : List Check)
      (value : LiteralValue)
  | uniqueSymbol (annotations : Annotations) (checks : List Check)
      (key : GlobalSymbolKey)
  | objectKeyword (annotations : Annotations) (checks : List Check)
  | enum (annotations : Annotations) (checks : List Check)
      (entries : List EnumEntry)
  | templateLiteral (annotations : Annotations) (checks : List Check)
      (parts : List Representation)
  | arrays (annotations : Annotations) (checks : List Check)
      (elements : List (ElementOf Representation)) (rest : List Representation)
  | objects (annotations : Annotations) (checks : List Check)
      (properties : List (PropertySignatureOf Representation))
      (indexes : List (IndexSignatureOf Representation))
  | union (annotations : Annotations) (checks : List Check)
      (types : List Representation) (mode : UnionMode)
deriving BEq

inductive Check where
  | filter (representation : CheckRepresentationAnnotationOf Representation)
      (annotations : Annotations) (aborted : Bool)
  | filterGroup
      (representation : Option (CheckRepresentationAnnotationOf Representation))
      (annotations : Annotations) (checks : List Check)
deriving BEq

end

#synth BEq Representation
#synth BEq Check

mutual

def traversesRepresentation : Representation → Bool
  | .declaration representation _ types checks =>
      (representation.id != "") &&
        Effect4.Json.numbersFinite representation.payload &&
        traversesRepresentationList types && traversesCheckList checks
  | .reference key => key.value != ""
  | .suspend _ checks thunk =>
      checks.isEmpty && traversesRepresentation thunk
  | .null _ checks
  | .undefined _ checks
  | .void _ checks
  | .never _ checks
  | .unknown _ checks
  | .any _ checks
  | .string _ checks
  | .number _ checks
  | .boolean _ checks
  | .bigint _ checks
  | .symbol _ checks
  | .uniqueSymbol _ checks _
  | .objectKeyword _ checks
  | .enum _ checks _ => traversesCheckList checks
  | .literal _ checks (.string _)
  | .literal _ checks (.bigint _)
  | .literal _ checks (.boolean _) => traversesCheckList checks
  | .literal _ checks (.number value) =>
      value.isFinite && traversesCheckList checks
  | .templateLiteral _ checks parts =>
      traversesCheckList checks && traversesRepresentationList parts
  | .arrays _ checks elements rest =>
      traversesCheckList checks && traversesElementList elements &&
        traversesRepresentationList rest
  | .objects _ checks properties indexes =>
      traversesCheckList checks && traversesPropertyList properties &&
        traversesIndexList indexes
  | .union _ checks types _ =>
      traversesCheckList checks && traversesRepresentationList types

def traversesCheck : Check → Bool
  | .filter representation _ _ =>
      traversesCheckAnnotation representation
  | .filterGroup representation _ checks =>
      (!checks.isEmpty) && traversesCheckList checks &&
        traversesOptionalCheckAnnotation representation

def traversesRepresentationList : List Representation → Bool
  | [] => true
  | head :: tail => traversesRepresentation head && traversesRepresentationList tail

def traversesCheckList : List Check → Bool
  | [] => true
  | head :: tail => traversesCheck head && traversesCheckList tail

def traversesElementList : List (ElementOf Representation) → Bool
  | [] => true
  | head :: tail => traversesElement head && traversesElementList tail

def traversesPropertyList : List (PropertySignatureOf Representation) → Bool
  | [] => true
  | head :: tail => traversesProperty head && traversesPropertyList tail

def traversesIndexList : List (IndexSignatureOf Representation) → Bool
  | [] => true
  | head :: tail => traversesIndex head && traversesIndexList tail

def traversesCheckAnnotation : CheckRepresentationAnnotationOf Representation → Bool
  | ⟨id, payload, schemas⟩ =>
      (id != "") && Effect4.Json.numbersFinite payload &&
        traversesOptionalRepresentationList schemas

def traversesOptionalCheckAnnotation :
    Option (CheckRepresentationAnnotationOf Representation) → Bool
  | none => true
  | some annotation => traversesCheckAnnotation annotation

def traversesElement : ElementOf Representation → Bool
  | ⟨_, type, _⟩ => traversesRepresentation type

def traversesProperty : PropertySignatureOf Representation → Bool
  | ⟨_, type, _, _, _⟩ => traversesRepresentation type

def traversesIndex : IndexSignatureOf Representation → Bool
  | ⟨parameter, type⟩ =>
      traversesRepresentation parameter && traversesRepresentation type

def traversesOptionalRepresentationList : Option (List Representation) → Bool
  | none => true
  | some schemas => traversesRepresentationList schemas

end

#eval traversesRepresentation (Representation.never none [])

end Effect4.Workshop.PayloadFeasibility
