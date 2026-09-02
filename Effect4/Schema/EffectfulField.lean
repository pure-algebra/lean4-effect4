import Effect4.Schema.Annotations
import Effects.Algebra.Laws
import Effect4.Flow.Block

/-!
# Effectful Schema fields

This module derives executable field access from the existing Schema
annotation data, pure optics, and closed effect signature. The first-order
annotation payload remains separate from the resolved functions used to build
`Program` values.
-/

namespace Effect4

open Effects

universe uOp uAns uTarget

/-- Portable identity of the operations that implement one annotated field. -/
structure EffectfulFieldSpec where
  alphabet : AlphabetId
  readOperation : OperationId
  writeOperation : OperationId
deriving DecidableEq, Repr

namespace EffectfulFieldSpec

/-! The annotation codec is proof-oriented. Decimal rendering, parsing, and
raw equality are structural definitions whose reflection laws are proved
without importing the runtime's opaque numeric-string theorem or the derived
`DecidableEq Json` gate. -/

private theorem append_nil_exact {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

private theorem append_assoc_exact {α : Type}
    (xs ys zs : List α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

private theorem concat_eq_append_singleton_exact {α : Type}
    (xs : List α) (x : α) : xs.concat x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

private theorem byteArray_list_roundtrip {bytes : List UInt8} :
    bytes.toByteArray.data.toList = bytes := by
  rw [List.toByteArray]
  suffices ∀ xs acc,
      (List.toByteArray.loop xs acc).data.toList = acc.data.toList ++ xs by
    simpa using this bytes ByteArray.empty
  intro xs acc
  fun_induction List.toByteArray.loop xs acc with
  | case1 => exact (append_nil_exact _).symm
  | case2 head tail acc ih =>
      rw [ih]
      cases acc with
      | mk data =>
          cases data with
          | mk values =>
              change values.concat head ++ tail = values ++ head :: tail
              rw [concat_eq_append_singleton_exact]
              exact append_assoc_exact _ _ _

private inductive Digit where
  | zero | one | two | three | four | five | six | seven | eight | nine
deriving DecidableEq

namespace Digit

private def value : Digit → Nat
  | zero => 0
  | one => 1
  | two => 2
  | three => 3
  | four => 4
  | five => 5
  | six => 6
  | seven => 7
  | eight => 8
  | nine => 9

private def char : Digit → Char
  | zero => '0'
  | one => '1'
  | two => '2'
  | three => '3'
  | four => '4'
  | five => '5'
  | six => '6'
  | seven => '7'
  | eight => '8'
  | nine => '9'

private def byte : Digit → UInt8
  | zero => 48
  | one => 49
  | two => 50
  | three => 51
  | four => 52
  | five => 53
  | six => 54
  | seven => 55
  | eight => 56
  | nine => 57

private def ofByte (byte : UInt8) : Option Digit :=
  if byte = 48 then some zero else
  if byte = 49 then some one else
  if byte = 50 then some two else
  if byte = 51 then some three else
  if byte = 52 then some four else
  if byte = 53 then some five else
  if byte = 54 then some six else
  if byte = 55 then some seven else
  if byte = 56 then some eight else
  if byte = 57 then some nine else
  none

private theorem ofByte_byte (digit : Digit) : ofByte digit.byte = some digit := by
  cases digit <;> rfl

private theorem utf8EncodeChar_char (digit : Digit) :
    String.utf8EncodeChar digit.char = [digit.byte] := by
  cases digit <;> decide

end Digit

private def reverseExact {α : Type} : List α → List α
  | [] => []
  | head :: tail => reverseExact tail ++ [head]

private theorem reverse_append_exact {α : Type} (xs ys : List α) :
    reverseExact (xs ++ ys) = reverseExact ys ++ reverseExact xs := by
  induction xs with
  | nil => exact (append_nil_exact _).symm
  | cons head tail ih =>
      change reverseExact (tail ++ ys) ++ [head] =
        reverseExact ys ++ (reverseExact tail ++ [head])
      rw [ih]
      exact append_assoc_exact _ _ _

private theorem reverse_singleton_exact {α : Type} (x : α) :
    reverseExact [x] = [x] := rfl

private theorem reverse_reverse_exact {α : Type} (xs : List α) :
    reverseExact (reverseExact xs) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      change reverseExact (reverseExact tail ++ [head]) = head :: tail
      rw [reverse_append_exact, reverse_singleton_exact, ih]
      rfl

private def increment : List Digit → List Digit
  | [] => [.one]
  | .zero :: tail => .one :: tail
  | .one :: tail => .two :: tail
  | .two :: tail => .three :: tail
  | .three :: tail => .four :: tail
  | .four :: tail => .five :: tail
  | .five :: tail => .six :: tail
  | .six :: tail => .seven :: tail
  | .seven :: tail => .eight :: tail
  | .eight :: tail => .nine :: tail
  | .nine :: tail => .zero :: increment tail

private def digitsRev : Nat → List Digit
  | 0 => [.zero]
  | n + 1 => increment (digitsRev n)

private def valueRev : List Digit → Nat
  | [] => 0
  | digit :: tail => digit.value + 10 * valueRev tail

private theorem valueRev_increment (digits : List Digit) :
    valueRev (increment digits) = valueRev digits + 1 := by
  induction digits with
  | nil => rfl
  | cons digit tail ih =>
      cases digit with
      | zero => exact Nat.succ_add 0 (10 * valueRev tail)
      | one => exact Nat.succ_add 1 (10 * valueRev tail)
      | two => exact Nat.succ_add 2 (10 * valueRev tail)
      | three => exact Nat.succ_add 3 (10 * valueRev tail)
      | four => exact Nat.succ_add 4 (10 * valueRev tail)
      | five => exact Nat.succ_add 5 (10 * valueRev tail)
      | six => exact Nat.succ_add 6 (10 * valueRev tail)
      | seven => exact Nat.succ_add 7 (10 * valueRev tail)
      | eight => exact Nat.succ_add 8 (10 * valueRev tail)
      | nine =>
          simp only [increment, valueRev, Digit.value, Nat.zero_add]
          rw [ih, Nat.mul_succ]
          exact (congrArg (fun value => value + 1)
            (Nat.add_comm 9 (10 * valueRev tail))).symm

private theorem valueRev_digitsRev (n : Nat) : valueRev (digitsRev n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [digitsRev, valueRev_increment, ih]

private def parseBytes : List UInt8 → Option (List Digit)
  | [] => some []
  | byte :: bytes => do
      let digit ← Digit.ofByte byte
      let digits ← parseBytes bytes
      pure (digit :: digits)

private theorem parseBytes_map_byte (digits : List Digit) :
    parseBytes (digits.map Digit.byte) = some digits := by
  induction digits with
  | nil => rfl
  | cons digit tail ih =>
      unfold List.map parseBytes
      rw [Digit.ofByte_byte, ih]
      rfl

private theorem utf8Digits_exact (digits : List Digit) :
    (digits.map Digit.char).flatMap String.utf8EncodeChar =
      digits.map Digit.byte := by
  induction digits with
  | nil => rfl
  | cons digit tail ih =>
      change String.utf8EncodeChar digit.char ++
          (tail.map Digit.char).flatMap String.utf8EncodeChar =
        digit.byte :: tail.map Digit.byte
      rw [Digit.utf8EncodeChar_char, ih]
      rfl

private def decimal (n : Nat) : String :=
  String.ofList ((reverseExact (digitsRev n)).map Digit.char)

private def parseDecimal (raw : String) : Option Nat := do
  let msfDigits ← parseBytes raw.toByteArray.data.toList
  pure (valueRev (reverseExact msfDigits))

private theorem parseDecimal_decimal (n : Nat) :
    parseDecimal (decimal n) = some n := by
  unfold parseDecimal decimal String.ofList List.utf8Encode
  rw [byteArray_list_roundtrip, utf8Digits_exact, parseBytes_map_byte]
  change some (valueRev (reverseExact (reverseExact (digitsRev n)))) = some n
  rw [reverse_reverse_exact, valueRev_digitsRev]

private def encode (spec : EffectfulFieldSpec) : Json :=
  .obj
    [ ("alphabet", .str (decimal spec.alphabet.value))
    , ("readOperation", .str (decimal spec.readOperation.value))
    , ("writeOperation", .str (decimal spec.writeOperation.value))
    ]

private def jsonString : Json → Option String
  | .null => none
  | .bool _ => none
  | .number _ => none
  | .str raw => some raw
  | .arr _ => none
  | .obj _ => none

private def decodePayloads
    (alphabetPayload readPayload writePayload : Json) :
    Option EffectfulFieldSpec := do
  let alphabetString ← jsonString alphabetPayload
  let readString ← jsonString readPayload
  let writeString ← jsonString writePayload
  let alphabet ← parseDecimal alphabetString
  let readOperation ← parseDecimal readString
  let writeOperation ← parseDecimal writeString
  pure
    { alphabet := ⟨alphabet⟩
      readOperation := ⟨readOperation⟩
      writeOperation := ⟨writeOperation⟩ }

private def decodeEntries : List (String × Json) → Option EffectfulFieldSpec
  | [] => none
  | alphabetEntry :: rest =>
      match rest with
      | [] => none
      | readEntry :: rest =>
          match rest with
          | [] => none
          | writeEntry :: rest =>
              match rest with
              | [] => decodePayloads alphabetEntry.2 readEntry.2 writeEntry.2
              | _ :: _ => none

private def decodeCandidate : Json → Option EffectfulFieldSpec
  | .null => none
  | .bool _ => none
  | .number _ => none
  | .str _ => none
  | .arr _ => none
  | .obj entries => decodeEntries entries

private def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | left + 1, right + 1 => natEq left right

private theorem natEq_self (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem natEq_true {left right : Nat}
    (equal : natEq left right = true) : left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ _ => cases equal
  | succ left ih =>
      cases right with
      | zero => cases equal
      | succ right => exact congrArg Nat.succ (ih equal)

private def byteEq (left right : UInt8) : Bool :=
  natEq left.toNat right.toNat

private theorem byteEq_self (byte : UInt8) : byteEq byte byte = true :=
  natEq_self byte.toNat

private theorem byteEq_true {left right : UInt8}
    (equal : byteEq left right = true) : left = right :=
  UInt8.toNat_inj.mp (natEq_true equal)

private def byteListEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | left :: lefts, right :: rights =>
      match byteEq left right with
      | false => false
      | true => byteListEq lefts rights

private theorem byteListEq_self (bytes : List UInt8) :
    byteListEq bytes bytes = true := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      unfold byteListEq
      rw [byteEq_self]
      exact ih

private theorem byteListEq_true {left right : List UInt8}
    (equal : byteListEq left right = true) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => cases equal
  | cons left lefts ih =>
      cases right with
      | nil => cases equal
      | cons right rights =>
          unfold byteListEq at equal
          cases headEq : byteEq left right with
          | false =>
              rw [headEq] at equal
              cases equal
          | true =>
              rw [headEq] at equal
              have sameHead := byteEq_true headEq
              have sameTail := ih equal
              cases sameHead
              cases sameTail
              rfl

private def stringEq (left right : String) : Bool :=
  byteListEq left.toByteArray.data.toList right.toByteArray.data.toList

private theorem stringEq_self (value : String) : stringEq value value = true :=
  byteListEq_self value.toByteArray.data.toList

private theorem array_eq_of_toList_eq {array₁ array₂ : Array UInt8}
    (equal : array₁.toList = array₂.toList) : array₁ = array₂ := by
  cases array₁ with
  | mk left =>
      cases array₂ with
      | mk right =>
          exact congrArg Array.mk equal

private theorem byteArray_eq_of_toList_eq {array₁ array₂ : ByteArray}
    (equal : array₁.data.toList = array₂.data.toList) : array₁ = array₂ := by
  cases array₁ with
  | mk left =>
      cases array₂ with
      | mk right =>
          exact congrArg ByteArray.mk (array_eq_of_toList_eq equal)

private theorem stringEq_true {left right : String}
    (equal : stringEq left right = true) : left = right :=
  String.toByteArray_inj.mp (byteArray_eq_of_toList_eq (byteListEq_true equal))

private def exactStringEntry
    (expectedKey expectedValue : String) (entry : String × Json) : Bool :=
  match entry.2 with
  | .null => false
  | .bool _ => false
  | .number _ => false
  | .str raw =>
      match stringEq entry.1 expectedKey with
      | false => false
      | true => stringEq raw expectedValue
  | .arr _ => false
  | .obj _ => false

private theorem exactStringEntry_expected (key value : String) :
    exactStringEntry key value (key, .str value) = true := by
  unfold exactStringEntry
  change (match stringEq key key with
    | false => false
    | true => stringEq value value) = true
  rw [stringEq_self]
  exact stringEq_self value

private theorem exactStringEntry_eq {key value : String}
    {entry : String × Json}
    (exact : exactStringEntry key value entry = true) :
    entry = (key, .str value) := by
  cases entry with
  | mk actualKey payload =>
      cases payload <;> try cases exact
      rename_i raw
      unfold exactStringEntry at exact
      generalize keyEq : stringEq actualKey key = sameKey at exact
      cases sameKey with
      | false => cases exact
      | true =>
          have actualKeyEq : actualKey = key := stringEq_true keyEq
          have rawEq : raw = value := stringEq_true exact
          cases actualKeyEq
          cases rawEq
          rfl

private def exactEntries
    (spec : EffectfulFieldSpec) : List (String × Json) → Bool
  | [] => false
  | alphabetEntry :: rest =>
      match rest with
      | [] => false
      | readEntry :: rest =>
          match rest with
          | [] => false
          | writeEntry :: rest =>
              match rest with
              | _ :: _ => false
              | [] =>
                  match exactStringEntry "alphabet"
                      (decimal spec.alphabet.value) alphabetEntry with
                  | false => false
                  | true =>
                      match exactStringEntry "readOperation"
                          (decimal spec.readOperation.value) readEntry with
                      | false => false
                      | true => exactStringEntry "writeOperation"
                          (decimal spec.writeOperation.value) writeEntry

private theorem exactEntries_encode (spec : EffectfulFieldSpec) :
    exactEntries spec
      [ ("alphabet", .str (decimal spec.alphabet.value))
      , ("readOperation", .str (decimal spec.readOperation.value))
      , ("writeOperation", .str (decimal spec.writeOperation.value))
      ] = true := by
  change (match exactStringEntry "alphabet"
      (decimal spec.alphabet.value)
      ("alphabet", .str (decimal spec.alphabet.value)) with
    | false => false
    | true =>
      match exactStringEntry "readOperation"
          (decimal spec.readOperation.value)
          ("readOperation", .str (decimal spec.readOperation.value)) with
      | false => false
      | true => exactStringEntry "writeOperation"
          (decimal spec.writeOperation.value)
          ("writeOperation", .str (decimal spec.writeOperation.value))) = true
  rw [exactStringEntry_expected, exactStringEntry_expected,
    exactStringEntry_expected]

private theorem exactEntries_eq {spec : EffectfulFieldSpec}
    {entries : List (String × Json)}
    (exact : exactEntries spec entries = true) :
    entries =
      [ ("alphabet", .str (decimal spec.alphabet.value))
      , ("readOperation", .str (decimal spec.readOperation.value))
      , ("writeOperation", .str (decimal spec.writeOperation.value))
      ] := by
  cases entries with
  | nil => cases exact
  | cons alphabetEntry rest =>
      cases rest with
      | nil => cases exact
      | cons readEntry rest =>
          cases rest with
          | nil => cases exact
          | cons writeEntry rest =>
              cases rest with
              | cons extra rest => cases exact
              | nil =>
                  change (match exactStringEntry "alphabet"
                      (decimal spec.alphabet.value) alphabetEntry with
                    | false => false
                    | true =>
                      match exactStringEntry "readOperation"
                          (decimal spec.readOperation.value) readEntry with
                      | false => false
                      | true => exactStringEntry "writeOperation"
                          (decimal spec.writeOperation.value) writeEntry) = true at exact
                  cases alphabetEq : exactStringEntry "alphabet"
                      (decimal spec.alphabet.value) alphabetEntry with
                  | false =>
                      rw [alphabetEq] at exact
                      cases exact
                  | true =>
                      rw [alphabetEq] at exact
                      cases readEq : exactStringEntry "readOperation"
                          (decimal spec.readOperation.value) readEntry with
                      | false =>
                          rw [readEq] at exact
                          cases exact
                      | true =>
                          rw [readEq] at exact
                          have alphabetEntryEq := exactStringEntry_eq alphabetEq
                          have readEntryEq := exactStringEntry_eq readEq
                          have writeEntryEq := exactStringEntry_eq exact
                          cases alphabetEntryEq
                          cases readEntryEq
                          cases writeEntryEq
                          rfl

private def exactRaw (spec : EffectfulFieldSpec) : Json → Bool
  | .null => false
  | .bool _ => false
  | .number _ => false
  | .str _ => false
  | .arr _ => false
  | .obj entries => exactEntries spec entries

private theorem exactRaw_encode (spec : EffectfulFieldSpec) :
    exactRaw spec (encode spec) = true :=
  exactEntries_encode spec

private theorem exactRaw_eq {spec : EffectfulFieldSpec} {raw : Json}
    (exact : exactRaw spec raw = true) : encode spec = raw := by
  cases raw with
  | null => cases exact
  | bool _ => cases exact
  | number _ => cases exact
  | str _ => cases exact
  | arr _ => cases exact
  | obj entries =>
      have entriesEq := exactEntries_eq exact
      cases entriesEq
      rfl

/-- Parse the exact canonical payload. The structural raw gate rejects leading
zeroes, reordered fields, duplicates, and extra fields. -/
private def decode (raw : Json) : Option EffectfulFieldSpec :=
  match decodeCandidate raw with
  | some spec =>
      match exactRaw spec raw with
      | true => some spec
      | false => none
  | none => none

private theorem decodeCandidate_encode (spec : EffectfulFieldSpec) :
    decodeCandidate (encode spec) = some spec := by
  cases spec with
  | mk alphabet readOperation writeOperation =>
      cases alphabet with
      | mk alphabetValue =>
        cases readOperation with
        | mk readOperationValue =>
          cases writeOperation with
          | mk writeOperationValue =>
            change (do
              let alphabet ← parseDecimal (decimal alphabetValue)
              let readOperation ← parseDecimal (decimal readOperationValue)
              let writeOperation ← parseDecimal (decimal writeOperationValue)
              some (EffectfulFieldSpec.mk ⟨alphabet⟩ ⟨readOperation⟩
                ⟨writeOperation⟩)) =
              some (EffectfulFieldSpec.mk ⟨alphabetValue⟩ ⟨readOperationValue⟩
                ⟨writeOperationValue⟩)
            rw [parseDecimal_decimal, parseDecimal_decimal, parseDecimal_decimal]
            rfl

private theorem decode_encode (spec : EffectfulFieldSpec) :
    decode (encode spec) = some spec := by
  unfold decode
  rw [decodeCandidate_encode]
  change (match exactRaw spec (encode spec) with
    | true => some spec
    | false => none) = some spec
  rw [exactRaw_encode]

private theorem encode_decode {raw : Json} {spec : EffectfulFieldSpec}
    (decoded : decode raw = some spec) : encode spec = raw := by
  unfold decode at decoded
  cases candidateEq : decodeCandidate raw with
  | none =>
      rw [candidateEq] at decoded
      cases decoded
  | some candidate =>
      rw [candidateEq] at decoded
      change (match exactRaw candidate raw with
        | true => some candidate
        | false => none) = some spec at decoded
      cases exactRawEq : exactRaw candidate raw with
      | true =>
        rw [exactRawEq] at decoded
        have sameSpec : candidate = spec := Option.some.inj decoded
        cases sameSpec
        exact exactRaw_eq exactRawEq
      | false =>
        rw [exactRawEq] at decoded
        cases decoded

/-- The one portable annotation dimension for effectful fields. -/
def annotationKey : AnnotationKey EffectfulFieldSpec where
  name := "effect4/effectful-field"
  encode := encode
  decode := decode

/-- The effectful-field payload is an exact partial isomorphism with raw JSON. -/
theorem annotationKey_lawful : annotationKey.Lawful where
  decode_encode := decode_encode
  encode_decode _ _ decoded := encode_decode decoded

/-- Every raw same-name payload, including malformed and duplicate entries. -/
def rawOccurrences (annotations : Annotations) : List Json :=
  (Annotations.payloadsAt annotationKey.name).collect annotations

/-- Exactly one canonically encoded effectful-field marker exists. -/
def RawAdmissible (annotations : Annotations) : Prop :=
  ∃ spec, rawOccurrences annotations = [annotationKey.encode spec]

/-- Decide the exact raw marker. Typed filtering is deliberately not used. -/
def check (annotations : Annotations) : Option EffectfulFieldSpec :=
  match rawOccurrences annotations with
  | [raw] => annotationKey.decode raw
  | _ => none

theorem check_eq_some_iff {annotations : Annotations}
    {spec : EffectfulFieldSpec} :
    check annotations = some spec ↔
      rawOccurrences annotations = [annotationKey.encode spec] := by
  unfold check
  generalize occurrencesEq : rawOccurrences annotations = occurrences
  cases occurrences with
  | nil => simp
  | cons raw rest =>
      cases rest with
      | nil =>
          constructor
          · intro decoded
            have exactRaw := annotationKey_lawful.encode_decode raw spec decoded
            simp [exactRaw]
          · intro exactOccurrence
            have exactRaw : raw = annotationKey.encode spec := by
              simpa using exactOccurrence
            subst raw
            exact annotationKey_lawful.decode_encode spec
      | cons second tail => simp

theorem rawAdmissible_iff_exists_check {annotations : Annotations} :
    RawAdmissible annotations ↔ ∃ spec, check annotations = some spec := by
  constructor
  · rintro ⟨spec, admissible⟩
    exact ⟨spec, check_eq_some_iff.mpr admissible⟩
  · rintro ⟨spec, checked⟩
    exact ⟨spec, check_eq_some_iff.mp checked⟩

end EffectfulFieldSpec

namespace PropertySignatureOf

/-- Decode the exact effectful-field marker attached to this property. -/
def effectfulFieldSpec (property : PropertySignatureOf A) :
    Option EffectfulFieldSpec :=
  EffectfulFieldSpec.check property.annotations

/-- Decide whether this property carries exactly one canonical marker. -/
def hasEffectfulField (property : PropertySignatureOf A) : Bool :=
  property.effectfulFieldSpec.isSome

theorem hasEffectfulField_eq_true_iff (property : PropertySignatureOf A) :
    property.hasEffectfulField = true <->
      EffectfulFieldSpec.RawAdmissible property.annotations := by
  rw [EffectfulFieldSpec.rawAdmissible_iff_exists_check]
  unfold hasEffectfulField effectfulFieldSpec
  cases checked : EffectfulFieldSpec.check property.annotations <;>
    simp

end PropertySignatureOf

private abbrev EffectfulFieldPropertyRows :=
  List (PropertySignature × EffectfulFieldSpec)

private abbrev RepresentationWithEffectfulFields :=
  Representation × EffectfulFieldPropertyRows

private abbrev CheckWithEffectfulFields :=
  Check × EffectfulFieldPropertyRows

private def representationRows
    (children : List RepresentationWithEffectfulFields) :
    EffectfulFieldPropertyRows :=
  children.flatMap Prod.snd

private def checkRows (children : List CheckWithEffectfulFields) :
    EffectfulFieldPropertyRows :=
  children.flatMap Prod.snd

private def rebuildElement
    (element : ElementOf RepresentationWithEffectfulFields) : Element :=
  { isOptional := element.isOptional
    type := element.type.1
    annotations := element.annotations }

private def elementRows
    (elements : List (ElementOf RepresentationWithEffectfulFields)) :
    EffectfulFieldPropertyRows :=
  elements.flatMap fun element => element.type.2

private def rebuildProperty
    (property : PropertySignatureOf RepresentationWithEffectfulFields) :
    PropertySignature :=
  { name := property.name
    type := property.type.1
    isOptional := property.isOptional
    isMutable := property.isMutable
    annotations := property.annotations }

private def propertyRows
    (properties : List (PropertySignatureOf RepresentationWithEffectfulFields)) :
    EffectfulFieldPropertyRows :=
  properties.flatMap fun property =>
    let original := rebuildProperty property
    match original.effectfulFieldSpec with
    | some spec => (original, spec) :: property.type.2
    | none => property.type.2

private def rebuildIndex
    (index : IndexSignatureOf RepresentationWithEffectfulFields) : IndexSignature :=
  { parameter := index.parameter.1
    type := index.type.1 }

private def indexRows
    (indexes : List (IndexSignatureOf RepresentationWithEffectfulFields)) :
    EffectfulFieldPropertyRows :=
  indexes.flatMap fun index => index.parameter.2 ++ index.type.2

private def rebuildCheckAnnotation
    (annotation : CheckRepresentationAnnotationOf RepresentationWithEffectfulFields) :
    CheckRepresentationAnnotation :=
  { id := annotation.id
    payload := annotation.payload
    schemas := annotation.schemas.map (List.map Prod.fst) }

private def checkAnnotationRows
    (annotation : CheckRepresentationAnnotationOf RepresentationWithEffectfulFields) :
    EffectfulFieldPropertyRows :=
  match annotation.schemas with
  | none => []
  | some schemas => representationRows schemas

private def effectfulFieldPropertyAlgebra :
    Representation.FoldAlgebra RepresentationWithEffectfulFields
      CheckWithEffectfulFields where
  declaration := fun representation annotations typeParameters checks =>
    ( .declaration representation annotations (typeParameters.map Prod.fst)
        (checks.map Prod.fst)
    , representationRows typeParameters ++ checkRows checks )
  reference := fun key => (.reference key, [])
  suspend := fun annotations checks thunk =>
    (.suspend annotations (checks.map Prod.fst) thunk.1,
      checkRows checks ++ thunk.2)
  null := fun annotations checks =>
    (.null annotations (checks.map Prod.fst), checkRows checks)
  undefined := fun annotations checks =>
    (.undefined annotations (checks.map Prod.fst), checkRows checks)
  void := fun annotations checks =>
    (.void annotations (checks.map Prod.fst), checkRows checks)
  never := fun annotations checks =>
    (.never annotations (checks.map Prod.fst), checkRows checks)
  unknown := fun annotations checks =>
    (.unknown annotations (checks.map Prod.fst), checkRows checks)
  any := fun annotations checks =>
    (.any annotations (checks.map Prod.fst), checkRows checks)
  string := fun annotations checks =>
    (.string annotations (checks.map Prod.fst), checkRows checks)
  number := fun annotations checks =>
    (.number annotations (checks.map Prod.fst), checkRows checks)
  boolean := fun annotations checks =>
    (.boolean annotations (checks.map Prod.fst), checkRows checks)
  bigint := fun annotations checks =>
    (.bigint annotations (checks.map Prod.fst), checkRows checks)
  symbol := fun annotations checks =>
    (.symbol annotations (checks.map Prod.fst), checkRows checks)
  literal := fun annotations checks value =>
    (.literal annotations (checks.map Prod.fst) value, checkRows checks)
  uniqueSymbol := fun annotations checks key =>
    (.uniqueSymbol annotations (checks.map Prod.fst) key, checkRows checks)
  objectKeyword := fun annotations checks =>
    (.objectKeyword annotations (checks.map Prod.fst), checkRows checks)
  enum := fun annotations checks entries =>
    (.enum annotations (checks.map Prod.fst) entries, checkRows checks)
  templateLiteral := fun annotations checks parts =>
    ( .templateLiteral annotations (checks.map Prod.fst) (parts.map Prod.fst)
    , checkRows checks ++ representationRows parts )
  arrays := fun annotations checks elements rest =>
    ( .arrays annotations (checks.map Prod.fst)
        (elements.map rebuildElement) (rest.map Prod.fst)
    , checkRows checks ++ elementRows elements ++ representationRows rest )
  objects := fun annotations checks properties indexes =>
    ( .objects annotations (checks.map Prod.fst)
        (properties.map rebuildProperty) (indexes.map rebuildIndex)
    , checkRows checks ++ propertyRows properties ++ indexRows indexes )
  union := fun annotations checks types mode =>
    ( .union annotations (checks.map Prod.fst) (types.map Prod.fst) mode
    , checkRows checks ++ representationRows types )
  filter := fun representation annotations aborted =>
    ( .filter (rebuildCheckAnnotation representation) annotations aborted
    , checkAnnotationRows representation )
  filterGroup := fun representation annotations checks =>
    let rebuilt := representation.map rebuildCheckAnnotation
    let representationRows :=
      match representation with
      | none => []
      | some value => checkAnnotationRows value
    (.filterGroup rebuilt annotations (checks.map Prod.fst),
      representationRows ++ checkRows checks)

/-- Discover every exactly marked property through the existing exhaustive
Schema fold, retaining structural preorder and duplicate occurrences. -/
def Representation.effectfulFieldProperties (representation : Representation) :
    List (PropertySignature × EffectfulFieldSpec) :=
  (Representation.fold effectfulFieldPropertyAlgebra representation).2

/-- Resolution of portable operation identities into one existing signature. -/
structure FieldEffectOps
    (signature : Signature.{uOp, uAns}) (S A : Type uAns) where
  alphabet : AlphabetId
  readOperation : OperationId
  writeOperation : OperationId
  operationId : signature.Op → OperationId
  read : S → signature.Op
  read_answer : ∀ source, signature.Answer (read source) = A
  write : S → A → signature.Op
  read_operation : ∀ source, operationId (read source) = readOperation
  write_operation : ∀ source value,
    operationId (write source value) = writeOperation

namespace EffectfulFieldSpec

/-- Exact identity agreement between portable metadata and resolved operations. -/
def Matches (spec : EffectfulFieldSpec)
    (operations : FieldEffectOps signature S A) : Prop :=
  spec.alphabet = operations.alphabet ∧
    spec.readOperation = operations.readOperation ∧
    spec.writeOperation = operations.writeOperation

instance (spec : EffectfulFieldSpec)
    (operations : FieldEffectOps signature S A) :
    Decidable (spec.Matches operations) :=
  inferInstanceAs (Decidable
    (spec.alphabet = operations.alphabet ∧
      spec.readOperation = operations.readOperation ∧
      spec.writeOperation = operations.writeOperation))

end EffectfulFieldSpec

/-- A pure field focus paired with resolved operations in an existing effect
signature. It is an authoring/proof view, not persisted Schema data. -/
structure EffectfulField
    (signature : Signature.{uOp, uAns}) (S A : Type uAns) where
  optic : Lens S A
  operations : FieldEffectOps signature S A

namespace EffectfulField

/-- Raw annotation evidence and the resolved operation identities agree. -/
def Resolvable (annotations : Annotations)
    (operations : FieldEffectOps signature S A) : Prop :=
  ∃ spec, EffectfulFieldSpec.check annotations = some spec ∧
    spec.Matches operations

/-- Resolve one exact raw marker into the effectful interface. -/
def resolve {signature : Signature.{uOp, uAns}} {S A : Type uAns}
    (optic : Lens S A) (operations : FieldEffectOps signature S A)
    (annotations : Annotations) : Option (EffectfulField signature S A) :=
  match EffectfulFieldSpec.check annotations with
  | some spec =>
      if spec.Matches operations then some { optic, operations } else none
  | none => none

theorem resolvable_iff_resolve_isSome
    {signature : Signature.{uOp, uAns}} {S A : Type uAns}
    {optic : Lens S A} {operations : FieldEffectOps signature S A}
    {annotations : Annotations} :
    Resolvable annotations operations ↔
      (resolve optic operations annotations).isSome = true := by
  unfold Resolvable resolve
  cases checked : EffectfulFieldSpec.check annotations with
  | none => simp
  | some spec =>
      by_cases matched : spec.Matches operations <;> simp [matched]

/-- Read the field through the resolved effect operation. -/
def get (field : EffectfulField signature S A) (_source : S) :
    Program signature A :=
  Program.perform (field.operations.read _source) >>= fun answer =>
    Program.pure ((field.operations.read_answer _source).mp answer)

/-- Write first, then return the locally updated source. The operation reply
is discarded without constraining its answer type to `Unit`. -/
def set (field : EffectfulField signature S A) (value : A) (source : S) :
    Program signature S :=
  Program.perform (field.operations.write source value) >>= fun _ =>
    Program.pure (field.optic.replace value source)

/-- Read the current effectful value, transform it, and write the result. -/
def modify (field : EffectfulField signature S A) (f : A → A) (source : S) :
    Program signature S :=
  field.get source >>= fun current => field.set (f current) source

theorem get_eq (field : EffectfulField signature S A) (source : S) :
    field.get source =
      Program.perform (field.operations.read source) >>= fun answer =>
        Program.pure ((field.operations.read_answer source).mp answer) :=
  rfl

theorem set_eq (field : EffectfulField signature S A) (value : A) (source : S) :
    field.set value source =
      Program.perform (field.operations.write source value) >>= fun _ =>
        Program.pure (field.optic.replace value source) :=
  rfl

theorem modify_eq (field : EffectfulField signature S A)
    (f : A → A) (source : S) :
    field.modify f source =
      field.get source >>= fun current => field.set (f current) source :=
  rfl

theorem interpret_set {signature : Signature.{uOp, uAns}}
    {S A : Type uAns} {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M] (handler : Handler signature M)
    (field : EffectfulField signature S A) (value : A) (source : S) :
    interpret handler (field.set value source) =
      handler.handle (field.operations.write source value) >>= fun _ =>
        pure (field.optic.replace value source) := by
  rfl

theorem interpret_modify {signature : Signature.{uOp, uAns}}
    {S A : Type uAns} {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M] (handler : Handler signature M)
    (field : EffectfulField signature S A) (f : A → A) (source : S) :
    interpret handler (field.modify f source) =
      handler.handle (field.operations.read source) >>= fun answer =>
        let current := (field.operations.read_answer source).mp answer
        handler.handle (field.operations.write source (f current)) >>= fun _ =>
          pure (field.optic.replace (f current) source) := by
  rfl

end EffectfulField

end Effect4
