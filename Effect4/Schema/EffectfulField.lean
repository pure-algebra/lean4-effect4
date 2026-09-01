import Effect4.Schema.Annotations
import Effect4.Algebra.Laws
import Effect4.Flow.Block

/-!
# Effectful Schema fields

This module derives executable field access from the existing Schema
annotation data, pure optics, and closed effect signature. The first-order
annotation payload remains separate from the resolved functions used to build
`Program` values.
-/

namespace Effect4

universe uOp uAns uTarget

/-- Portable identity of the operations that implement one annotated field. -/
structure EffectfulFieldSpec where
  alphabet : AlphabetId
  readOperation : OperationId
  writeOperation : OperationId
deriving DecidableEq, Repr

namespace EffectfulFieldSpec

private def encode (spec : EffectfulFieldSpec) : Json :=
  .obj
    [ ("alphabet", .str (Nat.repr spec.alphabet.value))
    , ("readOperation", .str (Nat.repr spec.readOperation.value))
    , ("writeOperation", .str (Nat.repr spec.writeOperation.value))
    ]

private def decodeCandidate : Json → Option EffectfulFieldSpec
  | .obj
      [ ("alphabet", .str alphabet)
      , ("readOperation", .str readOperation)
      , ("writeOperation", .str writeOperation)
      ] => do
        let alphabet ← alphabet.toNat?
        let readOperation ← readOperation.toNat?
        let writeOperation ← writeOperation.toNat?
        pure
          { alphabet := ⟨alphabet⟩
            readOperation := ⟨readOperation⟩
            writeOperation := ⟨writeOperation⟩ }
  | _ => none

/-- Parse the exact canonical payload. The re-encoding equality rejects
leading zeroes, reordered fields, duplicates, and extra fields. -/
private def decode (raw : Json) : Option EffectfulFieldSpec :=
  match decodeCandidate raw with
  | some spec => if encode spec = raw then some spec else none
  | none => none

private theorem decodeCandidate_encode (spec : EffectfulFieldSpec) :
    decodeCandidate (encode spec) = some spec := by
  cases spec with
  | mk alphabet readOperation writeOperation =>
      cases alphabet
      cases readOperation
      cases writeOperation
      simp [decodeCandidate, encode, Nat.toNat?_repr]

private theorem decode_encode (spec : EffectfulFieldSpec) :
    decode (encode spec) = some spec := by
  simp [decode, decodeCandidate_encode]

private theorem encode_decode {raw : Json} {spec : EffectfulFieldSpec}
    (decoded : decode raw = some spec) : encode spec = raw := by
  unfold decode at decoded
  cases candidateEq : decodeCandidate raw with
  | none => simp [candidateEq] at decoded
  | some candidate =>
      by_cases exactRaw : encode candidate = raw
      · simp [candidateEq, exactRaw] at decoded
        cases decoded
        exact exactRaw
      · simp [candidateEq, exactRaw] at decoded

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
