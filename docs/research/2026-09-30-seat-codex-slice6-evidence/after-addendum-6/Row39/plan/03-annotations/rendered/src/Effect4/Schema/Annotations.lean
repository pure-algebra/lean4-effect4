import Effect4.Data.Optic
import Effect4.Schema.Representation

/-!
# Schema annotation carrier

Typed annotation keys describe payloads in the existing raw `Annotations`
carrier. Their two laws require written values to decode and decoded payloads
to re-encode exactly. Entry construction and append preserve the stored list.

`Representation.nodeAnnotations` views the annotation field on one node;
references have no field, while a stored `none` is a present field. Recursive
annotation traversal and the broader annotation editing API were retired by
decision row 39.
-/

namespace Effect4

universe u

/-- A typed dimension carried by ordinary Schema annotation entries. -/
structure AnnotationKey (A : Type u) where
  name : String
  encode : A → Json
  decode : Json → Option A

namespace AnnotationKey

/-- Exactness laws for a typed view of raw JSON annotation payloads. -/
structure Lawful (key : AnnotationKey A) : Prop where
  decode_encode : ∀ value, key.decode (key.encode value) = some value
  encode_decode : ∀ raw value, key.decode raw = some value →
    key.encode value = raw

/-- Encode one typed value as an existing raw annotation entry. -/
def entry (key : AnnotationKey A) (value : A) : AnnotationEntry :=
  { key := key.name, payload := key.encode value }

/-- A one-entry annotation bag. -/
def singleton (key : AnnotationKey A) (value : A) : Annotations :=
  some [key.entry value]

/-- Append one typed value without changing existing entries or multiplicity. -/
def append (key : AnnotationKey A) (value : A) : Annotations → Annotations
  | none => key.singleton value
  | some entries => some (entries ++ [key.entry value])

end AnnotationKey

namespace Representation

/-- The annotation field on one representation node. `Reference` has no such
field; a stored `none` on every other constructor is still a present focus. -/
def nodeAnnotations : Optional Representation Annotations where
  preview
    | .reference _ => none
    | .declaration _ annotations _ _
    | .suspend annotations _ _
    | .null annotations _
    | .undefined annotations _
    | .void annotations _
    | .never annotations _
    | .unknown annotations _
    | .any annotations _
    | .string annotations _
    | .number annotations _
    | .boolean annotations _
    | .bigint annotations _
    | .symbol annotations _
    | .literal annotations _ _
    | .uniqueSymbol annotations _ _
    | .objectKeyword annotations _
    | .enum annotations _ _
    | .templateLiteral annotations _ _
    | .arrays annotations _ _ _
    | .objects annotations _ _ _
    | .union annotations _ _ _ => some annotations
  replace replacement
    | .declaration representation _ parameters checks =>
        .declaration representation replacement parameters checks
    | .reference ref => .reference ref
    | .suspend _ checks thunk => .suspend replacement checks thunk
    | .null _ checks => .null replacement checks
    | .undefined _ checks => .undefined replacement checks
    | .void _ checks => .void replacement checks
    | .never _ checks => .never replacement checks
    | .unknown _ checks => .unknown replacement checks
    | .any _ checks => .any replacement checks
    | .string _ checks => .string replacement checks
    | .number _ checks => .number replacement checks
    | .boolean _ checks => .boolean replacement checks
    | .bigint _ checks => .bigint replacement checks
    | .symbol _ checks => .symbol replacement checks
    | .literal _ checks value => .literal replacement checks value
    | .uniqueSymbol _ checks key => .uniqueSymbol replacement checks key
    | .objectKeyword _ checks => .objectKeyword replacement checks
    | .enum _ checks entries => .enum replacement checks entries
    | .templateLiteral _ checks parts => .templateLiteral replacement checks parts
    | .arrays _ checks elements rest => .arrays replacement checks elements rest
    | .objects _ checks properties indexes =>
        .objects replacement checks properties indexes
    | .union _ checks types mode => .union replacement checks types mode

theorem nodeAnnotations_lawful : Optional.Lawful nodeAnnotations := by
  constructor
  · intro source value absent
    cases source <;> cases absent <;> rfl
  · intro source current value present
    cases source <;> cases present <;> rfl
  · intro source current present
    cases source <;> cases present <;> rfl
  · intro source first second
    cases source <;> rfl

end Representation

end Effect4
