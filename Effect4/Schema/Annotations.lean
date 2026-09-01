import Effect4.Data.Optic
import Effect4.Schema.Representation

/-!
# Schema annotation data plane

The annotation API is a typed, composable view over the annotation data that
the persisted Schema carrier already contains.  Raw storage remains
`Annotations`: an optional ordered list of `AnnotationEntry` values.  In
particular, this module does not introduce a map, a second Schema tree, or a
new JSON carrier.

`AnnotationKey` describes one typed dimension of the raw payload.  Its lawful
form is an exact partial isomorphism: values written through it decode, and a
successfully decoded raw payload re-encodes byte-for-data exactly.  That
second direction is what makes the derived traversal an exact edit of raw
Schema data rather than an implicit normalizer.
-/

namespace Effect4

universe u v

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

/-- Decode an entry only when both its name and payload match this dimension. -/
def decodeEntry (key : AnnotationKey A) (entry : AnnotationEntry) : Option A :=
  if entry.key = key.name then key.decode entry.payload else none

/-- A successfully encoded entry decodes to its source value. -/
theorem decodeEntry_entry (key : AnnotationKey A) (law : key.Lawful)
    (value : A) : key.decodeEntry (key.entry value) = some value := by
  change (if key.name = key.name then key.decode (key.encode value) else none) =
    some value
  rw [if_pos rfl]
  exact law.decode_encode value

/-- Successful typed observation reconstructs the exact raw entry. -/
theorem entry_of_decodeEntry (key : AnnotationKey A) (law : key.Lawful)
    {entry : AnnotationEntry} {value : A}
    (decoded : key.decodeEntry entry = some value) : key.entry value = entry := by
  unfold decodeEntry at decoded
  split at decoded
  next nameEqual =>
    cases entry with
    | mk name payload =>
        change name = key.name at nameEqual
        subst name
        have payloadEqual := law.encode_decode payload value decoded
        cases payloadEqual
        rfl
  next nameDifferent => cases decoded

/-- The typed focus inside one raw payload. Malformed values are absent and
therefore remain untouched by replacement. -/
private def payloadValue (key : AnnotationKey A) : Optional Json A where
  preview := key.decode
  replace value raw :=
    match key.decode raw with
    | none => raw
    | some _ => key.encode value

private theorem payloadValue_lawful (key : AnnotationKey A) (law : key.Lawful) :
    Optional.Lawful key.payloadValue := by
  constructor
  · intro raw value absent
    change key.decode raw = none at absent
    change (match key.decode raw with
      | none => raw
      | some _ => key.encode value) = raw
    rw [absent]
  · intro raw current value present
    change key.decode raw = some current at present
    change key.decode (match key.decode raw with
      | none => raw
      | some _ => key.encode value) = some value
    rw [present]
    exact law.decode_encode value
  · intro raw current present
    change key.decode raw = some current at present
    change (match key.decode raw with
      | none => raw
      | some _ => key.encode current) = raw
    rw [present]
    exact law.encode_decode raw current present
  · intro raw first second
    cases decoded : key.decode raw with
    | none =>
        have firstNoop : key.payloadValue.replace first raw = raw := by
          change (match key.decode raw with
            | none => raw
            | some _ => key.encode first) = raw
          rw [decoded]
        rw [firstNoop]
    | some current =>
        have firstReplacement :
            key.payloadValue.replace first raw = key.encode first := by
          change (match key.decode raw with
            | none => raw
            | some _ => key.encode first) = key.encode first
          rw [decoded]
        have secondReplacement :
            key.payloadValue.replace second raw = key.encode second := by
          change (match key.decode raw with
            | none => raw
            | some _ => key.encode second) = key.encode second
          rw [decoded]
        rw [firstReplacement, secondReplacement]
        change (match key.decode (key.encode first) with
          | none => key.encode first
          | some _ => key.encode second) = key.encode second
        rw [law.decode_encode]

end AnnotationKey

namespace Annotations

private def collectPayloadsAt (name : String) : List AnnotationEntry → List Json
  | [] => []
  | entry :: tail =>
      if entry.key = name then
        entry.payload :: collectPayloadsAt name tail
      else
        collectPayloadsAt name tail

private def modifyPayloadsAt (name : String) (f : Json → Json) :
    List AnnotationEntry → List AnnotationEntry
  | [] => []
  | entry :: tail =>
      (if entry.key = name then { entry with payload := f entry.payload } else entry) ::
        modifyPayloadsAt name f tail

private theorem modifyPayloadsAt_cons_same (name : String) (payload : Json)
    (tail : List AnnotationEntry) (f : Json → Json) :
    modifyPayloadsAt name f (AnnotationEntry.mk name payload :: tail) =
      AnnotationEntry.mk name (f payload) :: modifyPayloadsAt name f tail := by
  rw [modifyPayloadsAt, if_pos rfl]

private theorem modifyPayloadsAt_cons_other (name key : String) (payload : Json)
    (tail : List AnnotationEntry) (f : Json → Json) (different : key ≠ name) :
    modifyPayloadsAt name f (AnnotationEntry.mk key payload :: tail) =
      AnnotationEntry.mk key payload :: modifyPayloadsAt name f tail := by
  rw [modifyPayloadsAt, if_neg different]

private theorem collectPayloadsAt_cons_same (name : String) (payload : Json)
    (tail : List AnnotationEntry) :
    collectPayloadsAt name (AnnotationEntry.mk name payload :: tail) =
      payload :: collectPayloadsAt name tail := by
  rw [collectPayloadsAt, if_pos rfl]

private theorem collectPayloadsAt_cons_other (name key : String) (payload : Json)
    (tail : List AnnotationEntry) (different : key ≠ name) :
    collectPayloadsAt name (AnnotationEntry.mk key payload :: tail) =
      collectPayloadsAt name tail := by
  rw [collectPayloadsAt, if_neg different]

/-- Every payload with the requested name, in stored order. -/
def payloadsAt (name : String) : Traversal Annotations Json where
  collect
    | none => []
    | some entries => collectPayloadsAt name entries
  modifyAll f
    | none => none
    | some entries => some (modifyPayloadsAt name f entries)

private theorem modifyPayloadsAt_id (name : String)
    (entries : List AnnotationEntry) :
    modifyPayloadsAt name id entries = entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk key payload =>
        simp only [modifyPayloadsAt]
        split
        next same =>
          subst key
          change AnnotationEntry.mk name payload ::
              modifyPayloadsAt name id tail =
            AnnotationEntry.mk name payload :: tail
          rw [ih]
        next different =>
          change AnnotationEntry.mk key payload ::
              modifyPayloadsAt name id tail =
            AnnotationEntry.mk key payload :: tail
          rw [ih]

private theorem modifyPayloadsAt_comp (name : String)
    (entries : List AnnotationEntry) (first second : Json → Json) :
    modifyPayloadsAt name second (modifyPayloadsAt name first entries) =
      modifyPayloadsAt name (second ∘ first) entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk key payload =>
          by_cases same : key = name
          · subst key
            rw [modifyPayloadsAt_cons_same, modifyPayloadsAt_cons_same,
              modifyPayloadsAt_cons_same, ih]
            rfl
          · rw [modifyPayloadsAt_cons_other name key payload tail first same,
              modifyPayloadsAt_cons_other name key payload
                (modifyPayloadsAt name first tail) second same,
              modifyPayloadsAt_cons_other name key payload tail (second ∘ first) same,
              ih]

private theorem modifyPayloadsAt_congr (name : String)
    (entries : List AnnotationEntry) {first second : Json → Json}
    (pointwise : ∀ value, first value = second value) :
    modifyPayloadsAt name first entries = modifyPayloadsAt name second entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk key payload =>
          by_cases same : key = name
          · subst key
            rw [modifyPayloadsAt_cons_same, modifyPayloadsAt_cons_same,
              pointwise, ih]
          · rw [modifyPayloadsAt_cons_other name key payload tail first same,
              modifyPayloadsAt_cons_other name key payload tail second same, ih]

private theorem collectPayloadsAt_modify (name : String)
    (entries : List AnnotationEntry) (f : Json → Json) :
    collectPayloadsAt name (modifyPayloadsAt name f entries) =
      (collectPayloadsAt name entries).map f := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk key payload =>
          by_cases same : key = name
          · subst key
            rw [modifyPayloadsAt_cons_same, collectPayloadsAt_cons_same,
              collectPayloadsAt_cons_same]
            change f payload ::
                collectPayloadsAt name (modifyPayloadsAt name f tail) =
              f payload :: (collectPayloadsAt name tail).map f
            rw [ih]
          · rw [modifyPayloadsAt_cons_other name key payload tail f same,
              collectPayloadsAt_cons_other name key payload
                (modifyPayloadsAt name f tail) same,
              collectPayloadsAt_cons_other name key payload tail same, ih]

/-- Raw same-name payload traversal satisfies the pure traversal equations. -/
theorem payloadsAt_lawful (name : String) :
    Traversal.Lawful (payloadsAt name) := by
  constructor
  · intro first second pointwise annotations
    cases annotations with
    | none => rfl
    | some entries =>
        exact congrArg some (modifyPayloadsAt_congr name entries pointwise)
  · intro annotations
    cases annotations with
    | none => rfl
    | some entries => exact congrArg some (modifyPayloadsAt_id name entries)
  · intro annotations first second
    cases annotations with
    | none => rfl
    | some entries =>
        exact congrArg some (modifyPayloadsAt_comp name entries first second)
  · intro annotations f
    cases annotations with
    | none => rfl
    | some entries => exact collectPayloadsAt_modify name entries f

end Annotations

namespace AnnotationKey

/-- Every successfully decoded occurrence of this dimension. Malformed
same-name entries stay in the raw bag and are not foci of this typed view. -/
def values (key : AnnotationKey A) : Traversal Annotations A :=
  (Annotations.payloadsAt key.name).compose key.payloadValue.toTraversal

/-- Lift a typed annotation dimension through any outer annotation traversal. -/
def inTraversal (key : AnnotationKey A) (outer : Traversal S Annotations) :
    Traversal S A :=
  outer.compose key.values

/-- Read every successfully decoded occurrence in order. -/
def getAll (key : AnnotationKey A) (annotations : Annotations) : List A :=
  key.values.collect annotations

/-- Modify every successfully decoded occurrence in place. -/
def modifyAll (key : AnnotationKey A) (f : A → A)
    (annotations : Annotations) : Annotations :=
  key.values.modifyAll f annotations

/-- Replace every successfully decoded occurrence with one typed value. -/
def replaceAll (key : AnnotationKey A) (value : A)
    (annotations : Annotations) : Annotations :=
  key.modifyAll (fun _ => value) annotations

/-- A lawful typed key yields a lawful traversal of its occurrences. -/
theorem values_lawful (key : AnnotationKey A) (law : key.Lawful) :
    Traversal.Lawful key.values := by
  change Traversal.Lawful
    ((Annotations.payloadsAt key.name).compose key.payloadValue.toTraversal)
  exact Traversal.Lawful.compose (Annotations.payloadsAt_lawful key.name)
    (Optional.Lawful.toTraversal (key.payloadValue_lawful law))

/-- Lawfulness composes through an outer annotation traversal. -/
theorem inTraversal_lawful (key : AnnotationKey A)
    {outer : Traversal S Annotations} (keyLaw : key.Lawful)
    (outerLaw : Traversal.Lawful outer) :
    Traversal.Lawful (key.inTraversal outer) := by
  change Traversal.Lawful (outer.compose key.values)
  exact Traversal.Lawful.compose outerLaw (key.values_lawful keyLaw)

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

theorem nodeAnnotations_reference (ref : ReferenceKey) :
    nodeAnnotations.preview (.reference ref) = none := rfl

theorem nodeAnnotations_string_none :
    nodeAnnotations.preview (.string none []) = some none := rfl

theorem nodeAnnotations_lawful : Optional.Lawful nodeAnnotations := by
  constructor
  · intro source value absent
    cases source <;> first | rfl | cases absent
  · intro source current value present
    cases source <;> first | rfl | cases present
  · intro source current present
    cases source <;> cases present <;> rfl
  · intro source first second
    cases source <;> rfl

end Representation

namespace Check

/-- The annotation field of either check node. -/
def annotationsLens : Lens Check Annotations where
  get
    | .filter _ annotations _ => annotations
    | .filterGroup _ annotations _ => annotations
  replace replacement
    | .filter representation _ aborted =>
        .filter representation replacement aborted
    | .filterGroup representation _ checks =>
        .filterGroup representation replacement checks

theorem annotationsLens_lawful : Lens.Lawful annotationsLens := by
  constructor <;> intros <;> cases ‹Check› <;> rfl

end Check

namespace ElementOf

/-- The annotation field of one array element record. -/
def annotationsLens : Lens (ElementOf A) Annotations where
  get := ElementOf.annotations
  replace replacement element := { element with annotations := replacement }

theorem annotationsLens_lawful :
    Lens.Lawful (annotationsLens (A := A)) := by
  constructor <;> intros <;> cases ‹ElementOf A› <;> rfl

end ElementOf

namespace PropertySignatureOf

/-- The annotation field of one object property record. -/
def annotationsLens : Lens (PropertySignatureOf A) Annotations where
  get := PropertySignatureOf.annotations
  replace replacement property := { property with annotations := replacement }

theorem annotationsLens_lawful :
    Lens.Lawful (annotationsLens (A := A)) := by
  constructor <;> intros <;> cases ‹PropertySignatureOf A› <;> rfl

end PropertySignatureOf

/-!
## Recursive annotation data

The two payload traversals below are algebras over the existing closed
`Representation.fold` / `Check.fold`.  The collection algebra returns the
preorder list of bags.  The update algebra reconstructs the existing carrier
while applying one bag endomorphism at every annotation-bearing site.
-/

namespace AnnotationTraversal

private def appendMany : List (List A) → List A
  | [] => []
  | head :: tail => head ++ appendMany tail

private theorem map_append_exact (f : A → B) (first second : List A) :
    (first ++ second).map f = first.map f ++ second.map f := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      change f head :: (tail ++ second).map f =
        f head :: (tail.map f ++ second.map f)
      rw [ih]

private theorem map_map_exact (values : List A) (first : A → B) (second : B → C) :
    (values.map first).map second = values.map (second ∘ first) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change second (first head) :: (tail.map first).map second =
        (second ∘ first) head :: tail.map (second ∘ first)
      rw [ih]
      rfl

private def checkSchemas
    (annotation : CheckRepresentationAnnotationOf (List Annotations)) :
    List Annotations :=
  match annotation.schemas with
  | none => []
  | some schemas => appendMany schemas

private def checkSchemasOptional
    (annotation : Option (CheckRepresentationAnnotationOf (List Annotations))) :
    List Annotations :=
  match annotation with
  | none => []
  | some value => checkSchemas value

private def elementBags : List (ElementOf (List Annotations)) → List Annotations
  | [] => []
  | element :: tail => element.annotations :: (element.type ++ elementBags tail)

private def propertyBags :
    List (PropertySignatureOf (List Annotations)) → List Annotations
  | [] => []
  | property :: tail => property.annotations :: (property.type ++ propertyBags tail)

private def indexBags :
    List (IndexSignatureOf (List Annotations)) → List Annotations
  | [] => []
  | index :: tail => index.parameter ++ index.type ++ indexBags tail

private def collectAlgebra :
    Representation.FoldAlgebra (List Annotations) (List Annotations) where
  declaration _ annotations parameters checks :=
    annotations :: (appendMany parameters ++ appendMany checks)
  reference _ := []
  suspend annotations checks thunk :=
    annotations :: (appendMany checks ++ thunk)
  null annotations checks := annotations :: appendMany checks
  undefined annotations checks := annotations :: appendMany checks
  void annotations checks := annotations :: appendMany checks
  never annotations checks := annotations :: appendMany checks
  unknown annotations checks := annotations :: appendMany checks
  any annotations checks := annotations :: appendMany checks
  string annotations checks := annotations :: appendMany checks
  number annotations checks := annotations :: appendMany checks
  boolean annotations checks := annotations :: appendMany checks
  bigint annotations checks := annotations :: appendMany checks
  symbol annotations checks := annotations :: appendMany checks
  literal annotations checks _ := annotations :: appendMany checks
  uniqueSymbol annotations checks _ := annotations :: appendMany checks
  objectKeyword annotations checks := annotations :: appendMany checks
  enum annotations checks _ := annotations :: appendMany checks
  templateLiteral annotations checks parts :=
    annotations :: (appendMany checks ++ appendMany parts)
  arrays annotations checks elements rest :=
    annotations :: (appendMany checks ++ elementBags elements ++ appendMany rest)
  objects annotations checks properties indexes :=
    annotations :: (appendMany checks ++ propertyBags properties ++ indexBags indexes)
  union annotations checks types _ :=
    annotations :: (appendMany checks ++ appendMany types)
  filter representation annotations _ :=
    annotations :: checkSchemas representation
  filterGroup representation annotations checks :=
    annotations :: (checkSchemasOptional representation ++ appendMany checks)

private def modifyAlgebra (f : Annotations → Annotations) :
    Representation.FoldAlgebra Representation Check where
  declaration representation annotations parameters checks :=
    .declaration representation (f annotations) parameters checks
  reference := .reference
  suspend annotations checks thunk := .suspend (f annotations) checks thunk
  null annotations checks := .null (f annotations) checks
  undefined annotations checks := .undefined (f annotations) checks
  void annotations checks := .void (f annotations) checks
  never annotations checks := .never (f annotations) checks
  unknown annotations checks := .unknown (f annotations) checks
  any annotations checks := .any (f annotations) checks
  string annotations checks := .string (f annotations) checks
  number annotations checks := .number (f annotations) checks
  boolean annotations checks := .boolean (f annotations) checks
  bigint annotations checks := .bigint (f annotations) checks
  symbol annotations checks := .symbol (f annotations) checks
  literal annotations checks value := .literal (f annotations) checks value
  uniqueSymbol annotations checks key := .uniqueSymbol (f annotations) checks key
  objectKeyword annotations checks := .objectKeyword (f annotations) checks
  enum annotations checks entries := .enum (f annotations) checks entries
  templateLiteral annotations checks parts :=
    .templateLiteral (f annotations) checks parts
  arrays annotations checks elements rest :=
    .arrays (f annotations) checks
      (elements.map fun element => { element with annotations := f element.annotations })
      rest
  objects annotations checks properties indexes :=
    .objects (f annotations) checks
      (properties.map fun property =>
        { property with annotations := f property.annotations })
      indexes
  union annotations checks types mode := .union (f annotations) checks types mode
  filter representation annotations aborted :=
    .filter representation (f annotations) aborted
  filterGroup representation annotations checks :=
    .filterGroup representation (f annotations) checks

private def collectRepresentation (representation : Representation) :
    List Annotations :=
  Representation.fold collectAlgebra representation

private def collectCheck (check : Check) : List Annotations :=
  Check.fold collectAlgebra check

private def modifyRepresentation (f : Annotations → Annotations)
    (representation : Representation) : Representation :=
  Representation.fold (modifyAlgebra f) representation

private def modifyCheck (f : Annotations → Annotations) (check : Check) : Check :=
  Check.fold (modifyAlgebra f) check

mutual

private theorem modifyRepresentation_id (representation : Representation) :
    modifyRepresentation id representation = representation := by
  cases representation with
  | declaration rep annotations parameters checks =>
      rw [modifyRepresentation, Representation.fold_declaration]
      change Representation.declaration rep annotations
          (parameters.map (Representation.fold (modifyAlgebra id)))
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyRepresentationList_id, modifyCheckList_id]
  | reference ref => rfl
  | suspend annotations checks thunk =>
      rw [modifyRepresentation, Representation.fold_suspend]
      change Representation.suspend annotations
          (checks.map (Check.fold (modifyAlgebra id)))
          (Representation.fold (modifyAlgebra id) thunk) = _
      have thunkId : Representation.fold (modifyAlgebra id) thunk = thunk :=
        modifyRepresentation_id thunk
      rw [modifyCheckList_id, thunkId]
  | null annotations checks =>
      rw [modifyRepresentation, Representation.fold_null]
      change Representation.null annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | undefined annotations checks =>
      rw [modifyRepresentation, Representation.fold_undefined]
      change Representation.undefined annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | void annotations checks =>
      rw [modifyRepresentation, Representation.fold_void]
      change Representation.void annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | never annotations checks =>
      rw [modifyRepresentation, Representation.fold_never]
      change Representation.never annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | unknown annotations checks =>
      rw [modifyRepresentation, Representation.fold_unknown]
      change Representation.unknown annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | any annotations checks =>
      rw [modifyRepresentation, Representation.fold_any]
      change Representation.any annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | string annotations checks =>
      rw [modifyRepresentation, Representation.fold_string]
      change Representation.string annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | number annotations checks =>
      rw [modifyRepresentation, Representation.fold_number]
      change Representation.number annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | boolean annotations checks =>
      rw [modifyRepresentation, Representation.fold_boolean]
      change Representation.boolean annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | bigint annotations checks =>
      rw [modifyRepresentation, Representation.fold_bigint]
      change Representation.bigint annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | symbol annotations checks =>
      rw [modifyRepresentation, Representation.fold_symbol]
      change Representation.symbol annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | literal annotations checks value =>
      rw [modifyRepresentation, Representation.fold_literal]
      change Representation.literal annotations
          (checks.map (Check.fold (modifyAlgebra id))) value = _
      rw [modifyCheckList_id]
  | uniqueSymbol annotations checks key =>
      rw [modifyRepresentation, Representation.fold_uniqueSymbol]
      change Representation.uniqueSymbol annotations
          (checks.map (Check.fold (modifyAlgebra id))) key = _
      rw [modifyCheckList_id]
  | objectKeyword annotations checks =>
      rw [modifyRepresentation, Representation.fold_objectKeyword]
      change Representation.objectKeyword annotations
          (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id]
  | enum annotations checks entries =>
      rw [modifyRepresentation, Representation.fold_enum]
      change Representation.enum annotations
          (checks.map (Check.fold (modifyAlgebra id))) entries = _
      rw [modifyCheckList_id]
  | templateLiteral annotations checks parts =>
      rw [modifyRepresentation, Representation.fold_templateLiteral]
      change Representation.templateLiteral annotations
          (checks.map (Check.fold (modifyAlgebra id)))
          (parts.map (Representation.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id, modifyRepresentationList_id]
  | arrays annotations checks elements rest =>
      rw [modifyRepresentation, Representation.fold_arrays]
      change Representation.arrays annotations
          (checks.map (Check.fold (modifyAlgebra id)))
          ((elements.map fun element =>
            ElementOf.mk element.isOptional
              (Representation.fold (modifyAlgebra id) element.type)
              element.annotations).map fun element =>
                ElementOf.mk element.isOptional element.type (id element.annotations))
          (rest.map (Representation.fold (modifyAlgebra id))) = _
      rw [modifyCheckList_id, modifyElements_id, modifyRepresentationList_id]
  | objects annotations checks properties indexes =>
      rw [modifyRepresentation, Representation.fold_objects]
      change Representation.objects annotations
          (checks.map (Check.fold (modifyAlgebra id)))
          ((properties.map fun property =>
            PropertySignatureOf.mk property.name
              (Representation.fold (modifyAlgebra id) property.type)
              property.isOptional property.isMutable property.annotations).map
                fun property => PropertySignatureOf.mk property.name property.type
                  property.isOptional property.isMutable (id property.annotations))
          (indexes.map fun index => IndexSignatureOf.mk
            (Representation.fold (modifyAlgebra id) index.parameter)
            (Representation.fold (modifyAlgebra id) index.type)) = _
      rw [modifyCheckList_id, modifyProperties_id, modifyIndexes_id]
  | union annotations checks types mode =>
      rw [modifyRepresentation, Representation.fold_union]
      change Representation.union annotations
          (checks.map (Check.fold (modifyAlgebra id)))
          (types.map (Representation.fold (modifyAlgebra id))) mode = _
      rw [modifyCheckList_id, modifyRepresentationList_id]
termination_by structural representation

private theorem modifyCheck_id (check : Check) :
    modifyCheck id check = check := by
  cases check with
  | filter representation annotations aborted =>
      rw [modifyCheck, Check.fold_filter]
      change Check.filter
          { id := representation.id
            payload := representation.payload
            schemas := representation.schemas.map
              (List.map (Representation.fold (modifyAlgebra id))) }
          annotations aborted = _
      rw [modifyCheckAnnotation_id]
  | filterGroup representation annotations checks =>
      rw [modifyCheck, Check.fold_filterGroup]
      change Check.filterGroup
          (representation.map fun value =>
            { id := value.id
              payload := value.payload
              schemas := value.schemas.map
                (List.map (Representation.fold (modifyAlgebra id))) })
          annotations (checks.map (Check.fold (modifyAlgebra id))) = _
      rw [modifyCheckAnnotationOptional_id, modifyCheckList_id]
termination_by structural check

private theorem modifyRepresentationList_id (representations : List Representation) :
    representations.map (Representation.fold (modifyAlgebra id)) = representations := by
  cases representations with
  | nil => rfl
  | cons head tail =>
      change Representation.fold (modifyAlgebra id) head ::
          tail.map (Representation.fold (modifyAlgebra id)) = head :: tail
      have headId : Representation.fold (modifyAlgebra id) head = head :=
        modifyRepresentation_id head
      rw [headId, modifyRepresentationList_id tail]
termination_by structural representations

private theorem modifyCheckList_id (checks : List Check) :
    checks.map (Check.fold (modifyAlgebra id)) = checks := by
  cases checks with
  | nil => rfl
  | cons head tail =>
      change Check.fold (modifyAlgebra id) head ::
          tail.map (Check.fold (modifyAlgebra id)) = head :: tail
      have headId : Check.fold (modifyAlgebra id) head = head := modifyCheck_id head
      rw [headId, modifyCheckList_id tail]
termination_by structural checks

private theorem modifyElements_id (elements : List (ElementOf Representation)) :
    (elements.map fun element =>
      ElementOf.mk element.isOptional
        (Representation.fold (modifyAlgebra id) element.type)
        element.annotations).map (fun element =>
          ElementOf.mk element.isOptional element.type (id element.annotations)) =
      elements := by
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk isOptional type annotations =>
          change ElementOf.mk isOptional
                (Representation.fold (modifyAlgebra id) type) annotations ::
              ((tail.map fun element => ElementOf.mk element.isOptional
                (Representation.fold (modifyAlgebra id) element.type)
                element.annotations).map fun element =>
                  ElementOf.mk element.isOptional element.type
                    (id element.annotations)) =
            ElementOf.mk isOptional type annotations :: tail
          have typeId : Representation.fold (modifyAlgebra id) type = type :=
            modifyRepresentation_id type
          rw [typeId, modifyElements_id tail]
termination_by structural elements

private theorem modifyProperties_id
    (properties : List (PropertySignatureOf Representation)) :
    (properties.map fun property => PropertySignatureOf.mk property.name
      (Representation.fold (modifyAlgebra id) property.type)
      property.isOptional property.isMutable property.annotations).map
        (fun property => PropertySignatureOf.mk property.name property.type
          property.isOptional property.isMutable (id property.annotations)) = properties := by
  cases properties with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk name type isOptional isMutable annotations =>
          change PropertySignatureOf.mk name
                (Representation.fold (modifyAlgebra id) type)
                isOptional isMutable annotations ::
              ((tail.map fun property => PropertySignatureOf.mk property.name
                (Representation.fold (modifyAlgebra id) property.type)
                property.isOptional property.isMutable property.annotations).map
                  fun property => PropertySignatureOf.mk property.name property.type
                    property.isOptional property.isMutable (id property.annotations)) =
            PropertySignatureOf.mk name type isOptional isMutable annotations :: tail
          have typeId : Representation.fold (modifyAlgebra id) type = type :=
            modifyRepresentation_id type
          rw [typeId, modifyProperties_id tail]
termination_by structural properties

private theorem modifyIndexes_id
    (indexes : List (IndexSignatureOf Representation)) :
    indexes.map (fun (index : IndexSignatureOf Representation) =>
      { parameter := Representation.fold (modifyAlgebra id) index.parameter
        type := Representation.fold (modifyAlgebra id) index.type }) = indexes := by
  cases indexes with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk parameter type =>
          change IndexSignatureOf.mk
                (Representation.fold (modifyAlgebra id) parameter)
                (Representation.fold (modifyAlgebra id) type) ::
              tail.map (fun (index : IndexSignatureOf Representation) =>
                { parameter := Representation.fold (modifyAlgebra id) index.parameter
                  type := Representation.fold (modifyAlgebra id) index.type }) =
            IndexSignatureOf.mk parameter type :: tail
          have parameterId : Representation.fold (modifyAlgebra id) parameter = parameter :=
            modifyRepresentation_id parameter
          have typeId : Representation.fold (modifyAlgebra id) type = type :=
            modifyRepresentation_id type
          rw [parameterId, typeId, modifyIndexes_id tail]
termination_by structural indexes

private theorem modifySchemas_id (schemas : Option (List Representation)) :
    schemas.map (List.map (Representation.fold (modifyAlgebra id))) = schemas := by
  cases schemas with
  | none => rfl
  | some values =>
      change some (values.map (Representation.fold (modifyAlgebra id))) = some values
      rw [modifyRepresentationList_id values]
termination_by structural schemas

private theorem modifyCheckAnnotation_id
    (annotation : CheckRepresentationAnnotationOf Representation) :
    { id := annotation.id
      payload := annotation.payload
      schemas := annotation.schemas.map
        (List.map (Representation.fold (modifyAlgebra id))) } = annotation := by
  cases annotation with
  | mk name payload schemas =>
      change CheckRepresentationAnnotationOf.mk name payload
          (schemas.map (List.map (Representation.fold (modifyAlgebra id)))) =
        CheckRepresentationAnnotationOf.mk name payload schemas
      rw [modifySchemas_id schemas]
termination_by structural annotation

private theorem modifyCheckAnnotationOptional_id
    (annotation : Option (CheckRepresentationAnnotationOf Representation)) :
    annotation.map (fun value =>
      { id := value.id
        payload := value.payload
        schemas := value.schemas.map
          (List.map (Representation.fold (modifyAlgebra id))) }) = annotation := by
  cases annotation with
  | none => rfl
  | some value =>
      change some
          { id := value.id
            payload := value.payload
            schemas := value.schemas.map
              (List.map (Representation.fold (modifyAlgebra id))) } = some value
      rw [modifyCheckAnnotation_id value]
termination_by structural annotation

end

mutual

private theorem modifyRepresentation_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (representation : Representation) :
    modifyRepresentation first representation =
      modifyRepresentation second representation := by
  cases representation with
  | declaration rep annotations parameters checks =>
      rw [modifyRepresentation, Representation.fold_declaration,
        modifyRepresentation, Representation.fold_declaration]
      change Representation.declaration rep (first annotations)
          (parameters.map (Representation.fold (modifyAlgebra first)))
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.declaration rep (second annotations)
          (parameters.map (Representation.fold (modifyAlgebra second)))
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyRepresentationList_congr pointwise,
        modifyCheckList_congr pointwise]
  | reference ref => rfl
  | suspend annotations checks thunk =>
      rw [modifyRepresentation, Representation.fold_suspend,
        modifyRepresentation, Representation.fold_suspend]
      change Representation.suspend (first annotations)
          (checks.map (Check.fold (modifyAlgebra first)))
          (modifyRepresentation first thunk) =
        Representation.suspend (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
          (modifyRepresentation second thunk)
      rw [pointwise, modifyCheckList_congr pointwise,
        modifyRepresentation_congr pointwise thunk]
  | null annotations checks =>
      rw [modifyRepresentation, Representation.fold_null,
        modifyRepresentation, Representation.fold_null]
      change Representation.null (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.null (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | undefined annotations checks =>
      rw [modifyRepresentation, Representation.fold_undefined,
        modifyRepresentation, Representation.fold_undefined]
      change Representation.undefined (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.undefined (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | void annotations checks =>
      rw [modifyRepresentation, Representation.fold_void,
        modifyRepresentation, Representation.fold_void]
      change Representation.void (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.void (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | never annotations checks =>
      rw [modifyRepresentation, Representation.fold_never,
        modifyRepresentation, Representation.fold_never]
      change Representation.never (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.never (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | unknown annotations checks =>
      rw [modifyRepresentation, Representation.fold_unknown,
        modifyRepresentation, Representation.fold_unknown]
      change Representation.unknown (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.unknown (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | any annotations checks =>
      rw [modifyRepresentation, Representation.fold_any,
        modifyRepresentation, Representation.fold_any]
      change Representation.any (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.any (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | string annotations checks =>
      rw [modifyRepresentation, Representation.fold_string,
        modifyRepresentation, Representation.fold_string]
      change Representation.string (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.string (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | number annotations checks =>
      rw [modifyRepresentation, Representation.fold_number,
        modifyRepresentation, Representation.fold_number]
      change Representation.number (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.number (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | boolean annotations checks =>
      rw [modifyRepresentation, Representation.fold_boolean,
        modifyRepresentation, Representation.fold_boolean]
      change Representation.boolean (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.boolean (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | bigint annotations checks =>
      rw [modifyRepresentation, Representation.fold_bigint,
        modifyRepresentation, Representation.fold_bigint]
      change Representation.bigint (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.bigint (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | symbol annotations checks =>
      rw [modifyRepresentation, Representation.fold_symbol,
        modifyRepresentation, Representation.fold_symbol]
      change Representation.symbol (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.symbol (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | literal annotations checks value =>
      rw [modifyRepresentation, Representation.fold_literal,
        modifyRepresentation, Representation.fold_literal]
      change Representation.literal (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) value =
        Representation.literal (second annotations)
          (checks.map (Check.fold (modifyAlgebra second))) value
      rw [pointwise, modifyCheckList_congr pointwise]
  | uniqueSymbol annotations checks key =>
      rw [modifyRepresentation, Representation.fold_uniqueSymbol,
        modifyRepresentation, Representation.fold_uniqueSymbol]
      change Representation.uniqueSymbol (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) key =
        Representation.uniqueSymbol (second annotations)
          (checks.map (Check.fold (modifyAlgebra second))) key
      rw [pointwise, modifyCheckList_congr pointwise]
  | objectKeyword annotations checks =>
      rw [modifyRepresentation, Representation.fold_objectKeyword,
        modifyRepresentation, Representation.fold_objectKeyword]
      change Representation.objectKeyword (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) =
        Representation.objectKeyword (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise]
  | enum annotations checks entries =>
      rw [modifyRepresentation, Representation.fold_enum,
        modifyRepresentation, Representation.fold_enum]
      change Representation.enum (first annotations)
          (checks.map (Check.fold (modifyAlgebra first))) entries =
        Representation.enum (second annotations)
          (checks.map (Check.fold (modifyAlgebra second))) entries
      rw [pointwise, modifyCheckList_congr pointwise]
  | templateLiteral annotations checks parts =>
      rw [modifyRepresentation, Representation.fold_templateLiteral,
        modifyRepresentation, Representation.fold_templateLiteral]
      change Representation.templateLiteral (first annotations)
          (checks.map (Check.fold (modifyAlgebra first)))
          (parts.map (Representation.fold (modifyAlgebra first))) =
        Representation.templateLiteral (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
          (parts.map (Representation.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise,
        modifyRepresentationList_congr pointwise]
  | arrays annotations checks elements rest =>
      rw [modifyRepresentation, Representation.fold_arrays,
        modifyRepresentation, Representation.fold_arrays]
      change Representation.arrays (first annotations)
          (checks.map (Check.fold (modifyAlgebra first)))
          ((elements.map fun element =>
            ElementOf.mk element.isOptional
              (Representation.fold (modifyAlgebra first) element.type)
              element.annotations).map fun element =>
                ElementOf.mk element.isOptional element.type
                  (first element.annotations))
          (rest.map (Representation.fold (modifyAlgebra first))) =
        Representation.arrays (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
          ((elements.map fun element =>
            ElementOf.mk element.isOptional
              (Representation.fold (modifyAlgebra second) element.type)
              element.annotations).map fun element =>
                ElementOf.mk element.isOptional element.type
                  (second element.annotations))
          (rest.map (Representation.fold (modifyAlgebra second)))
      rw [pointwise, modifyCheckList_congr pointwise,
        modifyElements_congr pointwise, modifyRepresentationList_congr pointwise]
  | objects annotations checks properties indexes =>
      rw [modifyRepresentation, Representation.fold_objects,
        modifyRepresentation, Representation.fold_objects]
      change Representation.objects (first annotations)
          (checks.map (Check.fold (modifyAlgebra first)))
          ((properties.map fun property => PropertySignatureOf.mk property.name
            (Representation.fold (modifyAlgebra first) property.type)
            property.isOptional property.isMutable property.annotations).map
              fun property => PropertySignatureOf.mk property.name property.type
                property.isOptional property.isMutable (first property.annotations))
          (indexes.map fun index => IndexSignatureOf.mk
            (Representation.fold (modifyAlgebra first) index.parameter)
            (Representation.fold (modifyAlgebra first) index.type)) =
        Representation.objects (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
          ((properties.map fun property => PropertySignatureOf.mk property.name
            (Representation.fold (modifyAlgebra second) property.type)
            property.isOptional property.isMutable property.annotations).map
              fun property => PropertySignatureOf.mk property.name property.type
                property.isOptional property.isMutable (second property.annotations))
          (indexes.map fun index => IndexSignatureOf.mk
            (Representation.fold (modifyAlgebra second) index.parameter)
            (Representation.fold (modifyAlgebra second) index.type))
      rw [pointwise, modifyCheckList_congr pointwise,
        modifyProperties_congr pointwise, modifyIndexes_congr pointwise]
  | union annotations checks types mode =>
      rw [modifyRepresentation, Representation.fold_union,
        modifyRepresentation, Representation.fold_union]
      change Representation.union (first annotations)
          (checks.map (Check.fold (modifyAlgebra first)))
          (types.map (Representation.fold (modifyAlgebra first))) mode =
        Representation.union (second annotations)
          (checks.map (Check.fold (modifyAlgebra second)))
          (types.map (Representation.fold (modifyAlgebra second))) mode
      rw [pointwise, modifyCheckList_congr pointwise,
        modifyRepresentationList_congr pointwise]
termination_by structural representation

private theorem modifyCheck_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (check : Check) :
    modifyCheck first check = modifyCheck second check := by
  cases check with
  | filter representation annotations aborted =>
      rw [modifyCheck, Check.fold_filter, modifyCheck, Check.fold_filter]
      change Check.filter
          (CheckRepresentationAnnotationOf.mk representation.id
            representation.payload
            (representation.schemas.map
              (List.map (Representation.fold (modifyAlgebra first)))))
          (first annotations) aborted =
        Check.filter
          (CheckRepresentationAnnotationOf.mk representation.id
            representation.payload
            (representation.schemas.map
              (List.map (Representation.fold (modifyAlgebra second)))))
          (second annotations) aborted
      rw [modifyCheckAnnotation_congr pointwise, pointwise]
  | filterGroup representation annotations checks =>
      rw [modifyCheck, Check.fold_filterGroup,
        modifyCheck, Check.fold_filterGroup]
      change Check.filterGroup
          (representation.map fun value => CheckRepresentationAnnotationOf.mk
            value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra first)))))
          (first annotations) (checks.map (Check.fold (modifyAlgebra first))) =
        Check.filterGroup
          (representation.map fun value => CheckRepresentationAnnotationOf.mk
            value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra second)))))
          (second annotations) (checks.map (Check.fold (modifyAlgebra second)))
      rw [modifyCheckAnnotationOptional_congr pointwise, pointwise,
        modifyCheckList_congr pointwise]
termination_by structural check

private theorem modifyRepresentationList_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (representations : List Representation) :
    representations.map (Representation.fold (modifyAlgebra first)) =
      representations.map (Representation.fold (modifyAlgebra second)) := by
  cases representations with
  | nil => rfl
  | cons head tail =>
      simp only [List.map]
      change modifyRepresentation first head ::
          tail.map (Representation.fold (modifyAlgebra first)) =
        modifyRepresentation second head ::
          tail.map (Representation.fold (modifyAlgebra second))
      rw [modifyRepresentation_congr pointwise head,
        modifyRepresentationList_congr pointwise tail]
termination_by structural representations

private theorem modifyCheckList_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (checks : List Check) :
    checks.map (Check.fold (modifyAlgebra first)) =
      checks.map (Check.fold (modifyAlgebra second)) := by
  cases checks with
  | nil => rfl
  | cons head tail =>
      simp only [List.map]
      change modifyCheck first head ::
          tail.map (Check.fold (modifyAlgebra first)) =
        modifyCheck second head ::
          tail.map (Check.fold (modifyAlgebra second))
      rw [modifyCheck_congr pointwise head, modifyCheckList_congr pointwise tail]
termination_by structural checks

private theorem modifyElements_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (elements : List (ElementOf Representation)) :
    (elements.map fun element =>
      ElementOf.mk element.isOptional
        (Representation.fold (modifyAlgebra first) element.type)
        element.annotations).map (fun element =>
          ElementOf.mk element.isOptional element.type (first element.annotations)) =
      (elements.map fun element =>
        ElementOf.mk element.isOptional
          (Representation.fold (modifyAlgebra second) element.type)
          element.annotations).map (fun element =>
            ElementOf.mk element.isOptional element.type (second element.annotations)) := by
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk isOptional type annotations =>
          change ElementOf.mk isOptional
                (modifyRepresentation first type)
                (first annotations) :: _ =
            ElementOf.mk isOptional
                (modifyRepresentation second type)
                (second annotations) :: _
          rw [modifyRepresentation_congr pointwise type, pointwise,
            modifyElements_congr pointwise tail]
termination_by structural elements

private theorem modifyProperties_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (properties : List (PropertySignatureOf Representation)) :
    (properties.map fun property => PropertySignatureOf.mk property.name
      (Representation.fold (modifyAlgebra first) property.type)
      property.isOptional property.isMutable property.annotations).map
        (fun property => PropertySignatureOf.mk property.name property.type
          property.isOptional property.isMutable (first property.annotations)) =
      (properties.map fun property => PropertySignatureOf.mk property.name
        (Representation.fold (modifyAlgebra second) property.type)
        property.isOptional property.isMutable property.annotations).map
          (fun property => PropertySignatureOf.mk property.name property.type
            property.isOptional property.isMutable (second property.annotations)) := by
  cases properties with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk name type isOptional isMutable annotations =>
          change PropertySignatureOf.mk name
                (modifyRepresentation first type)
                isOptional isMutable (first annotations) :: _ =
            PropertySignatureOf.mk name
                (modifyRepresentation second type)
                isOptional isMutable (second annotations) :: _
          rw [modifyRepresentation_congr pointwise type, pointwise,
            modifyProperties_congr pointwise tail]
termination_by structural properties

private theorem modifyIndexes_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (indexes : List (IndexSignatureOf Representation)) :
    indexes.map (fun index => IndexSignatureOf.mk
        (Representation.fold (modifyAlgebra first) index.parameter)
        (Representation.fold (modifyAlgebra first) index.type)) =
      indexes.map (fun index => IndexSignatureOf.mk
        (Representation.fold (modifyAlgebra second) index.parameter)
        (Representation.fold (modifyAlgebra second) index.type)) := by
  cases indexes with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk parameter type =>
          change IndexSignatureOf.mk
                (modifyRepresentation first parameter)
                (modifyRepresentation first type) :: _ =
            IndexSignatureOf.mk
                (modifyRepresentation second parameter)
                (modifyRepresentation second type) :: _
          rw [modifyRepresentation_congr pointwise parameter,
            modifyRepresentation_congr pointwise type,
            modifyIndexes_congr pointwise tail]
termination_by structural indexes

private theorem modifySchemas_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (schemas : Option (List Representation)) :
    schemas.map (List.map (Representation.fold (modifyAlgebra first))) =
      schemas.map (List.map (Representation.fold (modifyAlgebra second))) := by
  cases schemas with
  | none => rfl
  | some values =>
      simp only [Option.map]
      rw [modifyRepresentationList_congr pointwise values]
termination_by structural schemas

private theorem modifyCheckAnnotation_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (annotation : CheckRepresentationAnnotationOf Representation) :
    CheckRepresentationAnnotationOf.mk annotation.id annotation.payload
        (annotation.schemas.map
          (List.map (Representation.fold (modifyAlgebra first)))) =
      CheckRepresentationAnnotationOf.mk annotation.id annotation.payload
        (annotation.schemas.map
          (List.map (Representation.fold (modifyAlgebra second)))) := by
  cases annotation with
  | mk name payload schemas =>
      rw [modifySchemas_congr pointwise schemas]
termination_by structural annotation

private theorem modifyCheckAnnotationOptional_congr
    {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (annotation : Option (CheckRepresentationAnnotationOf Representation)) :
    annotation.map (fun value =>
      CheckRepresentationAnnotationOf.mk value.id value.payload
        (value.schemas.map
          (List.map (Representation.fold (modifyAlgebra first))))) =
      annotation.map (fun value =>
        CheckRepresentationAnnotationOf.mk value.id value.payload
          (value.schemas.map
            (List.map (Representation.fold (modifyAlgebra second))))) := by
  cases annotation with
  | none => rfl
  | some value =>
      exact congrArg some (modifyCheckAnnotation_congr pointwise value)
termination_by structural annotation

end

mutual

private theorem modifyRepresentation_comp (representation : Representation)
    (first second : Annotations → Annotations) :
    modifyRepresentation second (modifyRepresentation first representation) =
      modifyRepresentation (second ∘ first) representation := by
  cases representation with
  | declaration rep annotations parameters checks =>
      simp only [modifyRepresentation, Representation.fold_declaration, modifyAlgebra]
      change Representation.declaration rep (second (first annotations))
          ((parameters.map (Representation.fold (modifyAlgebra first))).map
            (Representation.fold (modifyAlgebra second)))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.declaration rep ((second ∘ first) annotations)
          (parameters.map (Representation.fold (modifyAlgebra (second ∘ first))))
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyRepresentationList_comp parameters first second,
        modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | reference ref => rfl
  | suspend annotations checks thunk =>
      simp only [modifyRepresentation, Representation.fold_suspend, modifyAlgebra]
      change Representation.suspend (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second)))
          (modifyRepresentation second (modifyRepresentation first thunk)) =
        Representation.suspend ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
          (modifyRepresentation (second ∘ first) thunk)
      rw [modifyCheckList_comp checks first second,
        modifyRepresentation_comp thunk first second]
      rw [Function.comp_apply]
  | null annotations checks =>
      simp only [modifyRepresentation, Representation.fold_null, modifyAlgebra]
      change Representation.null (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.null ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | undefined annotations checks =>
      simp only [modifyRepresentation, Representation.fold_undefined, modifyAlgebra]
      change Representation.undefined (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.undefined ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | void annotations checks =>
      simp only [modifyRepresentation, Representation.fold_void, modifyAlgebra]
      change Representation.void (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.void ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | never annotations checks =>
      simp only [modifyRepresentation, Representation.fold_never, modifyAlgebra]
      change Representation.never (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.never ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | unknown annotations checks =>
      simp only [modifyRepresentation, Representation.fold_unknown, modifyAlgebra]
      change Representation.unknown (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.unknown ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | any annotations checks =>
      simp only [modifyRepresentation, Representation.fold_any, modifyAlgebra]
      change Representation.any (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.any ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | string annotations checks =>
      simp only [modifyRepresentation, Representation.fold_string, modifyAlgebra]
      change Representation.string (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.string ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | number annotations checks =>
      simp only [modifyRepresentation, Representation.fold_number, modifyAlgebra]
      change Representation.number (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.number ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | boolean annotations checks =>
      simp only [modifyRepresentation, Representation.fold_boolean, modifyAlgebra]
      change Representation.boolean (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.boolean ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | bigint annotations checks =>
      simp only [modifyRepresentation, Representation.fold_bigint, modifyAlgebra]
      change Representation.bigint (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.bigint ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | symbol annotations checks =>
      simp only [modifyRepresentation, Representation.fold_symbol, modifyAlgebra]
      change Representation.symbol (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.symbol ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | literal annotations checks value =>
      simp only [modifyRepresentation, Representation.fold_literal, modifyAlgebra]
      change Representation.literal (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) value =
        Representation.literal ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first)))) value
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | uniqueSymbol annotations checks key =>
      simp only [modifyRepresentation, Representation.fold_uniqueSymbol, modifyAlgebra]
      change Representation.uniqueSymbol (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) key =
        Representation.uniqueSymbol ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first)))) key
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | objectKeyword annotations checks =>
      simp only [modifyRepresentation, Representation.fold_objectKeyword, modifyAlgebra]
      change Representation.objectKeyword (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Representation.objectKeyword ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | enum annotations checks entries =>
      simp only [modifyRepresentation, Representation.fold_enum, modifyAlgebra]
      change Representation.enum (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) entries =
        Representation.enum ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first)))) entries
      rw [modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  | templateLiteral annotations checks parts =>
      simp only [modifyRepresentation, Representation.fold_templateLiteral, modifyAlgebra]
      change Representation.templateLiteral (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second)))
          ((parts.map (Representation.fold (modifyAlgebra first))).map
            (Representation.fold (modifyAlgebra second))) =
        Representation.templateLiteral ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
          (parts.map (Representation.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second,
        modifyRepresentationList_comp parts first second]
      rw [Function.comp_apply]
  | arrays annotations checks elements rest =>
      simp only [modifyRepresentation, Representation.fold_arrays, modifyAlgebra]
      change Representation.arrays (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second)))
          ((((elements.map (fun element => ElementOf.mk element.isOptional
              (Representation.fold (modifyAlgebra first) element.type)
              element.annotations)).map (fun element =>
                ElementOf.mk element.isOptional element.type
                  (first element.annotations))).map (fun element =>
            ElementOf.mk element.isOptional
              (Representation.fold (modifyAlgebra second) element.type)
              element.annotations)).map (fun element =>
                ElementOf.mk element.isOptional element.type
                  (second element.annotations)))
          ((rest.map (Representation.fold (modifyAlgebra first))).map
            (Representation.fold (modifyAlgebra second))) =
        Representation.arrays ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
          ((elements.map (fun element => ElementOf.mk element.isOptional
            (Representation.fold (modifyAlgebra (second ∘ first)) element.type)
            element.annotations)).map (fun element =>
              ElementOf.mk element.isOptional element.type
                ((second ∘ first) element.annotations)))
          (rest.map (Representation.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckList_comp checks first second,
        modifyElements_comp elements first second,
        modifyRepresentationList_comp rest first second]
      rw [Function.comp_apply]
  | objects annotations checks properties indexes =>
      simp only [modifyRepresentation, Representation.fold_objects, modifyAlgebra]
      change Representation.objects (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second)))
          ((((properties.map (fun property => PropertySignatureOf.mk property.name
              (Representation.fold (modifyAlgebra first) property.type)
              property.isOptional property.isMutable property.annotations)).map
                (fun property => PropertySignatureOf.mk property.name property.type
                  property.isOptional property.isMutable
                  (first property.annotations))).map (fun property =>
              PropertySignatureOf.mk property.name
                (Representation.fold (modifyAlgebra second) property.type)
                property.isOptional property.isMutable property.annotations)).map
                  (fun property => PropertySignatureOf.mk property.name property.type
                    property.isOptional property.isMutable
                    (second property.annotations)))
          ((indexes.map (fun index => IndexSignatureOf.mk
              (Representation.fold (modifyAlgebra first) index.parameter)
              (Representation.fold (modifyAlgebra first) index.type))).map (fun index =>
            IndexSignatureOf.mk
              (Representation.fold (modifyAlgebra second) index.parameter)
              (Representation.fold (modifyAlgebra second) index.type))) =
        Representation.objects ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
          ((properties.map (fun property => PropertySignatureOf.mk property.name
            (Representation.fold (modifyAlgebra (second ∘ first)) property.type)
            property.isOptional property.isMutable property.annotations)).map
              (fun property => PropertySignatureOf.mk property.name property.type
                property.isOptional property.isMutable
                ((second ∘ first) property.annotations)))
          (indexes.map (fun index => IndexSignatureOf.mk
            (Representation.fold (modifyAlgebra (second ∘ first)) index.parameter)
            (Representation.fold (modifyAlgebra (second ∘ first)) index.type)))
      rw [modifyCheckList_comp checks first second,
        modifyProperties_comp properties first second,
        modifyIndexes_comp indexes first second]
      rw [Function.comp_apply]
  | union annotations checks types mode =>
      simp only [modifyRepresentation, Representation.fold_union, modifyAlgebra]
      change Representation.union (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second)))
          ((types.map (Representation.fold (modifyAlgebra first))).map
            (Representation.fold (modifyAlgebra second))) mode =
        Representation.union ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
          (types.map (Representation.fold (modifyAlgebra (second ∘ first)))) mode
      rw [modifyCheckList_comp checks first second,
        modifyRepresentationList_comp types first second]
      rw [Function.comp_apply]
  all_goals rfl
termination_by structural representation

private theorem modifyCheck_comp (check : Check)
    (first second : Annotations → Annotations) :
    modifyCheck second (modifyCheck first check) =
      modifyCheck (second ∘ first) check := by
  cases check with
  | filter representation annotations aborted =>
      simp only [modifyCheck, Check.fold_filter, modifyAlgebra]
      change Check.filter
          (CheckRepresentationAnnotationOf.mk representation.id
            representation.payload
            ((representation.schemas.map
              (List.map (Representation.fold (modifyAlgebra first)))).map
                (List.map (Representation.fold (modifyAlgebra second)))))
          (second (first annotations)) aborted =
        Check.filter
          (CheckRepresentationAnnotationOf.mk representation.id
            representation.payload
            (representation.schemas.map
              (List.map (Representation.fold (modifyAlgebra (second ∘ first))))))
          ((second ∘ first) annotations) aborted
      rw [modifySchemas_comp representation.schemas first second]
      rw [Function.comp_apply]
  | filterGroup representation annotations checks =>
      simp only [modifyCheck, Check.fold_filterGroup, modifyAlgebra]
      change Check.filterGroup
          ((representation.map fun value => CheckRepresentationAnnotationOf.mk
            value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra first))))).map
                fun value => CheckRepresentationAnnotationOf.mk value.id value.payload
                  (value.schemas.map
                    (List.map (Representation.fold (modifyAlgebra second)))))
          (second (first annotations))
          ((checks.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        Check.filterGroup
          (representation.map fun value => CheckRepresentationAnnotationOf.mk
            value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra (second ∘ first))))))
          ((second ∘ first) annotations)
          (checks.map (Check.fold (modifyAlgebra (second ∘ first))))
      rw [modifyCheckAnnotationOptional_comp representation first second,
        modifyCheckList_comp checks first second]
      rw [Function.comp_apply]
  all_goals rfl
termination_by structural check

private theorem modifyRepresentationList_comp (representations : List Representation)
    (first second : Annotations → Annotations) :
    (representations.map (Representation.fold (modifyAlgebra first))).map
        (Representation.fold (modifyAlgebra second)) =
      representations.map
        (Representation.fold (modifyAlgebra (second ∘ first))) := by
  cases representations with
  | nil => rfl
  | cons head tail =>
      change modifyRepresentation second (modifyRepresentation first head) ::
          ((tail.map (Representation.fold (modifyAlgebra first))).map
            (Representation.fold (modifyAlgebra second))) =
        modifyRepresentation (second ∘ first) head ::
          tail.map (Representation.fold (modifyAlgebra (second ∘ first)))
      rw [modifyRepresentation_comp head first second,
        modifyRepresentationList_comp tail first second]
termination_by structural representations

private theorem modifyCheckList_comp (checks : List Check)
    (first second : Annotations → Annotations) :
    (checks.map (Check.fold (modifyAlgebra first))).map
        (Check.fold (modifyAlgebra second)) =
      checks.map (Check.fold (modifyAlgebra (second ∘ first))) := by
  cases checks with
  | nil => rfl
  | cons head tail =>
      change modifyCheck second (modifyCheck first head) ::
          ((tail.map (Check.fold (modifyAlgebra first))).map
            (Check.fold (modifyAlgebra second))) =
        modifyCheck (second ∘ first) head ::
          tail.map (Check.fold (modifyAlgebra (second ∘ first)))
      rw [modifyCheck_comp head first second, modifyCheckList_comp tail first second]
termination_by structural checks

private theorem modifyElements_comp (elements : List (ElementOf Representation))
    (first second : Annotations → Annotations) :
    (((elements.map fun element => ElementOf.mk element.isOptional
        (Representation.fold (modifyAlgebra first) element.type)
        element.annotations).map fun element =>
          ElementOf.mk element.isOptional element.type
            (first element.annotations)).map fun element =>
      ElementOf.mk element.isOptional
        (Representation.fold (modifyAlgebra second) element.type)
        element.annotations).map (fun element =>
          ElementOf.mk element.isOptional element.type
            (second element.annotations)) =
      (elements.map fun element => ElementOf.mk element.isOptional
        (Representation.fold (modifyAlgebra (second ∘ first)) element.type)
        element.annotations).map fun element =>
          ElementOf.mk element.isOptional element.type
            ((second ∘ first) element.annotations) := by
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk isOptional type annotations =>
          change ElementOf.mk isOptional
                (modifyRepresentation second (modifyRepresentation first type))
                (second (first annotations)) :: _ =
            ElementOf.mk isOptional (modifyRepresentation (second ∘ first) type)
                ((second ∘ first) annotations) :: _
          rw [modifyRepresentation_comp type first second,
            modifyElements_comp tail first second]
          rw [Function.comp_apply]
  all_goals rfl
termination_by structural elements

private theorem modifyProperties_comp
    (properties : List (PropertySignatureOf Representation))
    (first second : Annotations → Annotations) :
    (((properties.map fun property => PropertySignatureOf.mk property.name
        (Representation.fold (modifyAlgebra first) property.type)
        property.isOptional property.isMutable property.annotations).map
          fun property => PropertySignatureOf.mk property.name property.type
            property.isOptional property.isMutable
            (first property.annotations)).map fun property =>
      PropertySignatureOf.mk property.name
        (Representation.fold (modifyAlgebra second) property.type)
        property.isOptional property.isMutable property.annotations).map
          (fun property => PropertySignatureOf.mk property.name property.type
            property.isOptional property.isMutable
            (second property.annotations)) =
      (properties.map fun property => PropertySignatureOf.mk property.name
        (Representation.fold (modifyAlgebra (second ∘ first)) property.type)
        property.isOptional property.isMutable property.annotations).map
          fun property => PropertySignatureOf.mk property.name property.type
            property.isOptional property.isMutable
            ((second ∘ first) property.annotations) := by
  cases properties with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk name type isOptional isMutable annotations =>
          change PropertySignatureOf.mk name
                (modifyRepresentation second (modifyRepresentation first type))
                isOptional isMutable (second (first annotations)) :: _ =
            PropertySignatureOf.mk name (modifyRepresentation (second ∘ first) type)
                isOptional isMutable ((second ∘ first) annotations) :: _
          rw [modifyRepresentation_comp type first second,
            modifyProperties_comp tail first second]
          rw [Function.comp_apply]
  all_goals rfl
termination_by structural properties

private theorem modifyIndexes_comp
    (indexes : List (IndexSignatureOf Representation))
    (first second : Annotations → Annotations) :
    (indexes.map (fun index => IndexSignatureOf.mk
      (Representation.fold (modifyAlgebra first) index.parameter)
      (Representation.fold (modifyAlgebra first) index.type))).map
        (fun index => IndexSignatureOf.mk
          (Representation.fold (modifyAlgebra second) index.parameter)
          (Representation.fold (modifyAlgebra second) index.type)) =
      indexes.map (fun index => IndexSignatureOf.mk
        (Representation.fold (modifyAlgebra (second ∘ first)) index.parameter)
        (Representation.fold (modifyAlgebra (second ∘ first)) index.type)) := by
  cases indexes with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk parameter type =>
          change IndexSignatureOf.mk
                (modifyRepresentation second (modifyRepresentation first parameter))
                (modifyRepresentation second (modifyRepresentation first type)) :: _ =
            IndexSignatureOf.mk (modifyRepresentation (second ∘ first) parameter)
                (modifyRepresentation (second ∘ first) type) :: _
          rw [modifyRepresentation_comp parameter first second,
            modifyRepresentation_comp type first second,
            modifyIndexes_comp tail first second]
termination_by structural indexes

private theorem modifySchemas_comp (schemas : Option (List Representation))
    (first second : Annotations → Annotations) :
    (schemas.map (List.map (Representation.fold (modifyAlgebra first)))).map
        (List.map (Representation.fold (modifyAlgebra second))) =
      schemas.map
        (List.map (Representation.fold (modifyAlgebra (second ∘ first)))) := by
  cases schemas with
  | none => rfl
  | some values =>
      exact congrArg some (modifyRepresentationList_comp values first second)
termination_by structural schemas

private theorem modifyCheckAnnotationOptional_comp
    (annotation : Option (CheckRepresentationAnnotationOf Representation))
    (first second : Annotations → Annotations) :
    (annotation.map fun value => CheckRepresentationAnnotationOf.mk
      value.id value.payload
      (value.schemas.map
        (List.map (Representation.fold (modifyAlgebra first))))).map
          (fun value => CheckRepresentationAnnotationOf.mk
            value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra second))))) =
      annotation.map fun value => CheckRepresentationAnnotationOf.mk
        value.id value.payload
        (value.schemas.map
          (List.map (Representation.fold (modifyAlgebra (second ∘ first))))) := by
  cases annotation with
  | none => rfl
  | some value =>
      cases value with
      | mk name payload schemas =>
          change some (CheckRepresentationAnnotationOf.mk name payload
              ((schemas.map
                (List.map (Representation.fold (modifyAlgebra first)))).map
                  (List.map (Representation.fold (modifyAlgebra second))))) =
            some (CheckRepresentationAnnotationOf.mk name payload
              (schemas.map (List.map
                (Representation.fold (modifyAlgebra (second ∘ first))))))
          rw [modifySchemas_comp schemas first second]
termination_by structural annotation

end

private theorem appendMany_map (lists : List (List Annotations))
    (f : Annotations → Annotations) :
    appendMany (lists.map (List.map f)) = (appendMany lists).map f := by
  induction lists with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, appendMany]
      rw [map_append_exact, ih]

mutual

private theorem collect_modifyRepresentation (representation : Representation)
    (f : Annotations → Annotations) :
    collectRepresentation (modifyRepresentation f representation) =
      (collectRepresentation representation).map f := by
  cases representation with
  | reference ref => rfl
  | declaration rep annotations parameters checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_declaration, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have parametersLaw := collect_modifyRepresentationList parameters f
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at parametersLaw checksLaw
      rw [parametersLaw, checksLaw]
  | suspend annotations checks thunk =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_suspend, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have thunkLaw := collect_modifyRepresentation thunk f
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectRepresentation, modifyRepresentation,
        collectAlgebra, modifyAlgebra] at thunkLaw checksLaw
      rw [checksLaw, thunkLaw]
  | null annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_null, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | undefined annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_undefined, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | void annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_void, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | never annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_never, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | unknown annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_unknown, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | any annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_any, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | string annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_string, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | number annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_number, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | boolean annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_boolean, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | bigint annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_bigint, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | symbol annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_symbol, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | literal annotations checks value =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_literal, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | uniqueSymbol annotations checks key =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_uniqueSymbol, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | objectKeyword annotations checks =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_objectKeyword, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | enum annotations checks entries =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_enum, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact]
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw
      rw [checksLaw]
  | templateLiteral annotations checks parts =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_templateLiteral, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have checksLaw := collect_modifyCheckList checks f
      have partsLaw := collect_modifyRepresentationList parts f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw partsLaw
      rw [checksLaw, partsLaw]
  | arrays annotations checks elements rest =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_arrays, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have checksLaw := collect_modifyCheckList checks f
      have elementsLaw := collect_modifyElements elements f
      have restLaw := collect_modifyRepresentationList rest f
      simp only [collectRepresentation, modifyRepresentation,
        collectAlgebra, modifyAlgebra, map_map_exact]
        at checksLaw elementsLaw restLaw
      rw [checksLaw, elementsLaw, restLaw]
  | objects annotations checks properties indexes =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_objects, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have checksLaw := collect_modifyCheckList checks f
      have propertiesLaw := collect_modifyProperties properties f
      have indexesLaw := collect_modifyIndexes indexes f
      simp only [collectRepresentation, modifyRepresentation,
        collectAlgebra, modifyAlgebra, map_map_exact]
        at checksLaw propertiesLaw indexesLaw
      rw [checksLaw, propertiesLaw, indexesLaw]
  | union annotations checks types mode =>
      simp only [collectRepresentation, modifyRepresentation,
        Representation.fold_union, collectAlgebra, modifyAlgebra,
        List.map_cons, map_map_exact, map_append_exact]
      have checksLaw := collect_modifyCheckList checks f
      have typesLaw := collect_modifyRepresentationList types f
      simp only [collectAlgebra, modifyAlgebra] at checksLaw typesLaw
      rw [checksLaw, typesLaw]
termination_by structural representation

private theorem collect_modifyCheck (check : Check)
    (f : Annotations → Annotations) :
    collectCheck (modifyCheck f check) = (collectCheck check).map f := by
  cases check with
  | filter representation annotations aborted =>
      simp only [collectCheck, modifyCheck, Check.fold_filter,
        collectAlgebra, modifyAlgebra, List.map_cons]
      have representationLaw := collect_modifyCheckAnnotation representation f
      simp only [collectAlgebra, modifyAlgebra] at representationLaw
      rw [representationLaw]
  | filterGroup representation annotations checks =>
      simp only [collectCheck, modifyCheck, Check.fold_filterGroup,
        collectAlgebra, modifyAlgebra, List.map_cons, map_map_exact,
        map_append_exact]
      have representationLaw :=
        collect_modifyCheckAnnotationOptional representation f
      have checksLaw := collect_modifyCheckList checks f
      simp only [collectAlgebra, modifyAlgebra] at representationLaw checksLaw
      rw [representationLaw, checksLaw]
termination_by structural check

private theorem collect_modifyRepresentationList
    (representations : List Representation) (f : Annotations → Annotations) :
    appendMany
        (representations.map
          (Representation.fold collectAlgebra ∘
            Representation.fold (modifyAlgebra f))) =
      (appendMany
        (representations.map (Representation.fold collectAlgebra))).map f := by
  cases representations with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons, appendMany, map_append_exact,
        Function.comp_apply]
      have headLaw := collect_modifyRepresentation head f
      simp only [collectRepresentation, modifyRepresentation] at headLaw
      rw [headLaw, collect_modifyRepresentationList tail f]
termination_by structural representations

private theorem collect_modifyCheckList (checks : List Check)
    (f : Annotations → Annotations) :
    appendMany
        (checks.map
          (Check.fold collectAlgebra ∘ Check.fold (modifyAlgebra f))) =
      (appendMany (checks.map (Check.fold collectAlgebra))).map f := by
  cases checks with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons, appendMany, map_append_exact,
        Function.comp_apply]
      have headLaw := collect_modifyCheck head f
      simp only [collectCheck, modifyCheck] at headLaw
      rw [headLaw, collect_modifyCheckList tail f]
termination_by structural checks

private theorem collect_modifyElements
    (elements : List (ElementOf Representation))
    (f : Annotations → Annotations) :
    elementBags
        ((elements.map fun element =>
          ElementOf.mk element.isOptional
            (modifyRepresentation f element.type) element.annotations).map
              (fun element => ElementOf.mk element.isOptional element.type
                (f element.annotations)) |>.map
            fun element =>
              ElementOf.mk element.isOptional
                (collectRepresentation element.type) element.annotations) =
      (elementBags
        (elements.map fun element =>
          ElementOf.mk element.isOptional
            (collectRepresentation element.type) element.annotations)).map f := by
  cases elements with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk isOptional type annotations =>
          simp only [List.map_cons, elementBags, map_append_exact]
          rw [collect_modifyRepresentation type f,
            collect_modifyElements tail f]
termination_by structural elements

private theorem collect_modifyProperties
    (properties : List (PropertySignatureOf Representation))
    (f : Annotations → Annotations) :
    propertyBags
        ((properties.map fun property =>
          PropertySignatureOf.mk property.name
            (modifyRepresentation f property.type) property.isOptional
            property.isMutable property.annotations).map
              (fun property => PropertySignatureOf.mk property.name property.type
                property.isOptional property.isMutable
                (f property.annotations)) |>.map
            fun property =>
              PropertySignatureOf.mk property.name
                (collectRepresentation property.type) property.isOptional
                property.isMutable property.annotations) =
      (propertyBags
        (properties.map fun property =>
          PropertySignatureOf.mk property.name
            (collectRepresentation property.type) property.isOptional
            property.isMutable property.annotations)).map f := by
  cases properties with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk name type isOptional isMutable annotations =>
          simp only [List.map_cons, propertyBags, map_append_exact]
          rw [collect_modifyRepresentation type f,
            collect_modifyProperties tail f]
termination_by structural properties

private theorem collect_modifyIndexes
    (indexes : List (IndexSignatureOf Representation))
    (f : Annotations → Annotations) :
    indexBags
        ((indexes.map fun index =>
          IndexSignatureOf.mk (modifyRepresentation f index.parameter)
            (modifyRepresentation f index.type)).map fun index =>
              IndexSignatureOf.mk (collectRepresentation index.parameter)
                (collectRepresentation index.type)) =
      (indexBags
        (indexes.map fun index =>
          IndexSignatureOf.mk (collectRepresentation index.parameter)
            (collectRepresentation index.type))).map f := by
  cases indexes with
  | nil => rfl
  | cons head tail =>
      cases head with
      | mk parameter type =>
          simp only [List.map_cons, indexBags, map_append_exact]
          rw [collect_modifyRepresentation parameter f,
            collect_modifyRepresentation type f,
            collect_modifyIndexes tail f]
termination_by structural indexes

private theorem collect_modifySchemas
    (schemas : Option (List Representation))
    (f : Annotations → Annotations) :
    (match schemas with
      | none => []
      | some values =>
          appendMany
            (values.map fun value =>
              collectRepresentation (modifyRepresentation f value))) =
      (match schemas with
        | none => []
        | some values =>
            appendMany (values.map collectRepresentation)).map f := by
  cases schemas with
  | none => rfl
  | some values => exact collect_modifyRepresentationList values f
private theorem collect_modifyCheckAnnotation
    (annotation : CheckRepresentationAnnotationOf Representation)
    (f : Annotations → Annotations) :
    checkSchemas
        { id := annotation.id
          payload := annotation.payload
          schemas := (annotation.schemas.map
            (List.map (Representation.fold (modifyAlgebra f)))).map
              (List.map (Representation.fold collectAlgebra)) } =
      (checkSchemas
        { id := annotation.id
          payload := annotation.payload
          schemas := annotation.schemas.map
            (List.map (Representation.fold collectAlgebra)) }).map f := by
  cases annotation with
  | mk name payload schemas =>
      simp only [checkSchemas]
      cases schemas with
      | none => rfl
      | some values =>
          simp only [Option.map, map_map_exact]
          exact collect_modifyRepresentationList values f
termination_by structural annotation

private theorem collect_modifyCheckAnnotationOptional
    (annotation : Option (CheckRepresentationAnnotationOf Representation))
    (f : Annotations → Annotations) :
    checkSchemasOptional
        ((annotation.map fun value =>
          CheckRepresentationAnnotationOf.mk value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold (modifyAlgebra f))))).map
                (fun value =>
                  CheckRepresentationAnnotationOf.mk value.id value.payload
                    (value.schemas.map
                      (List.map (Representation.fold collectAlgebra))))) =
      (checkSchemasOptional
        (annotation.map fun value =>
          CheckRepresentationAnnotationOf.mk value.id value.payload
            (value.schemas.map
              (List.map (Representation.fold collectAlgebra))))).map f := by
  cases annotation with
  | none => rfl
  | some value =>
      simp only [Option.map, checkSchemasOptional]
      exact collect_modifyCheckAnnotation value f
termination_by structural annotation

end

end AnnotationTraversal

/-- Every annotation bag in a representation payload, in structural preorder. -/
def Representation.annotationBags : Traversal Representation Annotations where
  collect := AnnotationTraversal.collectRepresentation
  modifyAll := AnnotationTraversal.modifyRepresentation

/-- Every annotation bag in a check payload, in structural preorder. -/
def Check.annotationBags : Traversal Check Annotations where
  collect := AnnotationTraversal.collectCheck
  modifyAll := AnnotationTraversal.modifyCheck

/-- The representation annotation traversal satisfies congruence, identity,
composition, and exact collection after modification. -/
theorem Representation.annotationBags_lawful :
    Traversal.Lawful Representation.annotationBags := by
  constructor
  · intro first second pointwise representation
    exact AnnotationTraversal.modifyRepresentation_congr pointwise representation
  · intro representation
    exact AnnotationTraversal.modifyRepresentation_id representation
  · intro representation first second
    exact AnnotationTraversal.modifyRepresentation_comp representation first second
  · intro representation f
    exact AnnotationTraversal.collect_modifyRepresentation representation f

/-- The check annotation traversal satisfies the same four pure traversal
equations, including schemas stored under both check constructors. -/
theorem Check.annotationBags_lawful : Traversal.Lawful Check.annotationBags := by
  constructor
  · intro first second pointwise check
    exact AnnotationTraversal.modifyCheck_congr pointwise check
  · intro check
    exact AnnotationTraversal.modifyCheck_id check
  · intro check first second
    exact AnnotationTraversal.modifyCheck_comp check first second
  · intro check f
    exact AnnotationTraversal.collect_modifyCheck check f

end Effect4
