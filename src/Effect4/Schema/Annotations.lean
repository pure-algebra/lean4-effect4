import Effect4.Data.Optic
import Effect4.Schema.Representation
import Effect4.Schema.Fold

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

private theorem modifyPayloadsAt_keys (name : String) (f : Json → Json)
    (entries : List AnnotationEntry) :
    (modifyPayloadsAt name f entries).map AnnotationEntry.key =
      entries.map AnnotationEntry.key := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk key payload =>
          by_cases same : key = name
          · subst key
            rw [modifyPayloadsAt_cons_same]
            change name :: (modifyPayloadsAt name f tail).map AnnotationEntry.key =
              name :: tail.map AnnotationEntry.key
            rw [ih]
          · rw [modifyPayloadsAt_cons_other name key payload tail f same]
            change key :: (modifyPayloadsAt name f tail).map AnnotationEntry.key =
              key :: tail.map AnnotationEntry.key
            rw [ih]

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

/-- Modification preserves the outer shape: an absent bag stays absent rather
than being created. -/
theorem payloadsAt_modifyAll_none (name : String) (f : Json → Json) :
    (payloadsAt name).modifyAll f none = none := rfl

/-- Modification preserves the outer shape: a present bag stays present. -/
theorem payloadsAt_modifyAll_some (name : String) (f : Json → Json)
    (entries : List AnnotationEntry) :
    ∃ modified, (payloadsAt name).modifyAll f (some entries) = some modified :=
  ⟨modifyPayloadsAt name f entries, rfl⟩

/-- Modification changes payloads only: every entry keeps its position and its
key, so the entry count, the stored order, the keys, and the multiplicity of
same-name entries all survive. The four traversal equations do not say this on
their own — a modifier that dropped every unrelated entry would still satisfy
`modify_id`, `modify_comp`, and `collect_modify`. -/
theorem payloadsAt_modifyAll_keys (name : String) (f : Json → Json)
    (entries modified : List AnnotationEntry)
    (edited : (payloadsAt name).modifyAll f (some entries) = some modified) :
    modified.map AnnotationEntry.key = entries.map AnnotationEntry.key := by
  have listEdited : modifyPayloadsAt name f entries = modified := by
    change some (modifyPayloadsAt name f entries) = some modified at edited
    exact Option.some.inj edited
  rw [← listEdited]
  exact modifyPayloadsAt_keys name f entries

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

/-- A lawful encoder is injective. `decode_encode` already names the inverse;
this is the separation it implies, and it is what lets a written payload stand
for its typed value rather than merely decode to one. -/
theorem Lawful.encode_injective {key : AnnotationKey A} (law : key.Lawful)
    {first second : A} (equal : key.encode first = key.encode second) :
    first = second := by
  have decoded : key.decode (key.encode first) = some second := by
    rw [equal]
    exact law.decode_encode second
  rw [law.decode_encode first] at decoded
  exact Option.some.inj decoded

/-- Reading every occurrence after a modification is that modification applied
to every occurrence read before it. Order and multiplicity are preserved
because `List.map` is. -/
theorem getAll_modifyAll (key : AnnotationKey A) (law : key.Lawful) (f : A → A)
    (annotations : Annotations) :
    key.getAll (key.modifyAll f annotations) = (key.getAll annotations).map f :=
  (key.values_lawful law).collect_modify annotations f

/-- Reading every occurrence after a total replacement yields the replacement
once per occurrence. The count of decoded occurrences does not change. -/
theorem getAll_replaceAll (key : AnnotationKey A) (law : key.Lawful) (value : A)
    (annotations : Annotations) :
    key.getAll (key.replaceAll value annotations) =
      (key.getAll annotations).map (fun _ => value) :=
  (key.values_lawful law).collect_modify annotations (fun _ => value)

/-- Replacing every occurrence with one value is idempotent. -/
theorem replaceAll_idempotent (key : AnnotationKey A) (law : key.Lawful) (value : A)
    (annotations : Annotations) :
    key.replaceAll value (key.replaceAll value annotations) =
      key.replaceAll value annotations :=
  (key.values_lawful law).modify_comp annotations (fun _ => value) (fun _ => value)

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

/-- Replacement is a no-op on `Reference`: the constructor carries no
annotation field, so there is nothing for the optic to write. -/
theorem nodeAnnotations_replace_reference (ref : ReferenceKey)
    (replacement : Annotations) :
    nodeAnnotations.replace replacement (.reference ref) = .reference ref := rfl

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

The two payload traversals below are algebras over the generated fold of the
carrier (`Effect4.Schema.Fold`, the `SchemaFold` group).  The collection algebra
returns the preorder list of bags.  The update algebra reconstructs the existing
carrier while applying one bag endomorphism at every annotation-bearing site.
The four traversal laws are proved from the generated identity and uniqueness
theorems, not by a case analysis over the twenty-four constructors.
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

/-- The preorder list of every annotation bag, as an algebra on the constant carrier. -/
private def collectAlgebra : RepresentationAlgebra (fun _ => List Annotations) where
  representation_declaration _ annotations parameters checks :=
    annotations :: (appendMany parameters ++ appendMany checks)
  representation_reference _ := []
  representation_suspend annotations checks thunk :=
    annotations :: (appendMany checks ++ thunk)
  representation_null annotations checks := annotations :: appendMany checks
  representation_undefined annotations checks := annotations :: appendMany checks
  representation_void annotations checks := annotations :: appendMany checks
  representation_never annotations checks := annotations :: appendMany checks
  representation_unknown annotations checks := annotations :: appendMany checks
  representation_any annotations checks := annotations :: appendMany checks
  representation_string annotations checks := annotations :: appendMany checks
  representation_number annotations checks := annotations :: appendMany checks
  representation_boolean annotations checks := annotations :: appendMany checks
  representation_bigint annotations checks := annotations :: appendMany checks
  representation_symbol annotations checks := annotations :: appendMany checks
  representation_literal annotations checks _ := annotations :: appendMany checks
  representation_uniqueSymbol annotations checks _ := annotations :: appendMany checks
  representation_objectKeyword annotations checks := annotations :: appendMany checks
  representation_enum annotations checks _ := annotations :: appendMany checks
  representation_templateLiteral annotations checks parts :=
    annotations :: (appendMany checks ++ appendMany parts)
  representation_arrays annotations checks elements rest :=
    annotations :: (appendMany checks ++ elementBags elements ++ appendMany rest)
  representation_objects annotations checks properties indexes :=
    annotations :: (appendMany checks ++ propertyBags properties ++ indexBags indexes)
  representation_union annotations checks types _ :=
    annotations :: (appendMany checks ++ appendMany types)
  check_filter representation annotations _ :=
    annotations :: checkSchemas representation
  check_filterGroup representation annotations checks :=
    annotations :: (checkSchemasOptional representation ++ appendMany checks)


/-- The rebuild algebra with one endomorphism at every annotation-bearing site: the node's
own bag, and the bags the tuple elements and the object properties carry. -/
private def modifyAlgebra (f : Annotations → Annotations) :
    RepresentationAlgebra RepresentationSelfCarrier where
  representation_declaration representation annotations parameters checks :=
    .declaration representation (f annotations) parameters checks
  representation_reference := .reference
  representation_suspend annotations checks thunk := .suspend (f annotations) checks thunk
  representation_null annotations checks := .null (f annotations) checks
  representation_undefined annotations checks := .undefined (f annotations) checks
  representation_void annotations checks := .void (f annotations) checks
  representation_never annotations checks := .never (f annotations) checks
  representation_unknown annotations checks := .unknown (f annotations) checks
  representation_any annotations checks := .any (f annotations) checks
  representation_string annotations checks := .string (f annotations) checks
  representation_number annotations checks := .number (f annotations) checks
  representation_boolean annotations checks := .boolean (f annotations) checks
  representation_bigint annotations checks := .bigint (f annotations) checks
  representation_symbol annotations checks := .symbol (f annotations) checks
  representation_literal annotations checks value := .literal (f annotations) checks value
  representation_uniqueSymbol annotations checks key := .uniqueSymbol (f annotations) checks key
  representation_objectKeyword annotations checks := .objectKeyword (f annotations) checks
  representation_enum annotations checks entries := .enum (f annotations) checks entries
  representation_templateLiteral annotations checks parts :=
    .templateLiteral (f annotations) checks parts
  representation_arrays annotations checks elements rest :=
    .arrays (f annotations) checks
      (elements.map fun element => { element with annotations := f element.annotations })
      rest
  representation_objects annotations checks properties indexes :=
    .objects (f annotations) checks
      (properties.map fun property =>
        { property with annotations := f property.annotations })
      indexes
  representation_union annotations checks types mode := .union (f annotations) checks types mode
  check_filter representation annotations aborted :=
    .filter representation (f annotations) aborted
  check_filterGroup representation annotations checks :=
    .filterGroup representation (f annotations) checks



/-- The collection again, with one endomorphism applied to every bag it emits. Both
`collectRepresentation` after `modifyRepresentation f` and `List.map f` after
`collectRepresentation` are homomorphisms of this one algebra, which is how the fourth
traversal law is proved below. -/
private def collectMappedAlgebra (f : Annotations → Annotations) :
    RepresentationAlgebra (fun _ => List Annotations) where
  representation_declaration _ annotations parameters checks :=
    f annotations :: (appendMany parameters ++ appendMany checks)
  representation_reference _ := []
  representation_suspend annotations checks thunk :=
    f annotations :: (appendMany checks ++ thunk)
  representation_null annotations checks := f annotations :: appendMany checks
  representation_undefined annotations checks := f annotations :: appendMany checks
  representation_void annotations checks := f annotations :: appendMany checks
  representation_never annotations checks := f annotations :: appendMany checks
  representation_unknown annotations checks := f annotations :: appendMany checks
  representation_any annotations checks := f annotations :: appendMany checks
  representation_string annotations checks := f annotations :: appendMany checks
  representation_number annotations checks := f annotations :: appendMany checks
  representation_boolean annotations checks := f annotations :: appendMany checks
  representation_bigint annotations checks := f annotations :: appendMany checks
  representation_symbol annotations checks := f annotations :: appendMany checks
  representation_literal annotations checks _ := f annotations :: appendMany checks
  representation_uniqueSymbol annotations checks _ := f annotations :: appendMany checks
  representation_objectKeyword annotations checks := f annotations :: appendMany checks
  representation_enum annotations checks _ := f annotations :: appendMany checks
  representation_templateLiteral annotations checks parts :=
    f annotations :: (appendMany checks ++ appendMany parts)
  representation_arrays annotations checks elements rest :=
    f annotations :: (appendMany checks ++ elementBags (elements.map fun element =>
      { element with annotations := f element.annotations }) ++ appendMany rest)
  representation_objects annotations checks properties indexes :=
    f annotations :: (appendMany checks ++ propertyBags (properties.map fun property =>
      { property with annotations := f property.annotations }) ++ indexBags indexes)
  representation_union annotations checks types _ :=
    f annotations :: (appendMany checks ++ appendMany types)
  check_filter representation annotations _ :=
    f annotations :: checkSchemas representation
  check_filterGroup representation annotations checks :=
    f annotations :: (checkSchemasOptional representation ++ appendMany checks)



private def collectRepresentation (representation : Representation) : List Annotations :=
  cata_representation collectAlgebra representation

private def collectCheck (check : Check) : List Annotations :=
  cata_check collectAlgebra check

private def modifyRepresentation (f : Annotations → Annotations)
    (representation : Representation) : Representation :=
  cata_representation (modifyAlgebra f) representation

private def modifyCheck (f : Annotations → Annotations) (check : Check) : Check :=
  cata_check (modifyAlgebra f) check

/-! ### The bags under a map

`appendMany`, `elementBags`, `propertyBags`, `indexBags` and the two check-annotation
readers each commute with `List.map` over the collected bags. Every one is stated in the
direction the traversal proofs rewrite: the map moves inside. -/

private theorem appendMany_map (f : Annotations → Annotations)
    (bags : List (List Annotations)) :
    (appendMany bags).map f = appendMany (bags.map (List.map f)) := by
  induction bags with
  | nil => rfl
  | cons head tail ih => simp only [appendMany, List.map_cons, map_append_exact, ih]

private theorem elementBags_map (f : Annotations → Annotations)
    (elements : List (ElementOf (List Annotations))) :
    (elementBags elements).map f =
      elementBags (elements.map fun element =>
        { element with type := element.type.map f, annotations := f element.annotations }) := by
  induction elements with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, elementBags, map_append_exact, ih]

private theorem propertyBags_map (f : Annotations → Annotations)
    (properties : List (PropertySignatureOf (List Annotations))) :
    (propertyBags properties).map f =
      propertyBags (properties.map fun property =>
        { property with
          type := property.type.map f
          annotations := f property.annotations }) := by
  induction properties with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, propertyBags, map_append_exact, ih]

private theorem indexBags_map (f : Annotations → Annotations)
    (indexes : List (IndexSignatureOf (List Annotations))) :
    (indexBags indexes).map f =
      indexBags (indexes.map (IndexSignatureOf.map (List.map f))) := by
  induction indexes with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, indexBags, IndexSignatureOf.map, map_append_exact, ih]

private theorem checkSchemas_map (f : Annotations → Annotations)
    (annotation : CheckRepresentationAnnotationOf (List Annotations)) :
    (checkSchemas annotation).map f =
      checkSchemas (CheckRepresentationAnnotationOf.map (List.map f) annotation) := by
  cases annotation with
  | mk name payload schemas =>
    cases schemas with
    | none => rfl
    | some values => simp only [checkSchemas, CheckRepresentationAnnotationOf.map,
        Option.map_some, appendMany_map]

private theorem checkSchemasOptional_map (f : Annotations → Annotations)
    (annotation : Option (CheckRepresentationAnnotationOf (List Annotations))) :
    (checkSchemasOptional annotation).map f =
      checkSchemasOptional
        (annotation.map (CheckRepresentationAnnotationOf.map (List.map f))) := by
  cases annotation with
  | none => rfl
  | some value => simp only [Option.map_some, checkSchemasOptional, checkSchemas_map]

/-! ### Law 1: the identity

`modifyAlgebra id` *is* the generated identity algebra -- the annotation endomorphism is the
only thing it changes, and `List.map_id'` retires the two record maps -- so the law is the
generated `cata_id_*` and no case analysis at all. -/

private theorem modifyAlgebra_id : modifyAlgebra id = RepresentationAlgebra.id := by
  unfold modifyAlgebra RepresentationAlgebra.id
  simp only [id_eq, List.map_id']

private theorem modifyRepresentation_id (representation : Representation) :
    modifyRepresentation id representation = representation := by
  rw [modifyRepresentation, modifyAlgebra_id, cata_id_representation]

private theorem modifyCheck_id (check : Check) : modifyCheck id check = check := by
  rw [modifyCheck, modifyAlgebra_id, cata_id_check]

/-! ### Law 2: congruence

Two pointwise equal endomorphisms build the same algebra, so they fold to the same tree. -/

private theorem modifyRepresentation_congr {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations)
    (representation : Representation) :
    modifyRepresentation first representation =
      modifyRepresentation second representation := by
  rw [modifyRepresentation, modifyRepresentation, funext pointwise]

private theorem modifyCheck_congr {first second : Annotations → Annotations}
    (pointwise : ∀ annotations, first annotations = second annotations) (check : Check) :
    modifyCheck first check = modifyCheck second check := by
  rw [modifyCheck, modifyCheck, funext pointwise]

/-! ### Law 3: composition

The two folds composed satisfy the composite algebra's constructor equations, and the
generated uniqueness theorem says the fold is the only family that does. No induction over
the twenty-four constructors is written here: each equation is one rewrite. -/

private def compHom (first second : Annotations → Annotations) :
    RepresentationHom (modifyAlgebra (second ∘ first)) where
  f_representation := fun representation =>
    modifyRepresentation second (modifyRepresentation first representation)
  f_check := fun check => modifyCheck second (modifyCheck first check)
  h_representation_declaration := by
    intro a0 a1 a2 a3
    simp only [modifyRepresentation, modifyCheck, cata_representation_declaration,
      modifyAlgebra, List.map_map, Function.comp_def]
  h_representation_reference := by
    intro a0
    simp only [modifyRepresentation, cata_representation_reference, modifyAlgebra,
      Function.comp_def]
  h_representation_suspend := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_representation_suspend, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_null := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_null, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_undefined := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_undefined, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_void := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_void, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_never := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_never, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_unknown := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_unknown, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_any := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_any, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_string := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_string, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_number := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_number, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_boolean := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_boolean, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_bigint := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_bigint, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_symbol := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_symbol, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_literal := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_representation_literal, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_uniqueSymbol := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_representation_uniqueSymbol,
      modifyAlgebra, List.map_map, Function.comp_def]
  h_representation_objectKeyword := by
    intro a0 a1
    simp only [modifyRepresentation, modifyCheck, cata_representation_objectKeyword,
      modifyAlgebra, List.map_map, Function.comp_def]
  h_representation_enum := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_representation_enum, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_templateLiteral := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_representation_templateLiteral,
      modifyAlgebra, List.map_map, Function.comp_def]
  h_representation_arrays := by
    intro a0 a1 a2 a3
    simp only [modifyRepresentation, modifyCheck, cata_representation_arrays, modifyAlgebra,
      ElementOf.map, List.map_map, Function.comp_def]
  h_representation_objects := by
    intro a0 a1 a2 a3
    simp only [modifyRepresentation, modifyCheck, cata_representation_objects, modifyAlgebra,
      PropertySignatureOf.map, IndexSignatureOf.map_map, List.map_map, Function.comp_def]
  h_representation_union := by
    intro a0 a1 a2 a3
    simp only [modifyRepresentation, modifyCheck, cata_representation_union, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_check_filter := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_check_filter, modifyAlgebra,
      CheckRepresentationAnnotationOf.map, List.map_map, Option.map_map, Function.comp_def]
  h_check_filterGroup := by
    intro a0 a1 a2
    simp only [modifyRepresentation, modifyCheck, cata_check_filterGroup, modifyAlgebra,
      CheckRepresentationAnnotationOf.map_map, Option.map_map, List.map_map, Function.comp_def]

private theorem modifyRepresentation_comp (representation : Representation)
    (first second : Annotations → Annotations) :
    modifyRepresentation second (modifyRepresentation first representation) =
      modifyRepresentation (second ∘ first) representation := by
  exact hom_eq_cata_representation (compHom first second) representation

private theorem modifyCheck_comp (check : Check)
    (first second : Annotations → Annotations) :
    modifyCheck second (modifyCheck first check) = modifyCheck (second ∘ first) check := by
  exact hom_eq_cata_check (compHom first second) check

/-! ### Law 4: collection after modification

Collecting after modifying, and mapping after collecting, are two homomorphisms of the one
algebra `collectMappedAlgebra`; uniqueness identifies them. -/

private def collectAfterModify (f : Annotations → Annotations) :
    RepresentationHom (collectMappedAlgebra f) where
  f_representation := fun representation =>
    collectRepresentation (modifyRepresentation f representation)
  f_check := fun check => collectCheck (modifyCheck f check)
  h_representation_declaration := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_declaration, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_reference := by
    intro a0
    simp only [collectRepresentation, modifyRepresentation, cata_representation_reference,
      collectAlgebra, collectMappedAlgebra, modifyAlgebra]
  h_representation_suspend := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_suspend, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_null := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_null, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_undefined := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_undefined, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_void := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_void, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_never := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_never, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_unknown := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_unknown, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_any := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_any, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_string := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_string, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_number := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_number, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_boolean := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_boolean, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_bigint := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_bigint, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_symbol := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_symbol, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_literal := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_literal, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_uniqueSymbol := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_uniqueSymbol, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_objectKeyword := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_objectKeyword, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_enum := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_enum, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_templateLiteral := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_templateLiteral, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_representation_arrays := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_arrays, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, ElementOf.map, Function.comp_def]
  h_representation_objects := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_objects, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, PropertySignatureOf.map, IndexSignatureOf.map_map, Function.comp_def]
  h_representation_union := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_representation_union, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Function.comp_def]
  h_check_filter := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_check_filter, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      CheckRepresentationAnnotationOf.map_map]
  h_check_filterGroup := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, modifyRepresentation, modifyCheck,
      cata_check_filterGroup, collectAlgebra, collectMappedAlgebra, modifyAlgebra,
      List.map_map, Option.map_map, CheckRepresentationAnnotationOf.map_map, Function.comp_def]

private def mapAfterCollect (f : Annotations → Annotations) :
    RepresentationHom (collectMappedAlgebra f) where
  f_representation := fun representation => (collectRepresentation representation).map f
  f_check := fun check => (collectCheck check).map f
  h_representation_declaration := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, cata_representation_declaration,
      collectAlgebra, collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map,
      List.map_map, Function.comp_def]
  h_representation_reference := by
    intro a0
    simp only [collectRepresentation, cata_representation_reference, collectAlgebra,
      collectMappedAlgebra, List.map_nil]
  h_representation_suspend := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_representation_suspend,
      collectAlgebra, collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map,
      List.map_map, Function.comp_def]
  h_representation_null := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_null, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_undefined := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_undefined,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_void := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_void, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_never := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_never, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_unknown := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_unknown,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_any := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_any, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_string := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_string, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_number := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_number, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_boolean := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_boolean,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_bigint := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_bigint, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_symbol := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_symbol, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_literal := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_representation_literal,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_uniqueSymbol := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_representation_uniqueSymbol,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_objectKeyword := by
    intro a0 a1
    simp only [collectRepresentation, collectCheck, cata_representation_objectKeyword,
      collectAlgebra, collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map,
      Function.comp_def]
  h_representation_enum := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_representation_enum, collectAlgebra,
      collectMappedAlgebra, List.map_cons, appendMany_map, List.map_map, Function.comp_def]
  h_representation_templateLiteral := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_representation_templateLiteral,
      collectAlgebra, collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map,
      List.map_map, Function.comp_def]
  h_representation_arrays := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, cata_representation_arrays, collectAlgebra,
      collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map, elementBags_map,
      List.map_map, ElementOf.map, Function.comp_def]
  h_representation_objects := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, cata_representation_objects,
      collectAlgebra, collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map,
      propertyBags_map, indexBags_map, List.map_map, PropertySignatureOf.map,
      IndexSignatureOf.map_map, Function.comp_def]
  h_representation_union := by
    intro a0 a1 a2 a3
    simp only [collectRepresentation, collectCheck, cata_representation_union, collectAlgebra,
      collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map, List.map_map,
      Function.comp_def]
  h_check_filter := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_check_filter, collectAlgebra,
      collectMappedAlgebra, List.map_cons, checkSchemas_map,
      CheckRepresentationAnnotationOf.map_map]
  h_check_filterGroup := by
    intro a0 a1 a2
    simp only [collectRepresentation, collectCheck, cata_check_filterGroup, collectAlgebra,
      collectMappedAlgebra, List.map_cons, map_append_exact, appendMany_map,
      checkSchemasOptional_map, List.map_map, Option.map_map,
      CheckRepresentationAnnotationOf.map_map, Function.comp_def]


private theorem collect_modifyRepresentation (representation : Representation)
    (f : Annotations → Annotations) :
    collectRepresentation (modifyRepresentation f representation) =
      (collectRepresentation representation).map f := by
  exact (hom_eq_cata_representation (collectAfterModify f) representation).trans
    (hom_eq_cata_representation (mapAfterCollect f) representation).symm

private theorem collect_modifyCheck (check : Check) (f : Annotations → Annotations) :
    collectCheck (modifyCheck f check) = (collectCheck check).map f := by
  exact (hom_eq_cata_check (collectAfterModify f) check).trans
    (hom_eq_cata_check (mapAfterCollect f) check).symm

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
