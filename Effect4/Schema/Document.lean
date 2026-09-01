import Effect4.Schema.Annotations

/-!
# Schema.Document.lean

Owner: Named declarations, references, and guarded documents.

This module now declares the two document **containers** of
`test/contracts/schema-payload.contract.md` D6 and nothing else. Every
semantic object it is assigned below — the reference graph, guardedness,
productivity, the memoized checker — is still unopened, and its public surface
is frozen only after the owning contract and counterexample packet.

No reference edge is interpreted here. `ReferenceEntry.key` is an opaque
string, `$ref` is not resolved against it, and no theorem below is worded as a
termination, reachability, or dead-entry result.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

One root representation plus a keyed references table (`Document`), and a
non-empty ordered root list over the same kind of table (`MultiDocument`).
The reference graph, guardedness of recursive references, and the memoized
checker are this module's.

## Assigned future semantic obligations

The passive D6 containers and `Document.toMulti` receipts are implemented
below. They do not discharge the later graph-bearing reference semantics:

- `SC-DOC-01` reference graph
- `SC-DOC-02` guarded checker soundness
- `SC-DOC-03` guarded checker completeness
- `SC-DOC-04` memoized checker equivalence
- `SC-DOC-05` retained complexity counterexample

## Retains

- `E4-SCHEMA-CE-013` bare self-reference cycle
- `E4-SCHEMA-CE-014` guarded recursive reference
- `E4-SCHEMA-CE-015` bounded naive-versus-memoized fan-graph cost witness
- `E4-SCHEMA-CE-012` duplicate key becomes invisible after map parsing

`E4-SCHEMA-CE-015` currently retains a reported naive measurement of `302915`
milliseconds on one 25-entry fan table, plus separate executable memo and
small-input agreement guards. It is neither a same-input benchmark comparison
nor an asymptotic lower bound. A later complexity theorem must state its cost
model and prove the claimed family-wide growth before using “exponential.”
The memoized checker must still be proved to agree with the reference checker,
not merely to pass a separate guard.

Also `SC-DOC-06` productivity is not guardedness, and `SC-DOC-07` canonical
emission order for unions. Both are newly named and both are open.

`SC-DOC-06` is the one to keep in view while designing. A guarded document may
still have no value, because `Suspend` is a delay and not a constructor: a
recursive occurrence under one is deferred, not broken. Vendored commentary
records three documents said to pass guardedness while Effect's validator
diverges or overflows
(`vendor/foldlab/pinned/tree/library/cas/Cas/Schema/Guarded.lean:29-50`), but
this checkout does not yet contain their executable witness. Treat the claim
as a counterexample obligation, not established evidence. Neither this module
nor `Schema/Value.lean` may word `SC-DEN-07` or `SC-DEN-08` as a termination
result until productivity has its own relation and executable evidence.

## Gated by

The payload carrier. Duplicate JSON keys are rejected before either table is
constructed, so the raw-JSON layer must exist first.

## Prior art

The vendored Foldlab tree is rich here and is `evidenceOnly`; reuse the proof
shapes, never the carrier. Verified spans, all under
`vendor/foldlab/pinned/tree/library/cas/`:

- `Cas/Schema/Guarded.lean:191-193` — the naive checker used by the bounded
  cost witness; the asymptotic theorem remains open;
- `Cas/Schema/Guarded.lean:449-462` — the memoised checker. Two properties do
  the work: the memo is fuel-free, and a name enters it only on the way back
  out, so a cycle never enters the memo;
- `Cas/Schema/Guarded.lean:708-722` — memo/naive agreement, which is
  `SC-DOC-04` verbatim;
- `Cas/Schema/Guarded.lean:724-748` — a prose report of `302915` milliseconds
  for the naive checker at 25 entries, followed by separate memo and
  eight-entry agreement guards; no same-input benchmark theorem or asymptotic
  result;
- `Cas/Schema/Ingest.lean:871-891` — the guarded control and the two cycle
  witnesses for `E4-SCHEMA-CE-013` and `E4-SCHEMA-CE-014`.

Note that Foldlab's `Document` is single-root. `MultiDocument` has no prior
art here at all.
-/

namespace Effect4

/--
One entry of a document's references table.

The table is an ordered `List`, not a map. Duplicate raw keys remain
representable here so the future wire-profile judgment can inspect them before
any table is collapsed to a map (`E4-SCHEMA-CE-012`). Reference-key uniqueness
for both document forms is deliberately deferred to `Effect4.Protocol.Bytes`;
this packet declares no `ReferenceKeysUnique` predicate.

A table key is plain `Schema.String` (`SchemaRepresentation.ts:1096`) while
`Reference.$ref` is `Schema.NonEmptyString` (`:1068`), so an entry filed under
the empty key cannot be named by a **field-admissible** reference. The raw
carrier can still spell `.reference ⟨""⟩`, allowing admission to reject it.
`E4-SCHEMA-CE-030`.
-/
structure ReferenceEntry where
  /-- The persisted table key. -/
  key : String
  /-- The representation filed under that key. -/
  representation : Representation
deriving DecidableEq

/--
A single-root persisted document.

Pin: `SchemaRepresentation.ts:480-483`, codec `:1098-1103`.
-/
structure Document where
  /-- The document root. -/
  representation : Representation
  /-- The ordered references table. -/
  references : List ReferenceEntry
deriving DecidableEq

/--
A multi-root persisted document.

Pin: `SchemaRepresentation.ts:491-494`, codec `:1105-1110`. The root field is
`representations`, plural, and its non-emptiness is `Schema.NonEmptyArray`
(`:1107`) — a field-admission clause, not a carrier invariant.
-/
structure MultiDocument where
  /-- The ordered document roots. -/
  representations : List Representation
  /-- The ordered references table. -/
  references : List ReferenceEntry
deriving DecidableEq

/--
Read a single-root document as a multi-root one.

The two shapes are not distinguished by a tag at the pin, and they stay
nominally distinct here: this embedding is injective and not surjective, so
`MultiDocument` is strictly the wider container. `E4-SCHEMA-CE-038`.
-/
def Document.toMulti (document : Document) : MultiDocument :=
  { representations := [document.representation]
    references := document.references }

/-- The embedding, per constructor. -/
theorem Document.toMulti_mk (root : Representation)
    (references : List ReferenceEntry) :
    Document.toMulti (Document.mk root references) =
      MultiDocument.mk [root] references := rfl

/-- The single-root embedding loses nothing. -/
theorem Document.toMulti_injective (first second : Document)
    (equal : Document.toMulti first = Document.toMulti second) : first = second := by
  obtain ⟨root₁, references₁⟩ := first
  obtain ⟨root₂, references₂⟩ := second
  simp only [Document.toMulti, MultiDocument.mk.injEq, List.cons.injEq,
    and_true] at equal
  obtain ⟨rootEqual, referencesEqual⟩ := equal
  subst rootEqual
  subst referencesEqual
  rfl

/--
The single-root embedding does not reach every multi-root document.

The witness carries **two** roots rather than none. An empty-root witness would
conflate this nominal one-root/many-root distinction with the separate
non-empty-root admission clause of `Effect4/Schema/Check.lean`, and
`MultiDocument.fieldAdmissible_two_roots` records that this witness is itself
field-admissible.
-/
theorem Document.toMulti_two_roots_not_image (document : Document) :
    Document.toMulti document ≠
      MultiDocument.mk
        [Representation.never none [], Representation.string none []] [] := by
  intro equal
  injection equal with rootsEqual _
  injection rootsEqual with _ tailEqual
  exact absurd tailEqual (by simp)

/-! ## Structural annotation data plane

These traversals are deliberately acyclic: they visit the stored document
containers and delegate each representation subtree to
`Representation.annotationBags`.  Reference keys are never resolved, so dead
and duplicate entries remain visible in their original order.
-/

private def collectReferenceRepresentations : List ReferenceEntry →
    List Representation
  | [] => []
  | entry :: tail => entry.representation :: collectReferenceRepresentations tail

private def modifyReferenceRepresentations (f : Representation → Representation) :
    List ReferenceEntry → List ReferenceEntry
  | [] => []
  | entry :: tail =>
      { entry with representation := f entry.representation } ::
        modifyReferenceRepresentations f tail

private theorem modifyReferenceRepresentations_congr
    {first second : Representation → Representation}
    (pointwise : ∀ value, first value = second value)
    (references : List ReferenceEntry) :
    modifyReferenceRepresentations first references =
      modifyReferenceRepresentations second references := by
  induction references with
  | nil => rfl
  | cons entry tail ih =>
      cases entry
      simp only [modifyReferenceRepresentations]
      rw [pointwise, ih]

private theorem modifyReferenceRepresentations_id
    (references : List ReferenceEntry) :
    modifyReferenceRepresentations id references = references := by
  induction references with
  | nil => rfl
  | cons entry tail ih =>
      cases entry
      simp only [modifyReferenceRepresentations, id_eq]
      rw [ih]

private theorem modifyReferenceRepresentations_comp
    (references : List ReferenceEntry)
    (first second : Representation → Representation) :
    modifyReferenceRepresentations second
        (modifyReferenceRepresentations first references) =
      modifyReferenceRepresentations (second ∘ first) references := by
  induction references with
  | nil => rfl
  | cons entry tail ih =>
      cases entry
      simp only [modifyReferenceRepresentations, Function.comp_apply]
      rw [ih]

private theorem collectReferenceRepresentations_modify
    (references : List ReferenceEntry) (f : Representation → Representation) :
    collectReferenceRepresentations (modifyReferenceRepresentations f references) =
      (collectReferenceRepresentations references).map f := by
  induction references with
  | nil => rfl
  | cons entry tail ih =>
      cases entry
      simp only [modifyReferenceRepresentations, collectReferenceRepresentations,
        List.map_cons]
      rw [ih]

private theorem map_congr_exact {A B : Type} {first second : A → B}
    (pointwise : ∀ value, first value = second value) (values : List A) :
    values.map first = values.map second := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [pointwise, ih]

private theorem map_id_exact {A : Type} (values : List A) :
    values.map id = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, id_eq]
      rw [ih]

private theorem map_comp_exact {A : Type} (values : List A)
    (first second : A → A) :
    (values.map first).map second = values.map (second ∘ first) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, Function.comp_apply]
      rw [ih]

private theorem map_append_exact {A B : Type} (f : A → B)
    (first second : List A) :
    (first ++ second).map f = first.map f ++ second.map f := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, List.map_cons]
      rw [ih]

namespace Document

/-- The root followed by every stored reference representation, without
resolving reference keys. -/
private def representationSites : Traversal Document Representation where
  collect document :=
    document.representation :: collectReferenceRepresentations document.references
  modifyAll f document :=
    { representation := f document.representation
      references := modifyReferenceRepresentations f document.references }

private theorem representationSites_lawful :
    Traversal.Lawful representationSites := by
  constructor
  · intro first second pointwise document
    cases document with
    | mk root references =>
        change Document.mk (first root)
            (modifyReferenceRepresentations first references) =
          Document.mk (second root)
            (modifyReferenceRepresentations second references)
        rw [pointwise, modifyReferenceRepresentations_congr pointwise]
  · intro document
    cases document with
    | mk root references =>
        change Document.mk (id root)
            (modifyReferenceRepresentations id references) =
          Document.mk root references
        rw [modifyReferenceRepresentations_id]
        rfl
  · intro document first second
    cases document with
    | mk root references =>
        change Document.mk (second (first root))
            (modifyReferenceRepresentations second
              (modifyReferenceRepresentations first references)) =
          Document.mk ((second ∘ first) root)
            (modifyReferenceRepresentations (second ∘ first) references)
        rw [modifyReferenceRepresentations_comp]
        rfl
  · intro document f
    cases document with
    | mk root references =>
        change f root :: collectReferenceRepresentations
            (modifyReferenceRepresentations f references) =
          (root :: collectReferenceRepresentations references).map f
        rw [collectReferenceRepresentations_modify]
        rfl

/-- Every annotation bag in the root and every stored reference entry, in
structural preorder. -/
def annotationBags : Traversal Document Annotations :=
  representationSites.compose Representation.annotationBags

/-- The document annotation data-plane traversal satisfies the four pure
traversal equations. -/
theorem annotationBags_lawful : Traversal.Lawful annotationBags := by
  exact Traversal.Lawful.compose representationSites_lawful
    Representation.annotationBags_lawful

end Document

namespace MultiDocument

/-- Every root followed by every stored reference representation, preserving
both source orders and without resolving reference keys. -/
private def representationSites : Traversal MultiDocument Representation where
  collect document :=
    document.representations ++
      collectReferenceRepresentations document.references
  modifyAll f document :=
    { representations := document.representations.map f
      references := modifyReferenceRepresentations f document.references }

private theorem representationSites_lawful :
    Traversal.Lawful representationSites := by
  constructor
  · intro first second pointwise document
    cases document with
    | mk roots references =>
        change MultiDocument.mk (roots.map first)
            (modifyReferenceRepresentations first references) =
          MultiDocument.mk (roots.map second)
            (modifyReferenceRepresentations second references)
        rw [map_congr_exact pointwise,
          modifyReferenceRepresentations_congr pointwise]
  · intro document
    cases document with
    | mk roots references =>
        change MultiDocument.mk (roots.map id)
            (modifyReferenceRepresentations id references) =
          MultiDocument.mk roots references
        rw [map_id_exact, modifyReferenceRepresentations_id]
  · intro document first second
    cases document with
    | mk roots references =>
        change MultiDocument.mk ((roots.map first).map second)
            (modifyReferenceRepresentations second
              (modifyReferenceRepresentations first references)) =
          MultiDocument.mk (roots.map (second ∘ first))
            (modifyReferenceRepresentations (second ∘ first) references)
        rw [map_comp_exact, modifyReferenceRepresentations_comp]
  · intro document f
    cases document with
    | mk roots references =>
        change roots.map f ++ collectReferenceRepresentations
            (modifyReferenceRepresentations f references) =
          (roots ++ collectReferenceRepresentations references).map f
        rw [collectReferenceRepresentations_modify, map_append_exact]

/-- Every annotation bag in every root and stored reference entry, in
structural preorder. -/
def annotationBags : Traversal MultiDocument Annotations :=
  representationSites.compose Representation.annotationBags

/-- The multi-root annotation data-plane traversal satisfies the four pure
traversal equations. -/
theorem annotationBags_lawful : Traversal.Lawful annotationBags := by
  exact Traversal.Lawful.compose representationSites_lawful
    Representation.annotationBags_lawful

end MultiDocument

end Effect4
