# Schema annotation data-plane and optic contract

Status: **Pass-B FROZEN; implementation REQUIRED-BLOCKED**. The production
fences are `Effect4/Data/Optic.lean`, `Effect4/Schema/Annotations.lean`, and an
additive document-traversal section in `Effect4/Schema/Document.lean`.
The breaker-owned batteries are `Effect4Test/Data/OpticContract.lean` and
`Effect4Test/Schema/AnnotationDataPlaneContract.lean`; the retained attacks
are in `Effect4Test/Counterexamples/Schema/AnnotationDataPlane.lean`.

This packet exposes the existing annotation data as composable views. It does
not add a second Schema carrier, resolve document references, assign
denotational meaning to annotations, or introduce a `Describes`/`Described`
class. Typed annotation keys are codecs for one dimension of the existing
`Json` payload, not schemas for a new data universe.

## Existing-type disposition

The data plane reuses, without wrapping or copying:

- `AnnotationEntry` and `Annotations` as the raw ordered bag;
- `Representation` and `Check` as the mutually recursive payload;
- `ElementOf` and `PropertySignatureOf` as annotation-bearing child records;
- `Document`, `MultiDocument`, and every `ReferenceEntry`; and
- the closed `Representation.fold`/`Check.fold` recursion edge.

Module ownership is acyclic and frozen. `Data/Optic` owns the three generic
carriers and laws. `Schema/Annotations` imports `Schema/Representation` and
owns typed keys, raw/local optics, and the `Representation`/`Check` recursive
traversals. `Schema/Document` imports `Schema/Annotations` and owns only the
`Document`/`MultiDocument` traversal definitions and laws. Thus a consumer of
`Schema/Document` sees the whole surface, while `Schema/Annotations` never
imports its downstream document container.

Three small generic optic carriers are admitted in `Effect4.Data`: `Lens` for
one total focus, `Optional` for zero or one focus, and `Traversal` for an
ordered finite list of foci. They are reusable function records, not Schema
data. `AnnotationKey A` is the sole Schema-specific new carrier. It contains a
raw string key and a two-way codec between `A` and the existing `Json` leaf.

Forbidden alternatives are a second annotation bag, a map-backed bag, a
second Schema/JSON carrier, a dependent or monadic optic hierarchy, a
profunctor encoding, and reference-resolving traversal.

## Generic optic surface

All four type parameters below are universe-polymorphic.

```lean
structure Effect4.Lens (S : Type u) (A : Type v) where
  get : S -> A
  replace : A -> S -> S

Effect4.Lens.modify : Lens S A -> (A -> A) -> S -> S
Effect4.Lens.compose : Lens S A -> Lens A B -> Lens S B
Effect4.Lens.toOptional : Lens S A -> Optional S A

structure Effect4.Lens.Lawful (optic : Lens S A) : Prop where
  get_replace : forall source value,
    optic.get (optic.replace value source) = value
  replace_get : forall source,
    optic.replace (optic.get source) source = source
  replace_replace : forall source first second,
    optic.replace second (optic.replace first source) =
      optic.replace second source

structure Effect4.Optional (S : Type u) (A : Type v) where
  preview : S -> Option A
  replace : A -> S -> S

Effect4.Optional.modify : Optional S A -> (A -> A) -> S -> S
Effect4.Optional.compose : Optional S A -> Optional A B -> Optional S B
Effect4.Optional.toTraversal : Optional S A -> Traversal S A

structure Effect4.Optional.Lawful (optic : Optional S A) : Prop where
  replace_absent : forall source value, optic.preview source = none ->
    optic.replace value source = source
  preview_replace : forall source current value,
    optic.preview source = some current ->
      optic.preview (optic.replace value source) = some value
  replace_preview : forall source current,
    optic.preview source = some current ->
      optic.replace current source = source
  replace_replace : forall source first second,
    optic.replace second (optic.replace first source) =
      optic.replace second source

structure Effect4.Traversal (S : Type u) (A : Type v) where
  collect : S -> List A
  modifyAll : (A -> A) -> S -> S

Effect4.Traversal.compose : Traversal S A -> Traversal A B -> Traversal S B

structure Effect4.Traversal.Lawful (optic : Traversal S A) : Prop where
  modify_congr : forall {first second : A -> A},
    (forall value, first value = second value) -> forall source,
      optic.modifyAll first source = optic.modifyAll second source
  modify_id : forall source, optic.modifyAll id source = source
  modify_comp : forall source first second,
    optic.modifyAll second (optic.modifyAll first source) =
      optic.modifyAll (second . first) source
  collect_modify : forall source f,
    optic.collect (optic.modifyAll f source) = optic.collect source |>.map f
```

The builder also owes reusable law constructors:

```lean
Lens.Lawful.compose
Lens.Lawful.toOptional
Optional.Lawful.compose
Optional.Lawful.toTraversal
Traversal.Lawful.compose
```

`modify_congr` is intentionally pointwise. Without it, proving composition's
identity and composition equations requires turning pointwise equality of
modifiers into equality of functions; the first implementation probe did that
with `funext` and spent `Quot.sound`. The pointwise action law is reusable and
lets every composition proof remain structural. These are the only general
optic laws in this packet. There is no equality of optic records, no dependent
focus, and no effectful traversal law.

## Typed annotation dimensions

```lean
structure Effect4.AnnotationKey (A : Type u) where
  name : String
  encode : A -> Json
  decode : Json -> Option A

structure Effect4.AnnotationKey.Lawful (key : AnnotationKey A) : Prop where
  decode_encode : forall value, key.decode (key.encode value) = some value
  encode_decode : forall raw value, key.decode raw = some value ->
    key.encode value = raw
```

Both directions are required. `decode_encode` keeps a newly written value in
the typed focus. `encode_decode` makes an identity modification reconstruct
the exact raw payload rather than a canonical substitute.

The construction and observation surface is:

```lean
AnnotationKey.entry : AnnotationKey A -> A -> AnnotationEntry
AnnotationKey.singleton : AnnotationKey A -> A -> Annotations
AnnotationKey.append : AnnotationKey A -> A -> Annotations -> Annotations
AnnotationKey.decodeEntry : AnnotationKey A -> AnnotationEntry -> Option A
AnnotationKey.values : AnnotationKey A -> Traversal Annotations A
AnnotationKey.inTraversal : AnnotationKey A -> Traversal S Annotations -> Traversal S A
AnnotationKey.getAll : AnnotationKey A -> Annotations -> List A
AnnotationKey.modifyAll : AnnotationKey A -> (A -> A) -> Annotations -> Annotations
AnnotationKey.replaceAll : AnnotationKey A -> A -> Annotations -> Annotations
```

`decodeEntry_entry` and `entry_of_decodeEntry` are the exact reconstruction
laws. `values_lawful` requires `AnnotationKey.Lawful`; `inTraversal_lawful`
requires both key and outer traversal laws. `getAll`, `modifyAll`, and
`replaceAll` are definitions through `values`, not independent algorithms.

`Annotations.payloadsAt name` is the raw
`Traversal Annotations Json`. It visits every matching entry, including
duplicates and payloads a typed key would reject, in list order. Modification
changes payloads only: it preserves the outer `none` versus `some`, list
length, every key, duplicate multiplicity, order, and every unrelated entry.
`Annotations.payloadsAt_lawful` records the three traversal laws.

## Local annotation optics

`Representation.nodeAnnotations : Optional Representation Annotations` is
absent only for `Reference`. Every other constructor has a present focus even
when its stored field is `none`; consequently:

```lean
Representation.nodeAnnotations.preview (.reference ref) = none
Representation.nodeAnnotations.preview (.string none []) = some none
```

Replacement is a no-op on `Reference` and changes only the annotation field on
the other twenty-one constructors. The public laws are
`Representation.nodeAnnotations_lawful`,
`Representation.nodeAnnotations_reference`, and
`Representation.nodeAnnotations_string_none`.

`Check.annotationsLens`, `ElementOf.annotationsLens`, and
`PropertySignatureOf.annotationsLens` are total lenses. Each has a public
`_lawful` theorem. Their replacement changes only the named annotation field;
the batteries pin representative exact equations. `IndexSignatureOf` has no
annotations and receives no optic.

## Recursive annotation-bag traversals

The four public traversals are:

```lean
Representation.annotationBags : Traversal Representation Annotations
Check.annotationBags : Traversal Check Annotations
Document.annotationBags : Traversal Document Annotations
MultiDocument.annotationBags : Traversal MultiDocument Annotations
```

All four are lawful. The two payload traversals are defined from the closed
two-sorted fold, not from a second recursive carrier. Their order is structural
preorder and follows the fold handler's argument order:

1. A non-reference representation's own bag.
2. `Declaration` visits type parameters then checks. Every other
   non-reference node visits checks before its remaining children. For arrays,
   an element bag precedes that element's type subtree, followed by rest. For
   objects, a property bag precedes that property's type subtree, followed by
   each index's parameter then result. Other lists retain source order.
3. A check's own bag, then its representation-annotation schemas, then (for a
   group) its nested checks.

`Reference` is a leaf and contributes no bag. Traversal is deliberately over
raw structure: it does not assume field admission and it does not resolve a
reference key.

For `Document`, the root representation is traversed first, followed by the
representation of **every** reference entry in list order. For
`MultiDocument`, every root is traversed in list order and then every reference
entry in list order. Reachability, duplicate keys, and dead entries do not
filter this data-plane traversal.

`AnnotationKey.inTraversal` is the higher-order bridge: a caller composes one
typed dimension with any of these bag traversals and derives ordered lookup or
modification over a whole representation or document without a new per-key
algorithm.

## Counterexample allocation

- `E4-SCHEMA-CE-044`: no focus on `Reference` is not the same as a present
  annotation field whose value is `none`.
- `E4-SCHEMA-CE-045`: first-match or map lookup loses duplicate-key order and
  multiplicity; raw traversal visits all matches.
- `E4-SCHEMA-CE-046`: a one-sided typed codec can decode a noncanonical raw
  payload and re-encode a different payload; exact reconstruction requires
  both inverse laws.
- `E4-SCHEMA-CE-047`: a shallow node walk misses check annotation schemas,
  nested groups, element/property bags, and their nested types.
- `E4-SCHEMA-CE-048`: a reference-resolving document walk misses dead and
  duplicate reference entries; the data-plane visits every entry structurally.

## Proof burden

`DATA-PG-OPTIC` owns generic composition and conversion lawfulness. This graph
is warranted because each theorem transports three or four laws through a
higher-order combinator; the carrier projections and individual `modify`
definitions are trivial receipts and get no graph of their own.

`SCHEMA-PG-ANNOTATION-DATA` owns the two-sided key reconstruction laws, raw and
typed ordered traversals, and recursive bag traversal. It reuses the already
closed `SCHEMA-PG-PAYLOAD/SC-REP-03-RECURSOR` edge. The three local lenses and
the two ground `nodeAnnotations` equations attach as receipts; they do not get
separate proof graphs.

Acceptance requires both batteries and all five retained attacks to elaborate,
`#print axioms` to show no `Classical.choice`, `propext`, `Quot.sound`, or
`Lean.ofReduceBool` in the new law theorems, and the default project gate to
pass without editing the breaker-owned files.

## Breaker receipt

The green workshop probe establishes only satisfiability of the three optic
records, the local annotation optics, and the raw duplicate traversal. It is
candidate evidence, not authority. The frozen packet strengthens its
one-sided typed codec to exact two-sided reconstruction and adds the recursive
document-wide traversal obligations.

The breaker ran, from the project root:

```text
lake env lean -DmaxErrors=10000 --json Effect4Test/Data/OpticContract.lean
lake env lean -DmaxErrors=10000 --json Effect4Test/Schema/AnnotationDataPlaneContract.lean
lake env lean -DmaxErrors=10000 --json Effect4Test/Counterexamples/Schema/AnnotationDataPlane.lean
```

All three exited 1 against the production state at freeze time. The first optic battery emitted 69
errors rooted in the 24 missing `Lens`/`Optional`/`Traversal` carrier,
operation, law-record, and law-constructor names. The Schema battery emitted
118 errors rooted in the absent generic optics plus every frozen
`AnnotationKey`, `payloadsAt`, local optic, and recursive traversal name. The
counterexample battery emitted 24 errors rooted in the absent
`nodeAnnotations`, `payloadsAt`, `AnnotationKey`, and recursive traversal
surface. Later elaboration and `#guard` errors are dependency fallout.

During handoff the generic optic implementation landed concurrently. The
original optic battery then went green, but its axiom receipt exposed
`[propext]` on three law constructors and `[propext, Quot.sound]` on
`Traversal.Lawful.compose`. That fired the breaker: pointwise `modify_congr`
was added to the frozen traversal laws, and the implementation must remove
those dependencies rather than normalize them into the library trust ceiling.
The revised optic battery is red with exactly two errors, both the missing
`Traversal.Lawful.modify_congr` field/declaration.

Frozen battery hashes:

```text
b65b86534af75ec8067bda3cb3a96bd58bf8dc541a3b28dd55ddd6b7608a8bc5  Effect4Test/Data/OpticContract.lean
1b2aa06d0940a6e48d2c4cdbacc6a9cb67745113d78ce07ee03bcae0090fcb67  Effect4Test/Schema/AnnotationDataPlaneContract.lean
969e2e613043a6990d47e2530bd36d5165a95eb987effaca4be748d60dad6058  Effect4Test/Counterexamples/Schema/AnnotationDataPlane.lean
```
