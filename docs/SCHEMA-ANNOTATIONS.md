# Schema annotations as a data carrier

Schema annotations are typed dimensions carried by the existing raw Schema
tree. `AnnotationEntry`, `Annotations`, `Representation`, `Check`, `Document`,
and `MultiDocument` remain the stored data. The annotation API adds lawful
views and edits over those types; it does not introduce a second Schema tree
or convert the ordered annotation bag into a map.

## The three layers

The raw layer preserves every retained entry exactly:

```lean
structure AnnotationEntry where
  key : String
  payload : Json

abbrev Annotations := Option (List AnnotationEntry)
```

The typed layer describes one dimension of that data:

```lean
structure AnnotationKey (A : Type u) where
  name : String
  encode : A -> Json
  decode : Json -> Option A
```

`AnnotationKey.Lawful` requires both codec directions. A newly encoded value
must decode, and a successfully decoded payload must re-encode to the exact raw
payload. This makes identity edits preserve authored data rather than silently
canonicalizing it.

The compositional layer supplies `Lens`, `Optional`, and `Traversal` values.
A typed key is a traversal because one raw bag may contain several entries
with the same key. `AnnotationKey.inTraversal` lifts that one dimension through
`Representation.annotationBags`, `Check.annotationBags`,
`Document.annotationBags`, or `MultiDocument.annotationBags`.

```lean
def title : AnnotationKey String where
  name := "effect/schema/title"
  encode := Json.str
  decode
    | .str value => some value
    | _ => none

def titledDocument : Traversal Document String :=
  title.inTraversal Document.annotationBags
```

The derived traversal reads or changes every decodable title in structural
order. Same-key payloads that do not decode remain in place and unchanged.
Unrelated entries, duplicates, list order, and the distinction between `none`
and `some []` are preserved.

## Annotation planes

Effect's annotation API has separate planes, and the bridge keeps them
separate:

| Plane | Effect API | Meaning |
| --- | --- | --- |
| Decoded type | `Schema.annotate` | Metadata about values after decoding |
| Encoded type | `Schema.annotateEncoded` | Metadata about the wire-side value |
| Field position | `Schema.annotateKey` | Metadata about an element or property position |
| Resolved check | `Schema.resolveAnnotations` | The final check bag when checks exist; otherwise the node bag |

Resolution is a read policy, not storage normalization. In particular, a
final check bag that lacks a key does not fall back to the node bag for that
key. The Lean data-plane traversal inventories and edits raw stored bags; a
separate resolver can model Effect's last-check read policy.

## Higher-order authoring

The host harness defines reusable functions such as `withCodegen`,
`withAnalysis`, and `withDimensions`. Module augmentation gives each custom
key a checked TypeScript payload while the runtime continues to store ordinary
annotation data.

```ts
const withCodegen = (dimension: CodegenDimension) =>
  <S extends Schema.Top>(schema: S): S["Rebuild"] =>
    schema.annotate({ "effect4/codegen": dimension })

const UserId = Schema.String.pipe(
  withDimensions(
    { version: 1, typeName: "UserId", brand: "UserId" },
    {
      version: 1,
      sensitivity: "internal",
      determinism: "deterministic"
    }
  )
)
```

`./scripts/check-schema-annotations.sh` typechecks these combinators with the
unpatched TypeScript compiler, requests strict diagnostics from the Effect
language service, executes the fixture, and confirms that JSON-valued custom
dimensions survive `SchemaRepresentation.toRepresentation` and
`SchemaRepresentation.toJson`.

## Raw rendering and descriptions

The library does not add a universal `Describes` class. Raw Schema data already
has explicit projections: the TypeScript target renders a representation or
document, and the host bridge can render the revived raw JSON. These functions
keep description, persistence, and denotation separate. A future description
facade should be derived from the raw carrier or a typed annotation registry,
not stored as a second hand-maintained view of Schema.

Function-valued live annotations remain host-only. A later first-order
annotation registry may classify portable keys, allowed sites, and payload
schemas, but its canonical content must stay data-only; encoder and decoder
functions belong to authoring and proof descriptors.

## Effectful field interfaces

An annotation may also declare that a field is read or written through the
existing effect algebra. The next additive layer derives an effectful field
interface from three things: a pure `Lens`, a first-order annotation payload,
and operations from the existing closed `Signature`. The Schema tree stores
only portable operation identity data; the resolved interface keeps Lean
functions outside persisted content.

This does not make the pure optic itself monadic and does not add another
Schema or program carrier. `get`, `set`, and `modify` are generated programs,
so their observable operations remain available to interpreters, analyzers,
and TypeScript generation. Duplicate or malformed same-name annotations must
fail interface derivation rather than being hidden by first-match lookup.
