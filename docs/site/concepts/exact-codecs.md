# Exact codecs and data plane embeddings

This page explains exact codecs and data plane embeddings in Effect4. It covers how values and types serialize to JSON and Schema representations with bidirectional round-trip laws.

## The runtime concept {#runtime-concept}

Effect uses Effect Schema to validate, encode, and decode data crossing external boundaries. In Effect rc.112, schemas define transformations between runtime objects and JSON values.

Effect4 formalizes this boundary using bidirectional data plane embeddings in `Codec` (`src/Effect4/Schema/Codec.lean`) and `Bridge` (`src/Effect4/Schema/Bridge.lean`).

These embeddings translate values to JSON and types to Schema AST representations.

## Literature foundations {#literature}

The metatheory adapts invertible target syntax descriptions from Rendel and Ostermann (2010). Invertible syntax descriptions unify printers and parsers under partial isomorphisms.

Bidirectional transformations adapt the tree lenses of Foster et al. (2007). Lenses formalize GetPut and PutGet laws between abstract and concrete structures.

Exact embeddings adapt the lawful prisms and profunctor optics of Pickering, Gibbons, and Wu (2017).

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 defines an exact embedding as a write/read pair satisfying three laws:
- Totality on its domain.
- Retraction: reading a written image recovers the original element.
- Exactness: anything that reads successfully is an image modulo a named normaliser.

Under decisions row 128, Effect4 models two exact embeddings:
- The JSON codec: encodes `Val` into `Json` exact modulo key sorting via `normJ`.
- The Schema bridge: converts `Ty` into `Representation` exact modulo annotation erasure via `normS`.

Under decisions row 179, `normS` erases only nine approved annotation keys listed in `erasedKeys`. Arbitrary custom metadata is not erased.

Effect4 cuts ambiguous left-biased decoding (`E4-SCHEMA-CE-059`). Overlapping union shapes could defeat unchecked recovery.

The public encoder refuses ambiguous values so that every successful encoding decodes back reliably (`decode_of_encode`).

## How to read the claims {#reading-claims}

The claims under this concept state that serialization transformations maintain data fidelity without silent information loss.

Key properties to inspect:
- [`decode-iff`](#claim:decode-iff): JSON decoding is exact modulo key ordering `normJ`.
- [`decode-encode`](#claim:decode-encode): Decoding an encoded value recovers the original on codec-admitted values at canonical types.
- [`of-schema-exact`](#claim:of-schema-exact): Schema representation decoding is exact modulo the nine approved keys `normS`.

The table of claims on this page gives each claim's status and its statement.
