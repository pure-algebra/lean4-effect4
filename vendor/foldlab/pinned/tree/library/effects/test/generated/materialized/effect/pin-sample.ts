/**
 * GENERATED — do not edit. Materialized from canonical schema nodes
 * by `Cas.Materialize.source`: every binding below is what Effect's
 * own `SchemaRepresentation.toCodeDocument` prints for the schema
 * revived out of the addressed node. The addresses are the stamp
 * that makes this file a projection of store content and parity a
 * digest check (R7, the served-equals-derived wall) — regenerate,
 * never edit.
 *
 * Materialized from schema nodes (kind tag 0x53):
 *   - pinSample — 0ee1758ef14781a52a56e9e2d7951555d5af19a9eb7cb9238808ed39d782219e
 */
import { Schema } from "effect"
import { Cas } from "@foldlab/cas"

export const pinSample = Schema.Struct({ "count": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), "flag": Schema.Boolean, "items": Schema.Array(Schema.String), "label": Schema.String, "note": Schema.optionalKey(Schema.String), "root": Cas.CanonicalSchema.ref(9), "unit": Schema.Null })

export type pinSample = { readonly "count": number, readonly "flag": boolean, readonly "items": ReadonlyArray<string>, readonly "label": string, readonly "note"?: string, readonly "root": Cas.ReferenceSentinel, readonly "unit": null }
