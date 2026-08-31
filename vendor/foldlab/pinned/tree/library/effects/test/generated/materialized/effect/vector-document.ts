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
 *   - vectorDocument — cf674c2dfdbd3582661e2f96a026969d31956880a8912f7c1ddd1bb613ad968c
 */
import { Schema } from "effect"

export const vectorDocument = Schema.Struct({ "description": Schema.String, "digest": Schema.Literal("sha256-scheme0"), "name": Schema.String, "schemaVersion": Schema.Literal(1), "word": Schema.Array(Schema.Struct({ "address": Schema.String, "node": Schema.Struct({ "payload": Schema.String, "refs": Schema.Array(Schema.Struct({ "expectedTag": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), "id": Schema.String })), "tag": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), "version": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })) }) })) })

export type vectorDocument = { readonly "description": string, readonly "digest": "sha256-scheme0", readonly "name": string, readonly "schemaVersion": 1, readonly "word": ReadonlyArray<{ readonly "address": string, readonly "node": { readonly "payload": string, readonly "refs": ReadonlyArray<{ readonly "expectedTag": number, readonly "id": string }>, readonly "tag": number, readonly "version": number } }> }
