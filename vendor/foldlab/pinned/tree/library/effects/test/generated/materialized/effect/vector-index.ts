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
 *   - vectorIndex — a5445fde1908dedd1f115104b3853c8fe4146ecac58a0105009c2fb9fafb31f1
 */
import { Schema } from "effect"

export const vectorIndex = Schema.Struct({ "digest": Schema.Literal("sha256-scheme0"), "schemaVersion": Schema.Literal(1), "vectors": Schema.Array(Schema.Struct({ "bindings": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), "description": Schema.String, "file": Schema.String, "name": Schema.String, "root": Schema.String })) })

export type vectorIndex = { readonly "digest": "sha256-scheme0", readonly "schemaVersion": 1, readonly "vectors": ReadonlyArray<{ readonly "bindings": number, readonly "description": string, readonly "file": string, readonly "name": string, readonly "root": string }> }
