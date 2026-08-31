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
 *   - literalPin — 5461f66ed3a0eeade4cd058d438d24c86c32b28ce1756b4af8297434103f0c04
 */
import { Schema } from "effect"

export const literalPin = Schema.Struct({ "a": Schema.Null, "b": Schema.Literal(true), "c": Schema.optionalKey(Schema.Literal(-7)), "d": Schema.Literal("pinned") })

export type literalPin = { readonly "a": null, readonly "b": true, readonly "c"?: -7, readonly "d": "pinned" }
