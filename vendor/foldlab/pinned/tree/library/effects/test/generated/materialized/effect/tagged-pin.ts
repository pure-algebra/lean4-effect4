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
 *   - taggedPin — 90208f8ffb27351f48346c096e93869c633ec58840c91456b7b533f70c65c8d9
 */
import { Schema } from "effect"

export const taggedPin = Schema.Union([Schema.Struct({ "_tag": Schema.Literal("move"), "dx": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), "dy": Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })) }), Schema.Struct({ "_tag": Schema.Literal("say"), "body": Schema.String, "note": Schema.optionalKey(Schema.String) }), Schema.Struct({ "_tag": Schema.Literal("stop") })], { mode: "oneOf" })

export type taggedPin = { readonly "_tag": "move", readonly "dx": number, readonly "dy": number } | { readonly "_tag": "say", readonly "body": string, readonly "note"?: string } | { readonly "_tag": "stop" }
