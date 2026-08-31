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
 *   - unionPin — 98e36f2243f0269fc3165110660f7b8f08a43aaffc450be7b87ca1f4f6005819
 */
import { Schema } from "effect"

export const unionPin = Schema.Struct({ "choice": Schema.Union([Schema.String, Schema.Boolean, Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" }))]), "exact": Schema.Literals(["zebra", "alpha"]), "nested": Schema.optionalKey(Schema.Union([Schema.Null, Schema.Union([Schema.Array(Schema.String), Schema.Boolean], { mode: "oneOf" })])) })

export type unionPin = { readonly "choice": string | boolean | number, readonly "exact": "zebra" | "alpha", readonly "nested"?: null | ReadonlyArray<string> | boolean }
