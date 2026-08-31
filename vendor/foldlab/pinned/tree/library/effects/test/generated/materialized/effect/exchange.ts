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
 *   - exchange — 80f7a642c632bf435bd1a30de1466624abd1c3b69cfc1d96ef75d2bff752daf4
 */
import { Schema } from "effect"
import { Cas } from "@foldlab/cas"

export const exchange = Schema.Struct({ "answer": Schema.String, "prompt": Schema.String, "subject": Schema.Union([Schema.Struct({ "_tag": Schema.Literal("exchange"), "address": Cas.CanonicalSchema.ref(88) }), Schema.Struct({ "_tag": Schema.Literal("schema"), "address": Cas.CanonicalSchema.ref(83) })], { mode: "oneOf" }) })

export type exchange = { readonly "answer": string, readonly "prompt": string, readonly "subject": { readonly "_tag": "exchange", readonly "address": Cas.ReferenceSentinel } | { readonly "_tag": "schema", readonly "address": Cas.ReferenceSentinel } }
