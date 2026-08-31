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
 *   - tuplePin — 5f281a876efdf63c43a61c07a1422bf4311ed68efb65806a160db7bc80c5e942
 */
import { Schema } from "effect"

export const tuplePin = Schema.Struct({ "nested": Schema.optionalKey(Schema.Tuple([Schema.Array(Schema.Tuple([Schema.String])), Schema.Null])), "pair": Schema.Tuple([Schema.String, Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" }))]), "plain": Schema.Array(Schema.String), "withOptional": Schema.Tuple([Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" })), Schema.optionalKey(Schema.String)]), "withRest": Schema.TupleWithRest(Schema.Tuple([Schema.String]), [Schema.Number.check(Schema.isInt().annotate({ "expected": "an integer" }))]) })

export type tuplePin = { readonly "nested"?: readonly [ReadonlyArray<readonly [string]>, null], readonly "pair": readonly [string, number], readonly "plain": ReadonlyArray<string>, readonly "withOptional": readonly [number, string?], readonly "withRest": readonly [string, ...Array<number>] }
