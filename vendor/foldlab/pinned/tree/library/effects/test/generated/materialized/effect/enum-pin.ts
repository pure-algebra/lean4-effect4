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
 *   - enumPin — 845c3cfccb9fe60e6bdc4976e3e7e111ec57f2f88ee3bbfb47a7ae447490f15e
 */
import { Schema } from "effect"

const _Enum = { "Up": "Up", "Down": "Down" } as const
type _Enum = (typeof _Enum)[keyof typeof _Enum]

const _Enum1 = { "Debug": -1, "Warn": 1, "Warning": 1 } as const
type _Enum1 = (typeof _Enum1)[keyof typeof _Enum1]

const _Enum2 = { "Name": "name", "Zero": 0 } as const
type _Enum2 = (typeof _Enum2)[keyof typeof _Enum2]

export const enumPin = Schema.Struct({ "direction": Schema.Enum(_Enum), "level": Schema.Enum(_Enum1), "mixed": Schema.optionalKey(Schema.Enum(_Enum2)) })

export type enumPin = { readonly "direction": _Enum, readonly "level": _Enum1, readonly "mixed"?: _Enum2 }
