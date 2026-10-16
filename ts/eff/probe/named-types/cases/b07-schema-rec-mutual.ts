// expect: none
// Mutual recursion in Schema code: rc.112's generator suspends every reference inside a
// recursive definition (`toCodeDocument.ts:384-388`).
import { Schema } from "effect"
export type Even = { readonly _tag: "Zero" } | { readonly _tag: "SuccE"; readonly pred: Odd }
export type Odd = { readonly _tag: "SuccO"; readonly pred: Even }
export const Even = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Zero") }),
  Schema.Struct({ _tag: Schema.Literal("SuccE"), pred: Schema.suspend((): Schema.Codec<Odd> => Odd) })
])
export const Odd = Schema.Struct({ _tag: Schema.Literal("SuccO"), pred: Schema.suspend((): Schema.Codec<Even> => Even) })
