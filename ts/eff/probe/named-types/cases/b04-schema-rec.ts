// expect: none
// The Schema code face of a recursive declared name: one name for the alias and the Schema,
// as rc.112's code generator writes it (`toCodeDocument.ts:388`).
import { Schema } from "effect"
export type Tree = { readonly value: number; readonly children: ReadonlyArray<Tree> }
export const Tree = Schema.Struct({
  value: Schema.Number,
  children: Schema.Array(Schema.suspend((): Schema.Codec<Tree> => Tree))
})
export const decoded: Tree = Schema.decodeUnknownSync(Tree)({ value: 1, children: [{ value: 2, children: [] }] })
