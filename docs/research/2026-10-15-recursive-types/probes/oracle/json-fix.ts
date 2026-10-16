// The map spelling that recursion needs: an index signature, which tsgo defers, in place of
// `Readonly<Record<string, V>>`, which it expands at once (faces.ts: TS2456).
type Num = number
export type Json = string | boolean | ReadonlyArray<Json> | { readonly [key: string]: Json } | null | Num
export const json: Json = [null, true, 3, "x", [{}, { k: "v" }]]
// @ts-expect-error undefined is no JSON value
export const jsonBad: Json = [undefined]
// the two spellings are one type where no recursion is involved: each assigns to the other
type A = Readonly<Record<string, number>>
type B = { readonly [key: string]: number }
export const ab: (a: A) => B = a => a
export const ba: (b: B) => A = b => b
