// Does tsgo 7 accept a union inside a pair, record or Exit where the target is the union of
// the distributed members? Each line is one case; the error list names the refused ones.
import { Exit } from "effect"

// 1. tuple with a literal-union head (the tagged error spelling `pair(tag, message)`)
declare const t1: readonly ["A" | "B", string]
export const c1: readonly ["A", string] | readonly ["B", string] = t1

// 2. record with a literal-union `_tag` (a discriminant)
declare const r1: { readonly _tag: "A" | "B"; readonly x: number }
export const c2: { readonly _tag: "A"; readonly x: number } | { readonly _tag: "B"; readonly x: number } = r1

// 3. tuple whose union is in a non-discriminant position
declare const t3: readonly [number | string, boolean]
export const c3: readonly [number, boolean] | readonly [string, boolean] = t3

// 4. record whose union is in a non-literal field
declare const r4: { readonly a: number | string; readonly b: boolean }
export const c4: { readonly a: number; readonly b: boolean } | { readonly a: string; readonly b: boolean } = r4

// 5. Exit with a union in the success value
declare const e5: Exit.Exit<number | string, never>
export const c5: Exit.Exit<number, never> | Exit.Exit<string, never> = e5

// 6. a list does not distribute: mixed arrays are not in the union (control: must be refused)
declare const l6: ReadonlyArray<number | string>
export const c6: ReadonlyArray<number> | ReadonlyArray<string> = l6
