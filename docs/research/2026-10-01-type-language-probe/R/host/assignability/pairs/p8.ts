import type { Option } from "effect"
type __Left = { readonly _tag: "A"; readonly a: number } | { readonly _tag: "B"; readonly b: string }
type __Right = { readonly b: string; readonly _tag: "B" } | { readonly a: number; readonly _tag: "A" }
declare const __left: __Left
declare const __right: __Right
export const __pair_leftToRight: __Right = __left
export const __pair_rightToLeft: __Left = __right
export type __Use = Option.Option<never>
