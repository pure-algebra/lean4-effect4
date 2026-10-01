import type { Option } from "effect"
type __Left = { readonly u: { readonly a: number; readonly b: string }; readonly s: number }
type __Right = { readonly s: number; readonly u: { readonly b: string; readonly a: number } }
declare const __left: __Left
declare const __right: __Right
export const __pair_leftToRight: __Right = __left
export const __pair_rightToLeft: __Left = __right
export type __Use = Option.Option<never>
