import type { Option } from "effect"
type __Left = { readonly a: number; readonly b: string }
type __Right = unknown
declare const __left: __Left
declare const __right: __Right
export const __pair_leftToRight: __Right = __left
export const __pair_rightToLeft: __Left = __right
export type __Use = Option.Option<never>
