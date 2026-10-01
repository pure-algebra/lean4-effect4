import type { Option } from "effect"
type __Left = Option.Option<{ readonly a: number; readonly b: string }>
type __Right = Option.Option<{ readonly b: string; readonly a: number }>
declare const __left: __Left
declare const __right: __Right
export const __pair_leftToRight: __Right = __left
export const __pair_rightToLeft: __Left = __right
export type __Use = Option.Option<never>
