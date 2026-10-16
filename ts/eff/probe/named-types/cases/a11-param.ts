// expect: none
// A parameterized declaration (decisions row 401 (4)): regular recursion keeps the parameters.
import { Option } from "effect"
export type List<A> = { readonly head: A; readonly tail: Option.Option<List<A>> }
export const list: List<string> = { head: "a", tail: Option.some({ head: "b", tail: Option.none() }) }
